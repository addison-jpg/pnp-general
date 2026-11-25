"""Run a proposed program in a separate process.  Model output is NEVER exec'd or imported in the main process: it is written to a
file in an empty temporary directory and run by a fresh interpreter, and only its JSON result (data) comes back.
Layers, outermost first:
  1. no network: a new network namespace (`unshare -n`, or `unshare -r -n`, or `sudo -n unshare -n` and back to the calling user).
     If none of these works the sandbox REFUSES to run (override: FUNSEARCH_ALLOW_NO_NETNS=1, then only layers 2 to 4 apply).
  2. as root: the child drops to uid/gid 65534 (setpriv) before the interpreter starts.
  3. limits: wall-clock timeout (the whole process group is killed), RLIMIT_CPU, address space, file size, open files; empty
     environment; stdin closed; `python3 -I -S -B` (no site-packages, no user site, no PYTHON* variables), cwd = the temp dir.
  4. inside the interpreter an audit hook stops sockets, process creation, ctypes and opening files for writing.
Layer 4 alone is not a security boundary (Python audit hooks can be defeated by hostile code); layers 1 to 3 are the boundary.
The harness is: PREAMBLE (the target's helper code) + the program + a driver that calls ENTRY once per instance."""
import os, sys, json, shutil, signal, tempfile, subprocess, resource

GUARD = r'''
import sys as _s
def _hook(ev, args):
    if ev.startswith(('socket.', 'subprocess.', 'ctypes.', 'os.exec', 'os.fork', 'os.posix_spawn', 'os.system', 'os.spawn', 'shutil.', 'os.remove', 'os.rename', 'os.mkdir', 'os.chmod', 'os.chown', 'os.kill', 'webbrowser.', 'urllib.', 'http.', 'ftplib.', 'smtplib.')):
        raise RuntimeError('blocked: ' + ev)
    if ev == 'open' and _OPEN[0]:
        m = args[1]; f = args[2] if len(args) > 2 else 0
        if (isinstance(m, str) and any(c in m for c in 'wax+')) or (isinstance(f, int) and f & 3): raise RuntimeError('blocked: open for writing')
_OPEN = [False]
_s.addaudithook(_hook)
import json as _json, math, itertools, functools, random, collections
_OUT = open(1, 'w', closefd=False)
_OPEN[0] = True
'''

DRIVER = r'''
_res = []
for _a in _json.loads(%r):
    try: _res.append({'ok': True, 'value': _CALL(%s, _a)})
    except BaseException as _e: _res.append({'ok': False, 'error': type(_e).__name__ + ': ' + str(_e)[:200]})
_OUT.write('\x1eRESULT' + _json.dumps(_res)); _OUT.flush()
'''

_WRAP = [None]
def netns_wrapper():
    """argv prefix that gives the child no network, or None."""
    if _WRAP[0] is None:
        uid, gid = os.getuid(), os.getgid(); opts = []
        drop = ['setpriv', '--reuid=65534', '--regid=65534', '--clear-groups', '--'] if uid == 0 and shutil.which('setpriv') else []
        if shutil.which('unshare'):
            opts.append(['unshare', '-n', '--'] + drop)
            opts.append(['unshare', '-r', '-n', '--'])
            if shutil.which('sudo') and shutil.which('setpriv'):
                opts.append(['sudo', '-n', 'unshare', '-n', '--', 'setpriv', '--reuid=%d' % uid, '--regid=%d' % gid, '--clear-groups', '--'])
        _WRAP[0] = False
        for w in opts:
            try:
                if subprocess.run(w + ['true'], capture_output=True, timeout=20).returncode == 0: _WRAP[0] = w; break
            except Exception: pass
        if _WRAP[0] is False and os.environ.get('FUNSEARCH_ALLOW_NO_NETNS') == '1': _WRAP[0] = []
    return None if _WRAP[0] is False else _WRAP[0]

def _limits(cpu, mem):
    def f():
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu + 1))
        resource.setrlimit(resource.RLIMIT_AS, (mem, mem))
        resource.setrlimit(resource.RLIMIT_FSIZE, (8 << 20, 8 << 20))
        resource.setrlimit(resource.RLIMIT_NOFILE, (32, 32))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    return f

def run_program(source, preamble, entry, instances, timeout=10, mem=1 << 30):
    """-> list (one per instance) of {'ok': True, 'value': JSON} or {'ok': False, 'error': str}."""
    wrap = netns_wrapper()
    if wrap is None: raise RuntimeError('sandbox: no network namespace available (see sandbox.py); refusing to run model output')
    py = shutil.which('python3', path='/usr/bin:/usr/local/bin:/bin') or sys.executable
    d = tempfile.mkdtemp(prefix='fs-sbx-')
    try:
        os.chmod(d, 0o755); path = os.path.join(d, 'prog.py')
        with open(path, 'w') as f: f.write(GUARD + '\n' + preamble + '\n' + source + '\n' + DRIVER % (json.dumps(instances), entry))
        os.chmod(path, 0o644); outp = os.path.join(d, 'out'); errp = os.path.join(d, 'err')
        with open(outp, 'wb') as fo, open(errp, 'wb') as fe:
            p = subprocess.Popen(wrap + [py, '-I', '-S', '-B', path], stdin=subprocess.DEVNULL, stdout=fo, stderr=fe, cwd=d,
                                 env={'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8'}, start_new_session=True, preexec_fn=_limits(int(timeout) + 1, mem))
            try: rc = p.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                try: os.killpg(p.pid, signal.SIGKILL)
                except Exception: pass
                if wrap[:1] == ['sudo']: subprocess.run(['sudo', '-n', 'pkill', '-KILL', '-s', str(p.pid)], capture_output=True)
                p.wait(); return [{'ok': False, 'error': 'timeout'}] * len(instances)
        out = open(outp, 'rb').read(8 << 20).decode('utf-8', 'replace'); k = out.rfind('\x1eRESULT')
        if k < 0:
            err = open(errp, 'rb').read(4000).decode('utf-8', 'replace').strip().splitlines()
            return [{'ok': False, 'error': 'exit %s: %s' % (rc, err[-1][:200] if err else '')}] * len(instances)
        try: return json.loads(out[k + 7:])
        except ValueError: return [{'ok': False, 'error': 'unreadable result'}] * len(instances)
    finally: shutil.rmtree(d, ignore_errors=True)

def selftest():
    pre = 'def _CALL(f, a): return f(*a)'
    r = run_program('def build(x):\n    return x + 1', pre, 'build', [[1], [2]]); assert [x['value'] for x in r] == [2, 3], r
    bad = {'net': 'import socket\ndef build(x):\n    s = socket.socket(); s.settimeout(3); s.connect(("1.1.1.1", 53)); return 1',
           'net2': 'import _socket\ndef build(x):\n    s = _socket.socket(); s.settimeout(3); s.connect(("1.1.1.1", 53)); return 1',
           'proc': 'import os\ndef build(x):\n    return os.system("id")',
           'write': 'def build(x):\n    open("/tmp/fs_sbx_escape", "w").write("x"); return 1',
           'loop': 'def build(x):\n    while True: pass',
           'mem': 'def build(x):\n    return len(bytearray(1 << 33))',
           'exit': 'import sys\ndef build(x):\n    sys.exit(0)'}
    for k, src in bad.items():
        r = run_program(src, pre, 'build', [[1]], timeout=4); assert not r[0]['ok'], (k, r)
        print('  blocked %-5s %s' % (k, r[0]['error'][:70]))
    assert not os.path.exists('/tmp/fs_sbx_escape')
    print('sandbox selftest ok; wrapper:', ' '.join(netns_wrapper()) or '(none: FUNSEARCH_ALLOW_NO_NETNS)')

if __name__ == '__main__': selftest()
