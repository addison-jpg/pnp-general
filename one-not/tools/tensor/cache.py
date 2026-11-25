"""Content-addressed cache for the tensor backend ("Structure between jobs", README).
An entry is one array (truth tables, a slack table, ...) of one circuit, addressed by  KIND:sha256(json [n, sets, gates, outs])[:32].
The key covers the circuit only, so KIND must name everything else the array depends on (e.g. 'slack_any' = slack_cubes(any_gate=True)).
Storage: the directory $COMPUTE_CACHE (unset: the cache is off and get() just computes).
  $COMPUTE_CACHE/packs/*.pack   read at first use: zlib( json header line  [[key, dtype, shape, offset], ...] + raw little-endian bytes )
  $COMPUTE_CACHE/new/SHA.pack   written at exit: this process's misses, one pack named by the sha256 of its bytes
In Actions, packs/ is the `compute-cache` branch plus the packs of earlier jobs of the same run, and new/ is uploaded as an artifact
that the one writer job commits to the branch (compute.yml).  Locally: point COMPUTE_CACHE at any directory, then `cache.py absorb`.
At exit one line is printed:  CACHE {"hit": h, "miss": m, "new_bytes": b}   (dag.py adds these up over shards).
  python3 -I cache.py absorb [DIR]   move DIR/new/*.pack into DIR/packs/ (what the writer job does on the branch)
  python3 -I cache.py stat [DIR]     entries and bytes per kind"""
import os, sys, json, zlib, glob, atexit, hashlib
import numpy as np

DIR = os.environ.get('COMPUTE_CACHE') or None
_IDX = None          # key -> (pack bytes, dtype, shape, offset), filled lazily
_NEW = {}            # key -> array
STAT = {'hit': 0, 'miss': 0, 'new_bytes': 0}

def chash(c):
    """The address of a circuit: inputs, sets, gates, outputs (names and other fields do not count)."""
    return hashlib.sha256(json.dumps([c['n'], c.get('sets'), c['gates'], c['outs']], separators=(',', ':')).encode()).hexdigest()[:32]

def read_pack(path):
    raw = zlib.decompress(open(path, 'rb').read()); cut = raw.index(b'\n')
    return json.loads(raw[:cut]), memoryview(raw)[cut + 1:]

def _index():
    global _IDX
    if _IDX is None:
        _IDX = {}
        for p in sorted(glob.glob(os.path.join(DIR, 'packs', '*.pack'))) if DIR else []:
            try: head, body = read_pack(p)
            except Exception as e: print('cache: skipping unreadable pack', p, e, file=sys.stderr); continue
            for key, dt, shape, off in head: _IDX[key] = (body, dt, shape, off)
    return _IDX

def get(kind, c, compute):
    """The cached array of KIND for circuit c, or compute() (stored for the next job).  Read-only arrays."""
    if not DIR: return compute()
    key = kind + ':' + chash(c); idx = _index()
    if key in idx:
        body, dt, shape, off = idx[key]; STAT['hit'] += 1
        return np.frombuffer(body, dtype=dt, count=int(np.prod(shape, dtype=np.int64)), offset=off).reshape(shape)
    if key in _NEW: STAT['hit'] += 1; return _NEW[key]
    a = np.ascontiguousarray(compute()); a = a.astype(a.dtype.newbyteorder('<'), copy=False)
    _NEW[key] = a; STAT['miss'] += 1
    return a

def flush():
    """Write this process's misses as one pack; print the CACHE line."""
    if DIR and _NEW:
        head, parts, off = [], [], 0
        for key in sorted(_NEW):
            a = _NEW[key]; b = a.tobytes(); head.append([key, a.dtype.str, list(a.shape), off]); parts.append(b); off += len(b)
        blob = zlib.compress(json.dumps(head, separators=(',', ':')).encode() + b'\n' + b''.join(parts), 6)
        os.makedirs(os.path.join(DIR, 'new'), exist_ok=True)
        path = os.path.join(DIR, 'new', hashlib.sha256(blob).hexdigest()[:24] + '.pack')
        with open(path + '.tmp', 'wb') as f: f.write(blob)
        os.replace(path + '.tmp', path); STAT['new_bytes'] += len(blob); _NEW.clear()
    if DIR: print('CACHE ' + json.dumps(STAT), flush=True)
atexit.register(flush)

def absorb(d):
    os.makedirs(os.path.join(d, 'packs'), exist_ok=True); n = 0
    for p in glob.glob(os.path.join(d, 'new', '*.pack')): os.replace(p, os.path.join(d, 'packs', os.path.basename(p))); n += 1
    return n

if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'stat'; d = sys.argv[2] if len(sys.argv) > 2 else DIR
    DIR = None                                           # no CACHE line from the tool itself
    if not d: sys.exit('no cache directory (argument or $COMPUTE_CACHE)')
    if cmd == 'absorb': print('absorbed', absorb(d), 'packs')
    else:
        kinds = {}; nb = 0
        for p in glob.glob(os.path.join(d, 'packs', '*.pack')):
            nb += os.path.getsize(p)
            for key, dt, shape, off in read_pack(p)[0]: kinds[key.split(':')[0]] = kinds.get(key.split(':')[0], 0) + 1
        print(json.dumps({'packs_bytes': nb, 'entries': kinds}))
