"""Structure between compute jobs (README, "Structure between jobs"): the job DAG, the reduce step and the road back to the board tree.
A spec (compute/specs/*.json) is {"name", "entry", "args", "shards", "output", "requirements"} plus, all optional,
  "needs":   ["other-spec-name", ...]   specs in the same directory; their merged outputs reach the entry as  --input NAME=PATH
  "finding": {"dir", "serves", "statement", "evidence": [...], "runner"}   the board record of this job; "statement" is a format string
             over the result ({lines}, {sha256}, {shards}, {hit}, {miss}) and the top-level keys of the merged summary
A shard's SUMMARY is the last stdout line `SUMMARY {json}` of the entry; merging folds them (numbers add, min*/max* keys take min/max,
dicts fold by key, lists concatenate up to 200 items).  cache.py's `CACHE {json}` lines are added up the same way.

  dag.py plan SPEC                         topological levels (at most 4); in Actions also written to $GITHUB_OUTPUT
  dag.py run SPEC --shard I --of N         one shard: pip requirements, entry with the cache and the inputs, shards/I.part + I.summary.json
  dag.py merge SPEC --parts DIR [--prefix P] [--run ID]   merged/OUTPUT + merged/NAME.result.json; prints sha256 and `RESULT {json}`
  dag.py publish ARTIFACTS BRANCHDIR       lay packs and results out for the compute-cache branch (the writer job commits them)
  dag.py local SPEC [--work DIR] [--shards K]   the whole DAG on this machine, same steps, cache in DIR (default .pnp/compute)
  dag.py reduce [--who SEAT] [--dir DIR | --ref origin/compute-cache] [--name SPEC] [--dry]
        every published result whose spec has a "finding" becomes a `tested` record (boards.py add --runner) in that directory, by
        `gha-run-ID`; with --who the runner is rerun here (boards.py retest) and, if it passes, SEAT confirms it.  Confirmed violations
        (summary key "confirmed") are written as witness files and added the same way.  Nothing is committed: `git add` the lines yourself.
Run from the repository root.  Standard library only (the entries import numpy)."""
import os, sys, re, json, gzip, glob, shutil, hashlib, argparse, subprocess

MAXLEVELS = 4

def load_spec(path):
    spec = os.path.normpath(path)
    assert not spec.startswith(('..', '/')) and spec.endswith('.json') and os.path.isfile(spec), 'bad spec path ' + spec
    j = json.load(open(spec))
    n = j['shards']; assert isinstance(n, int) and 1 <= n <= 20, 'shards must be 1..20'
    e = os.path.normpath(j['entry']); assert e.endswith('.py') and not e.startswith(('..', '/')) and os.path.isfile(e), 'bad entry ' + e
    assert all(isinstance(x, str) for x in j.get('args', [])), 'args must be strings'
    assert re.fullmatch(r'[A-Za-z0-9._-]+', j['output']), 'output must be a plain file name'
    j['name'] = j.get('name') or os.path.basename(spec)[:-5]
    assert re.fullmatch(r'[A-Za-z0-9._-]+', j['name']), 'name must be a plain word'
    assert all(isinstance(x, str) and re.fullmatch(r'[A-Za-z0-9._-]+', x) for x in j.get('needs', [])), 'needs must be spec names'
    j['spec'] = spec
    return j

def plan(path):
    """Levels of the DAG rooted at SPEC: level 0 has no needs, every spec sits one level above its deepest need."""
    root = load_spec(path); d = os.path.dirname(root['spec']); specs = {}; level = {}
    def visit(p, stack):
        j = load_spec(p); assert p not in stack, 'cycle through ' + p
        if p in level: return level[p]
        deps = [os.path.join(d, x + '.json') for x in j.get('needs', [])]
        lv = 1 + max([visit(q, stack + [p]) for q in deps], default=-1)
        j['needs'] = [load_spec(q)['name'] for q in deps]; specs[p] = j; level[p] = lv
        return lv
    visit(root['spec'], [])
    assert max(level.values()) < MAXLEVELS, 'DAG deeper than %d levels' % MAXLEVELS
    names = [j['name'] for j in specs.values()]; assert len(set(names)) == len(names), 'duplicate spec names'
    single = len(specs) == 1                                            # one spec: the old artifact names (shard-i, merged)
    out = [[] for _ in range(MAXLEVELS)]
    for p, j in sorted(specs.items()):
        out[level[p]].append({'spec': p, 'name': j['name'], 'shards': j['shards'], 'prefix': '' if single else j['name'] + '-',
                              'matrix': json.dumps({'shard': list(range(j['shards']))}), 'needs': ' '.join(j['needs'])})
    return out

def fold(a, b, key=''):
    if a is None: return b
    if b is None: return a
    if isinstance(a, bool) or isinstance(b, bool): return a or b
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        return min(a, b) if key.startswith('min') else max(a, b) if key.startswith('max') else a + b
    if isinstance(a, dict) and isinstance(b, dict): return {k: fold(a.get(k), b.get(k), k) for k in list(a) + [k for k in b if k not in a]}
    if isinstance(a, list) and isinstance(b, list): return (a + b)[:200]
    return a

def tagged(text, tag):
    out = None
    for line in text.splitlines():
        if line.startswith(tag + ' '):
            try: out = fold(out, json.loads(line[len(tag) + 1:])) if tag == 'CACHE' else json.loads(line[len(tag) + 1:])
            except ValueError: pass
    return out

def run(spec, shard, of, inputs='inputs', work='shards', cache=None, pip=True, nice=False):
    j = load_spec(spec)
    if pip: subprocess.check_call([sys.executable, '-m', 'pip', 'install', '-q'] + j.get('requirements', ['numpy>=2.0']))
    os.makedirs(work, exist_ok=True)
    cmd = [sys.executable, '-I', j['entry']] + j.get('args', [])
    for dep in j.get('needs', []):
        hits = sorted(glob.glob(os.path.join(inputs, dep + '-merged', '*')))
        hits = [h for h in hits if not h.endswith('.result.json')]
        assert len(hits) == 1, 'need %s: expected one merged file under %s, found %s' % (dep, inputs, hits)
        cmd += ['--input', dep + '=' + hits[0]]
    cmd += ['--shard', str(shard), '--of', str(of), '--out', os.path.join(work, '%d.part' % shard)]
    env = dict(os.environ)
    if cache or env.get('COMPUTE_CACHE'): env['COMPUTE_CACHE'] = os.path.abspath(cache or env['COMPUTE_CACHE'])
    print(cmd, 'COMPUTE_CACHE=' + env.get('COMPUTE_CACHE', ''), flush=True)
    p = subprocess.Popen((['nice', '-n', '19'] if nice else []) + cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)
    lines = []
    for line in p.stdout:
        lines.append(line)
        sys.stdout.write(line if len(line) < 4000 else line[:4000] + ' ...\n'); sys.stdout.flush()
    rc = p.wait(); text = ''.join(lines)
    json.dump({'shard': shard, 'rc': rc, 'summary': tagged(text, 'SUMMARY'), 'cache': tagged(text, 'CACHE')}, open(os.path.join(work, '%d.summary.json' % shard), 'w'))
    return rc

def merge(spec, parts, prefix='', out='merged', run_id='local'):
    j = load_spec(spec); of = j['shards']; os.makedirs(out, exist_ok=True); path = os.path.join(out, j['output'])
    h = hashlib.sha256(); lines = size = 0; summ = cache = None
    with open(path, 'wb') as f:
        for i in range(of):
            d = os.path.join(parts, '%sshard-%d' % (prefix, i))
            with open(os.path.join(d, '%d.part' % i), 'rb') as g:
                for chunk in iter(lambda: g.read(1 << 20), b''): f.write(chunk); h.update(chunk); lines += chunk.count(b'\n'); size += len(chunk)
            sp = os.path.join(d, '%d.summary.json' % i)
            if os.path.isfile(sp):
                s = json.load(open(sp)); cache = fold(cache, s.get('cache'))
                ss = s.get('summary')
                if isinstance(ss, dict): ss = {k: v for k, v in ss.items() if k not in ('shard', 'of')}
                summ = fold(summ, ss)
    res = {'name': j['name'], 'spec': j['spec'], 'run': str(run_id), 'commit': os.environ.get('GITHUB_SHA', ''), 'output': j['output'], 'shards': of,
           'lines': lines, 'bytes': size, 'sha256': h.hexdigest(), 'needs': j.get('needs', []), 'cache': cache or {'hit': 0, 'miss': 0, 'new_bytes': 0}, 'summary': summ}
    json.dump(res, open(os.path.join(out, j['name'] + '.result.json'), 'w'))
    print('%d %s' % (lines, path)); print('%s  %s' % (res['sha256'], path))
    c = res['cache']; tot = c['hit'] + c['miss']
    print('cache: %d hits, %d misses%s' % (c['hit'], c['miss'], ', hit rate %.1f%%' % (100.0 * c['hit'] / tot) if tot else ''))
    line = 'RESULT ' + json.dumps(res, separators=(',', ':')); print(line if len(line) < 60000 else line[:60000] + ' ...(cut)')
    return res

def publish(artifacts, dest, limit=20 << 20):
    """artifacts/: cache-new-*/ *.pack and *merged/ {OUTPUT, NAME.result.json}  ->  dest/packs, dest/results/NAME/."""
    os.makedirs(os.path.join(dest, 'packs'), exist_ok=True); np_ = 0; recs = []
    for p in glob.glob(os.path.join(artifacts, '**', '*.pack'), recursive=True):
        q = os.path.join(dest, 'packs', os.path.basename(p))
        if not os.path.exists(q): shutil.copyfile(p, q); np_ += 1
    for rp in glob.glob(os.path.join(artifacts, '**', '*.result.json'), recursive=True): recs.append((rp, json.load(open(rp))))
    sha = {r['name']: r['sha256'] for _, r in recs}
    for rp, r in recs:
        d = os.path.join(dest, 'results', r['name']); os.makedirs(d, exist_ok=True)
        r['inputs'] = {x: sha.get(x) for x in r.get('needs', [])}
        src = os.path.join(os.path.dirname(rp), r['output']); data = r['sha256'][:16] + '.' + r['output'] + '.gz'
        if os.path.isfile(src) and not os.path.exists(os.path.join(d, data)):
            with open(src, 'rb') as f, open(os.path.join(d, data + '.tmp'), 'wb') as raw:
                with gzip.GzipFile(fileobj=raw, mode='wb', mtime=0) as g: shutil.copyfileobj(f, g)
            if os.path.getsize(os.path.join(d, data + '.tmp')) <= limit: os.replace(os.path.join(d, data + '.tmp'), os.path.join(d, data))
            else: os.remove(os.path.join(d, data + '.tmp')); data = None
        r['data'] = data
        json.dump(r, open(os.path.join(d, 'run-%s.json' % r['run']), 'w'), indent=1)
        print('published', r['name'], 'run', r['run'], r['sha256'][:16], 'data', data)
    print('new packs', np_)

def local(spec, work='.pnp/compute', shards=None, pip=False):
    """The DAG on this machine: the same run / merge / publish steps as compute.yml, one shard at a time under nice."""
    levels = plan(spec); run_id = 'local-' + hashlib.sha1(str(os.times()).encode()).hexdigest()[:8]
    cache = os.path.join(work, 'cache'); art = os.path.join(work, 'runs', run_id); os.makedirs(os.path.join(cache, 'packs'), exist_ok=True)
    for lv in levels:
        for job in lv:
            of = min(job['shards'], shards or job['shards']); parts = os.path.join(art, 'parts-' + job['name'])
            tmp = None
            if of != job['shards']:                                  # a smaller shard count for the local test: a copy of the spec
                tmp = os.path.join(os.path.dirname(job['spec']), '.local-%s.json' % job['name'])
                json.dump(dict(json.load(open(job['spec'])), shards=of, name=job['name']), open(tmp, 'w'))
            try:
                for i in range(of):
                    rc = run(tmp or job['spec'], i, of, inputs=art, work=os.path.join(parts, '%sshard-%d' % (job['prefix'], i)), cache=cache, pip=pip, nice=True)
                    assert rc == 0, '%s shard %d failed (%d)' % (job['name'], i, rc)
                    import_new = glob.glob(os.path.join(cache, 'new', '*.pack'))          # later shards and jobs read what this one wrote
                    for p in import_new: os.replace(p, os.path.join(cache, 'packs', os.path.basename(p)))
                res = merge(tmp or job['spec'], parts, job['prefix'], os.path.join(art, job['name'] + '-merged'), run_id)
                rp = os.path.join(art, job['name'] + '-merged', job['name'] + '.result.json'); res['spec'] = job['spec']; json.dump(res, open(rp, 'w'))
            finally:
                if tmp: os.remove(tmp)
    publish(art, cache)
    print('LOCAL run', run_id, 'results in', os.path.join(cache, 'results'))
    return run_id

def _results(dir_=None, ref='origin/compute-cache'):
    """{name: [result records]} from a directory (local runs) or from the compute-cache branch."""
    out = {}
    if dir_:
        for p in sorted(glob.glob(os.path.join(dir_, 'results', '*', 'run-*.json'))): r = json.load(open(p)); out.setdefault(r['name'], []).append(r)
        return out
    subprocess.call(['git', 'fetch', '-q', 'origin', 'compute-cache'])
    names = subprocess.run(['git', 'ls-tree', '-r', '--name-only', ref, 'results/'], capture_output=True, text=True).stdout.split('\n')
    for p in sorted(x for x in names if re.fullmatch(r'results/[^/]+/run-[^/]+\.json', x)):
        r = json.loads(subprocess.run(['git', 'show', ref + ':' + p], capture_output=True, text=True, check=True).stdout); out.setdefault(r['name'], []).append(r)
    return out

def _add(d, who, serves, statement, evidence, runner, seat, dry):
    rid = hashlib.sha1((statement + d).encode()).hexdigest()[:8]                # boards.add's id
    fj = os.path.join(d, 'findings.jsonl')
    if os.path.isfile(fj) and any('"id": "%s"' % rid in l for l in open(fj)): print('already on the board:', rid, d); return rid
    print('finding', rid, '->', fj, '|', statement)
    if dry: return rid
    subprocess.check_call([sys.executable, '-I', 'boards.py', 'add', d, who, serves, 'tested', statement] + evidence + ['--runner', runner], stdout=subprocess.DEVNULL)
    if seat:
        out = subprocess.run([sys.executable, '-I', 'boards.py', 'retest', rid], capture_output=True, text=True).stdout
        ok = any(l.startswith(rid + ' ok') for l in out.splitlines()); print('  rerun here:', 'ok' if ok else 'FAILED (left unconfirmed, stale)')
        if ok: subprocess.check_call([sys.executable, '-I', 'boards.py', 'confirm', rid, seat], stdout=subprocess.DEVNULL)
    return rid

def reduce(seat=None, dir_=None, ref='origin/compute-cache', name=None, dry=False, every=False):
    res = _results(dir_, ref); n = 0
    for nm, recs in sorted(res.items()):
        if name and nm != name: continue
        for r in (recs if every else recs[-1:]):
            if not os.path.isfile(r['spec']): continue
            fd = json.load(open(r['spec'])).get('finding')
            if not fd: continue
            s = r.get('summary') if isinstance(r.get('summary'), dict) else {}
            flat = dict(s, **{k: r[k] for k in ('lines', 'sha256', 'shards', 'run', 'bytes')}, hit=r['cache']['hit'], miss=r['cache']['miss'], sha16=r['sha256'][:16])
            who = ('gha-run-' if r['run'].isdigit() else '') + r['run']
            _add(fd['dir'], who, fd['serves'], fd['statement'].format(**flat), fd['evidence'], fd['runner'], seat, dry); n += 1
            for v in s.get('confirmed') or []:                      # a violation that passed the independent recheck job
                wdir = os.path.join(fd['dir'], 'violations'); wp = os.path.join(wdir, v['sha256'][:16] + '.json')
                if not dry: os.makedirs(wdir, exist_ok=True); json.dump(v, open(wp, 'w'), indent=1)
                st = 'Lemma D inequality FAILS (slack %s) on instance sha256 %s (%s); found by the neighbourhood job, confirmed by the independent recheck job (U1 matroid partition); a second seat must recheck before any word on PHC changes.' % (v.get('slack'), v['sha256'][:16], v.get('family'))
                _add(fd['dir'], who, fd['serves'], st, [wp], 'python3 -I one-not/tools/tensor/lemmad.py recheck --file ' + wp, seat, dry); n += 1
    print('reduced', n, 'records' + (' (dry)' if dry else ''))

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('cmd'); ap.add_argument('args', nargs='*')
    ap.add_argument('--shard', type=int); ap.add_argument('--of', type=int); ap.add_argument('--parts', default='parts'); ap.add_argument('--prefix', default='')
    ap.add_argument('--run', default='local'); ap.add_argument('--work', default='.pnp/compute'); ap.add_argument('--shards', type=int); ap.add_argument('--pip', action='store_true')
    ap.add_argument('--who'); ap.add_argument('--dir'); ap.add_argument('--ref', default='origin/compute-cache'); ap.add_argument('--name'); ap.add_argument('--dry', action='store_true'); ap.add_argument('--all', action='store_true')
    a = ap.parse_args()
    if a.cmd == 'plan':
        lv = plan(a.args[0])
        for i, l in enumerate(lv): print('level', i, [(j['name'], j['shards'], j['needs']) for j in l])
        if os.environ.get('GITHUB_OUTPUT'):
            with open(os.environ['GITHUB_OUTPUT'], 'a') as f:
                for i, l in enumerate(lv): f.write('l%d=%s\n' % (i, json.dumps(l)))
    elif a.cmd == 'run': sys.exit(run(a.args[0], a.shard, a.of))
    elif a.cmd == 'merge': merge(a.args[0], a.parts, a.prefix, 'merged', a.run)
    elif a.cmd == 'publish': publish(a.args[0], a.args[1])
    elif a.cmd == 'local': local(a.args[0], a.work, a.shards, a.pip)
    elif a.cmd == 'reduce': reduce(a.who, a.dir, a.ref, a.name, a.dry, a.all)
    else: sys.exit(__doc__)

if __name__ == '__main__': main()
