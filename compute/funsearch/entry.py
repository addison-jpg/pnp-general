#!/usr/bin/env python3
"""git-compute entries (.github/workflows/compute.yml; specs in compute/funsearch/specs/).
  search:   entry.py search --target T --proposer gguf --model REPO --minutes M  --shard i --of N --out PATH
            one independent FunSearch run per shard (seed = shard).  PATH gets the run log (JSON lines); the best witnesses, the
            candidates and the summary are also printed to the job log as `FSJSON {...}` (artifacts cannot be fetched from the cloud
            container, logs can).  Weights are downloaded inside the runner, never committed.
  recheck:  entry.py recheck [--input NAME=PATH] --shard 0 --of 1 --out PATH
            the SEPARATE job of the independent evaluator: every witness in the upstream job's output (`--input`, once the job DAG
            of dag.py is on main) or else in compute/funsearch/candidates/*.json and compute/funsearch/results/*/*.json, through
            recheck.py in its own process.  One CONFIRMED / REJECTED line each; exit 1 if a file under results/ is rejected.
  assemble: entry.py assemble LOG [LOG ...] --out DIR     rebuild a run directory (best/, candidates/, summary.json) from job logs,
            ready for `fs.py record DIR --who SEAT`"""
import os, sys, json, glob, argparse, subprocess, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..')); sys.path.insert(0, HERE)

def fname(w, tag): return '%s.%s.json' % ((w.get('system') or w.get('kind')).replace('(', '').replace(')', '').replace(',', '_'), tag)

def search(a, rest):
    import fs
    work = os.path.join(os.environ.get('RUNNER_TEMP') or tempfile.gettempdir(), 'fs-run-%d' % a.shard)
    sys.argv = ['fs.py', 'run', '--out', work, '--seed', str(a.shard)] + rest
    os.chdir(ROOT); fs.main()
    for sub in ('best', 'candidates'):
        for p in sorted(glob.glob(os.path.join(work, sub, '*.json'))):
            print('FSJSON ' + json.dumps({'shard': a.shard, 'kind': sub, 'file': os.path.basename(p), 'witness': json.load(open(p))}, separators=(',', ':')), flush=True)
    print('FSJSON ' + json.dumps({'shard': a.shard, 'kind': 'summary', 'summary': json.load(open(os.path.join(work, 'summary.json')))}), flush=True)
    open(a.out, 'w').write(open(os.path.join(work, 'log.jsonl')).read())

def recheck(a, rest):
    items = []
    for spec in a.input or []:
        for line in open(spec.split('=', 1)[1]):
            try: r = json.loads(line)
            except ValueError: continue
            for w in r.get('witnesses', []): items.append(('upstream', w))
    if not items:
        for p in sorted(glob.glob(os.path.join(HERE, 'candidates', '*.json')) + glob.glob(os.path.join(HERE, 'results', '*', '*.json'))):
            if os.path.basename(p) != 'summary.json': items.append((os.path.relpath(p, ROOT), json.load(open(p))))
    n = bad = below = 0; out = open(a.out, 'w')
    for i, (src, w) in enumerate(items):
        if i % a.of != a.shard: continue
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, 'w.json'); json.dump(w, open(p, 'w'))
            cmd = ['--rerun', p] if w.get('kind') == 'command' else ['--file', p]
            r = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'recheck.py')] + cmd, capture_output=True, text=True, cwd=ROOT)
        ok = r.returncode == 0; n += 1; bad += (not ok) and src != 'upstream'; sc = w.get('claim', {}).get('score'); below += bool(ok and sc and sc > 0)
        line = json.dumps({'source': src, 'system': w.get('system'), 'score': sc, 'confirmed': ok, 'tail': r.stdout.strip().splitlines()[-1:]})
        out.write(line + '\n'); print(('CONFIRMED ' if ok else 'REJECTED ') + line, flush=True)
    print('SUMMARY ' + json.dumps({'witnesses': n, 'rejected': bad, 'confirmed_below_base': below}), flush=True)
    sys.exit(1 if bad else 0)

def assemble(a, rest):
    summ = []; os.makedirs(a.out, exist_ok=True); best = {}
    for d in ('best', 'candidates'): os.makedirs(os.path.join(a.out, d), exist_ok=True)
    for p in rest:
        for line in open(p, encoding='utf-8', errors='replace'):
            k = line.find('FSJSON ')
            if k < 0: continue
            r = json.loads(line[k + 7:])
            if r['kind'] == 'summary': summ.append(r['summary'])
            elif r['kind'] == 'candidates': json.dump(r['witness'], open(os.path.join(a.out, 'candidates', 's%d.%s' % (r['shard'], r['file'])), 'w'))
            else:
                w = r['witness']; tag = r['file'].split('.')[-2]; key = (w.get('system') or w.get('kind')) + '|' + tag; sc = w.get('claim', {}).get('score', 0)
                if key not in best or sc > best[key][0]: best[key] = (sc, w); json.dump(w, open(os.path.join(a.out, 'best', fname(w, tag)), 'w'))
    assert summ, 'no FSJSON summary lines found'
    tot = dict(summ[0]); tot['shards'] = len(summ)
    for k in ('seconds', 'tokens', 'proposed', 'unparsed', 'duplicate', 'ran', 'distinct_programs', 'candidates', 'resets'): tot[k] = sum(s[k] for s in summ)
    tot['verdicts'] = {v: sum(s['verdicts'].get(v, 0) for s in summ) for v in sorted({v for s in summ for v in s['verdicts']})}
    tot['best'] = {k: v[0] for k, v in sorted(best.items())}; tot['beat_base'] = any(s['beat_base'] for s in summ); tot.pop('seed', None)
    json.dump(tot, open(os.path.join(a.out, 'summary.json'), 'w'), indent=1); print(json.dumps(tot))

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('cmd', choices=['search', 'recheck', 'assemble'])
    ap.add_argument('--shard', type=int, default=0); ap.add_argument('--of', type=int, default=1); ap.add_argument('--out'); ap.add_argument('--input', action='append')
    a, rest = ap.parse_known_args()
    {'search': search, 'recheck': recheck, 'assemble': assemble}[a.cmd](a, rest)

if __name__ == '__main__': main()
