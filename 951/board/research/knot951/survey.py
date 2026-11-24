"""survey.py FILE [maxbase] : for every system in FILE (JSON list of set lists) decide, at s = base-1,
SAT/UNSAT with UNLIMITED NOTs (k = s).  UNSAT => min size = base for every k (k=0 gives base).
If SAT: find min k and min s.  Results appended to results.jsonl (restart-safe, keyed by sets,s,k)."""
import sys, json, time, os
sys.path.insert(0, '/home/user/ku951')
from multiprocessing import Pool
import knot
RES = '/home/user/ku951/results.jsonl'
def key(sets, s, k): return json.dumps([sorted(map(sorted, sets)), s, k])
def done():
    d = {}
    if os.path.exists(RES):
        for l in open(RES):
            r = json.loads(l); d[key(r['sets'], r['s'], r['k'])] = r
    return d
def run(job):
    sets, s, k, name = job
    n = knot.nmax(sets); t0 = time.time()
    res = knot.solve(n, sets, s, k)
    rec = dict(name=name, n=n, sets=sets, base=knot.base(sets), s=s, k=k, sat=res is not None,
               secs=round(time.time() - t0, 1), enc='knot.solve sym=True cegar cadical195')
    if res: rec['gates'], rec['outs'] = res
    return rec
if __name__ == '__main__':
    L = json.load(open(sys.argv[1])); mb = int(sys.argv[2]) if len(sys.argv) > 2 else 99
    ks = sys.argv[3] if len(sys.argv) > 3 else 'all'
    d = done(); jobs = []
    for i, sets in enumerate(L):
        b = knot.base(sets)
        if b > mb: continue
        k = b - 1 if ks == 'all' else int(ks)
        if key(sets, b - 1, k) not in d and not (ks != 'all' and key(sets, b - 1, b - 1) in d and not d[key(sets, b-1, b-1)]['sat']):
            jobs.append((sets, b - 1, k, '%s#%d' % (os.path.basename(sys.argv[1]), i)))
    jobs.sort(key=lambda j: j[1])
    print(len(jobs), 'jobs', flush=True)
    with Pool(3) as P, open(RES, 'a') as f:
        for rec in P.imap_unordered(run, jobs):
            f.write(json.dumps(rec) + '\n'); f.flush()
            print(rec['name'], rec['n'], rec['base'], 's', rec['s'], 'k', rec['k'], 'SAT' if rec['sat'] else 'UNSAT', rec['secs'], flush=True)
