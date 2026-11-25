"""Weight<=1 relaxed one-NOT SAT at s = base-1 on front's base-15 frontier (front33.json).
Jobs = (rank, NOT position p); 4 workers; a system is CERTIFIED (s >= base) when all p are UNSAT.
Usage: python3 frontier.py front33.json out.jsonl [rank_lo rank_hi]"""
import sys, json, time
from multiprocessing import Pool
sys.path.insert(0, '/tmp/claude-0/-home-user/8c137ad4-29bc-5711-be93-e44232612946/scratchpad')
from relax import solve, rowset

systems = json.load(open(sys.argv[1])); out = sys.argv[2]
lo, hi = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (0, 10**9)
systems = [x for x in systems if lo <= x['rank'] <= hi]


def job(a):
    x, p = a
    n, sets, s = x['n'], x['sets'], x['base'] - 1
    t = time.time()
    sat, model = solve(n, sets, s, rowset(n, 'w<=1'), p_list=[p], want_model=True)
    return {'rank': x['rank'], 'p': p, 'sat': sat, 'model': model, 't': round(time.time() - t, 1)}


if __name__ == '__main__':
    jobs = [(x, p) for x in systems for p in range(x['base'] - 1)]
    left = {x['rank']: x['base'] - 1 for x in systems}; anysat = {x['rank']: False for x in systems}
    with Pool(4) as pool, open(out, 'a') as f:
        for r in pool.imap(job, jobs, chunksize=1):
            f.write(json.dumps(r) + '\n'); f.flush()
            left[r['rank']] -= 1; anysat[r['rank']] |= r['sat']
            if r['sat']:
                print('RELAXED SAT (not a counterexample; needs full check):', r, flush=True)
            if left[r['rank']] == 0:
                print(f"rank {r['rank']}: {'relaxed SAT' if anysat[r['rank']] else 'CERTIFIED (all p UNSAT)'}", flush=True)
