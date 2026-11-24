"""Sweep: for every (1,1)-disjoint system from stdin (graph6 from nauty-genbg, points = first n vertices),
ask whether a circuit of size base-1 exists that is correct only on the given row set.
mode 'sc' = monotone, rows weight<=1 (= Wegener's set circuits with union/intersection);
mode 'sc1' = <=1 NOT, rows weight<=1 (set circuits with one complement, value at 0 tracked);
mode 'full1' = <=1 NOT, all rows (= 951 itself).
Usage: nauty-genbg ... | python3 sweep.py n mode out.jsonl [filter]
filter 'core2': every point in >= 2 sets."""
import sys, json, time
from multiprocessing import Pool
import networkx as nx
sys.path.insert(0, '/tmp/claude-0/-home-user/8c137ad4-29bc-5711-be93-e44232612946/scratchpad')
from relax import solve, rowset

n = int(sys.argv[1]); mode = sys.argv[2]; out = sys.argv[3]; filt = sys.argv[4] if len(sys.argv) > 4 else ''


def job(sets):
    base = sum(len(S) - 1 for S in sets)
    rows = rowset(n, 'all' if mode == 'full1' else 'w<=1')
    t = time.time()
    sat, model = solve(n, sets, base - 1, rows, mono=(mode == 'sc'), want_model=True)
    return {'sets': sets, 'base': base, 'sat': sat, 'model': model, 't': round(time.time() - t, 2)}


def systems():
    for line in sys.stdin:
        g = nx.from_graph6_bytes(line.strip().encode())
        sets = [sorted(g[v]) for v in range(n, g.number_of_nodes())]
        if filt == 'core2' and any(sum(1 for S in sets if p in S) < 2 for p in range(n)):
            continue
        if max(len(S) for S in sets) < 3:      # all sets of size 2: trivially base (distinct outputs)
            continue
        yield sets


if __name__ == '__main__':
    cnt = 0; hits = 0
    with Pool(4) as pool, open(out, 'w') as f:
        for r in pool.imap_unordered(job, systems(), chunksize=1):
            cnt += 1; hits += r['sat']
            f.write(json.dumps(r) + '\n'); f.flush()
            if r['sat']:
                print('BEATS BASE:', r, flush=True)
    print(f'n={n} mode={mode} systems={cnt} beat_base={hits}', flush=True)
