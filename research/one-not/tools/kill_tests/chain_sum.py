# Chain sum (discrete Riemann sum) for realWitness gates (old: F2). Serves README items L5, C2.
# For a correct one-NOT circuit and ANY order of the points: sum of gains = |F2(empty)|, sum of costs = base.
# Also reports, per circuit, the minimum over sampled orders of the worst single term (gain - cost).
# Run from the repo root:  python3 -I research/one-not/tools/kill_tests/chain_sum.py [orders_per_circuit]
import sys, os, json, glob, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import f2lib as L
K = int(sys.argv[1]) if len(sys.argv) > 1 else 20
random.seed(1)
files = sorted(glob.glob('research/one-not/data/witnesses/*.json') + glob.glob('research/one-not/data/witnesses/nonlocal/*.json'))
tot = bad = 0; rows = []
for f in files:
    d = json.load(open(f))
    if d['n'] > 16: continue
    c = L.mk(d.get('name', f), d['n'], d['sets'], d['gates'], d['outs'], need_not=False)
    if c is None: continue
    n = d['n']; base = sum(len(R) - 1 for R in d['sets']); F0 = len(L.F2(c, 0))
    worst_best = None; neg = 0
    for _ in range(K):
        order = list(range(n)); random.shuffle(order)
        Q = 0; G = C = 0; worst = 0; prev = set(L.F2(c, 0))
        for v in order:
            cst = L.cost(c, Q, v); Q |= 1 << v; cur = set(L.F2(c, Q))
            assert cur <= prev, (f, 'F2 not decreasing')
            g = len(prev) - len(cur); G += g; C += cst; worst = min(worst, g - cst); prev = cur
        tot += 1
        if not (G == F0 and C == base and not prev): bad += 1
        neg += worst < 0
        worst_best = worst if worst_best is None else max(worst_best, worst)
    rows.append((os.path.basename(f), n, F0, base, F0 - base, neg, worst_best))
print(f"chains tested {tot}, identity failures {bad}")
print("| circuit | n | |realWitness| | base | integral = sum(gain - cost) | sampled orders with a negative term | best worst term |")
print("|---|---|---|---|---|---|---|")
for r in rows: print("| " + " | ".join(map(str, r)) + f"/{K} |" if False else "| " + " | ".join(map(str, r)) + " |")
