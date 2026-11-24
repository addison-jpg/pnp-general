# Chain depth: the least k such that some path of k points from the empty cube has
# sum(gain - cost) >= 0 at its END (prefixes may be negative). k = 1 is the point step (C2),
# k = n is the count. Serves README items L5, C3. Run: python3 -I one-not/tools/kill_tests/chain_depth.py [maxk]
import sys, os, json, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import f2lib as L
MAXK = int(sys.argv[1]) if len(sys.argv) > 1 else 3
print("| circuit | n | least k | path | sum at the end |"); print("|---|---|---|---|---|")
for f in sorted(glob.glob('one-not/data/witnesses/*.json') + glob.glob('one-not/data/witnesses/nonlocal/*.json')):
    d = json.load(open(f))
    c = L.mk(d.get('name', f), d['n'], d['sets'], d['gates'], d['outs'], need_not=False)
    if c is None: continue
    memo = {}
    def F(Q):
        if Q not in memo: memo[Q] = len(L.F2(c, Q))
        return memo[Q]
    frontier = [(0, 0, ())]; found = None
    for k in range(1, MAXK + 1):
        nxt = {}
        for Q, s, path in frontier:
            for v in L.apts(c, Q):
                cst = L.cost(c, Q, v); Q2 = Q | 1 << v; s2 = s + (F(Q) - F(Q2)) - cst
                if s2 >= 0 and found is None: found = (k, path + (v,), s2)
                if Q2 not in nxt or nxt[Q2][0] < s2: nxt[Q2] = (s2, path + (v,))
        if found: break
        frontier = [(Q, s, p) for Q, (s, p) in nxt.items()]
    print(f"| {os.path.basename(f)} | {d['n']} | {found[0] if found else '> ' + str(MAXK)} | {found[1] if found else ''} | {found[2] if found else ''} |")
