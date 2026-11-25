"""One neuron: the dendritic arbor as a rooted binary tree. Exact checks, stdlib only.
Run from repo root: python3 -I brain/neuron/check.py"""
import json, time
from fractions import Fraction as F
from itertools import product
from math import factorial
T0 = time.time()
NMAX = 9
TIP = ()  # a tip; a branch point is a pair (left, right)

def tips(t): return 1 if t == TIP else tips(t[0]) + tips(t[1])
def canon(t):
    if t == TIP: return TIP
    a, b = canon(t[0]), canon(t[1])
    return (a, b) if repr(a) <= repr(b) else (b, a)

# ---- 1. shapes: ordered (Catalan) and unordered (Wedderburn-Etherington)
ordered = {1: [TIP]}
for n in range(2, NMAX + 1):
    ordered[n] = [(l, r) for k in range(1, n) for l in ordered[k] for r in ordered[n - k]]
cat = [len(ordered[n]) for n in range(1, NMAX + 1)]
catrec = [factorial(2 * (n - 1)) // (factorial(n - 1) * factorial(n)) for n in range(1, NMAX + 1)]
assert cat == catrec == [1, 1, 2, 5, 14, 42, 132, 429, 1430]
shapes = {n: sorted({canon(t) for t in ordered[n]}, key=repr) for n in ordered}
we = [len(shapes[n]) for n in range(1, NMAX + 1)]
# Wedderburn-Etherington recurrence
W = [0, 1]
for n in range(2, 12):
    if n % 2: W.append(sum(W[i] * W[n - i] for i in range(1, (n + 1) // 2)))
    else:
        m = n // 2
        W.append(sum(W[i] * W[n - i] for i in range(1, m)) + W[m] * (W[m] + 1) // 2)
assert we == W[1:NMAX + 1]
assert W[1:12] == [1, 1, 1, 2, 3, 6, 11, 23, 46, 98, 207]
print("ordered shapes (Catalan)   n=1..9:", cat)
print("unordered shapes (W-E)     n=1..9:", we, " recurrence n=1..11:", W[1:12])
# structure counts: n tips -> n-1 branch points, 2n-1 segments (with trunk)
for n in range(1, NMAX + 1):
    for t in ordered[n]:
        def bp(t): return 0 if t == TIP else 1 + bp(t[0]) + bp(t[1])
        assert bp(t) == n - 1
print("every arbor: n-1 branch points, 2n-1 segments (trunk counted): PASS")

# ---- 2. growth models, summed over all growth histories (exact)
def grow_terminal(t):  # one new branch at each tip, each choice one history
    if t == TIP: return [(TIP, TIP)]
    return [(x, t[1]) for x in grow_terminal(t[0])] + [(t[0], x) for x in grow_terminal(t[1])]
def grow_segmental(t):  # one new branch on each segment (segment = edge above a node)
    out = [(t, TIP)]
    if t != TIP:
        out += [(x, t[1]) for x in grow_segmental(t[0])] + [(t[0], x) for x in grow_segmental(t[1])]
    return out
def run(grow, nmax):
    dist = {TIP: 1}; hist = [1]; P = {1: {TIP: F(1)}}
    for n in range(2, nmax + 1):
        nd = {}
        for t, w in dist.items():
            ch = grow(t)
            for s in ch: nd[s] = nd.get(s, 0) + w
        dist = nd; hist.append(sum(nd.values()))
        tot = hist[-1]; pu = {}
        for t, w in dist.items():
            c = canon(t); pu[c] = pu.get(c, 0) + F(w, tot)
        P[n] = pu
    return hist, P
# brute force: literally list every history for small n, as a cross-check
def brute(grow, nmax):
    res = {}
    def rec(t, n, path_w):
        res.setdefault(n, {}); c = canon(t); res[n][c] = res[n].get(c, 0) + 1
        if n < nmax:
            for s in grow(t): rec(s, n + 1, 0)
    rec(TIP, 1, 0); return res
hT, PT = run(grow_terminal, NMAX); hS, PS = run(grow_segmental, NMAX)
dfact = lambda m: 1 if m <= 0 else m * dfact(m - 2)
assert hT == [factorial(n - 1) for n in range(1, NMAX + 1)]
assert hS == [dfact(2 * n - 3) for n in range(1, NMAX + 1)]
print("growth histories, terminal  (n-1)! :", hT)
print("growth histories, segmental (2n-3)!!:", hS)
for g, P in ((grow_terminal, PT), (grow_segmental, PS)):
    b = brute(g, 7)
    for n in range(1, 8):
        tot = sum(b[n].values())
        assert {k: F(v, tot) for k, v in b[n].items()} == P[n]
print("history-by-history brute force agrees for n<=7: PASS")
for n in range(1, NMAX + 1):
    assert sum(PT[n].values()) == 1 == sum(PS[n].values())
    assert set(PT[n]) == set(PS[n]) == set(shapes[n])
def name(t): return "*" if t == TIP else "(" + name(t[0]) + name(t[1]) + ")"
assert [str(PT[4][s]) for s in shapes[4]] == ["2/3", "1/3"] and [str(PS[4][s]) for s in shapes[4]] == ["4/5", "1/5"]
assert [str(PT[5][s]) for s in shapes[5]] == ["1/3", "1/6", "1/2"] and [str(PS[5][s]) for s in shapes[5]] == ["4/7", "1/7", "2/7"]
for n in (4, 5):
    for s in shapes[n]: print(f"  n={n} {name(s):14s} terminal {str(PT[n][s]):6s} segmental {PS[n][s]}")

# ---- 3. join: terminal = Yule, segmental = uniform (PDA)
def sym(t): return 0 if t == TIP else sym(t[0]) + sym(t[1]) + (1 if t[0] == t[1] else 0)
def yule(t):  # Yule: 2^(n-1-sym) * prod over branch points 1/(tips below - 1)
    def prod(t): return F(1) if t == TIP else F(1, tips(t) - 1) * prod(t[0]) * prod(t[1])
    return 2 ** (tips(t) - 1 - sym(t)) * prod(t)
def labelled(t): return factorial(tips(t)) // 2 ** sym(t)  # leaf labellings = n!/|Aut|
nshapes = 0
for n in range(2, NMAX + 1):
    assert sum(labelled(s) for s in shapes[n]) == dfact(2 * n - 3)
    for s in shapes[n]:
        nshapes += 1
        assert PT[n][s] == yule(s)
        assert PS[n][s] == F(labelled(s), dfact(2 * n - 3))
assert nshapes == 93
print(f"terminal == Yule and segmental == labelled/(2n-3)!! for all {nshapes} shapes, n=2..{NMAX}: PASS")

# ---- 4. asymmetry and Strahler order
def Ap(r, s): return F(0) if r + s <= 2 else F(abs(r - s), r + s - 2)
def asym(t):
    acc = []
    def rec(t):
        if t == TIP: return
        acc.append(Ap(tips(t[0]), tips(t[1]))); rec(t[0]); rec(t[1])
    rec(t); return sum(acc, F(0)) / len(acc)
def strahler(t):
    if t == TIP: return 1
    a, b = strahler(t[0]), strahler(t[1]); return a + 1 if a == b else max(a, b)
rows = []
for n in range(3, NMAX + 1):
    eaT = sum(p * asym(s) for s, p in PT[n].items()); eaS = sum(p * asym(s) for s, p in PS[n].items())
    esT = sum(p * strahler(s) for s, p in PT[n].items()); esS = sum(p * strahler(s) for s, p in PS[n].items())
    rows.append((n, eaT, eaS, esT, esS))
    if n >= 4: assert eaT != eaS and eaS > eaT
    print(f"  n={n} E[asym] T={eaT} S={eaS}   E[Strahler] T={esT} S={esS}")
# n=4 by hand: caterpillar partitions (3,1),(2,1),(1,1) -> (1+1+0)/3 = 2/3; balanced 0.
# terminal 2/3*2/3 = 4/9; segmental 4/5*2/3 = 8/15
assert rows[1][1] == F(4, 9) and rows[1][2] == F(8, 15)
assert [str(r[1]) for r in rows] == "1/2 4/9 11/24 34/75 247/540 1006/2205 513/1120".split()
assert [str(r[2]) for r in rows] == "1/2 8/15 47/84 359/630 1147/1980 26354/45045 354587/600600".split()
assert [str(r[3]) for r in rows] == "2 7/3 8/3 43/15 133/45 946/315 3851/1260".split()
assert [str(r[4]) for r in rows] == "2 11/5 17/7 55/21 91/33 408/143 2088/715".split()
print("expected asymmetry differs between models for every n=4..9: PASS")

# ---- 5. criticality: every segment is a bridge
def edges(t):
    E = []; cnt = [1]  # vertex 0 = soma
    def rec(t, parent):
        v = cnt[0]; cnt[0] += 1; E.append((parent, v))
        if t != TIP: rec(t[0], v); rec(t[1], v)
    rec(t, 0); return cnt[0], E
def connected(V, E):
    adj = {v: [] for v in range(V)}
    for a, b in E: adj[a].append(b); adj[b].append(a)
    seen = {0}; st = [0]
    while st:
        for w in adj[st.pop()]:
            if w not in seen: seen.add(w); st.append(w)
    return len(seen) == V
ncrit = 0
for n in range(1, NMAX + 1):
    for s in shapes[n]:
        V, E = edges(s); assert len(E) == 2 * n - 1 == V - 1 and connected(V, E)
        for i in range(len(E)): assert not connected(V, E[:i] + E[i + 1:])
        ncrit += 1
assert ncrit == 93 + 1
print(f"every segment critical in all {ncrit} arbor shapes n=1..{NMAX}: PASS")
print("PASS")
print(json.dumps({"states": sum(cat) + ncrit, "seconds": round(time.time() - T0, 2)}))
