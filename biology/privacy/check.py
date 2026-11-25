"""biology/privacy/check.py: privacy definitions as exact, exhaustive counting.
Run from repo root: python3 -I biology/privacy/check.py   (standard library only)."""
import itertools, json, time
from fractions import Fraction as F
from collections import Counter
from math import comb

T0 = time.time()
STATES = 0
def show(label, value, expected):
    assert value == expected, (label, value, expected)
    print(f"{label}: {value}")

# ---------- 1. k-anonymity ----------
# Two quasi-identifier attributes, each with values 0..3.
# Generalization lattice per attribute: level 0 = exact, level 1 = pair {0,1}/{2,3}, level 2 = '*'.
def gen(v, lev): return v if lev == 0 else (v // 2 if lev == 1 else 0)
NODES = [(a, b) for a in range(3) for b in range(3)]
def kof(table, node):
    c = Counter((gen(x, node[0]), gen(y, node[1])) for x, y in table)
    return min(c.values())
def leq(u, v): return u[0] <= v[0] and u[1] <= v[1]

def lattice_search(ks, k):
    # breadth-first by height; stop at the first height with a node reaching k
    for h in range(5):
        hit = sorted(nd for nd in NODES if sum(nd) == h and ks[nd] >= k)
        if hit: return hit
    return None

N_ROWS = 4
VALS = [(x, y) for x in range(4) for y in range(4)]
maxk = Counter(); ties = Counter(); least2 = Counter(); minimal_sets_ok = 0
for table in itertools.product(VALS, repeat=N_ROWS):
    STATES += 1
    ks = {nd: kof(table, nd) for nd in NODES}
    # monotone: generalizing never lowers k
    for u in NODES:
        for v in NODES:
            if leq(u, v): assert ks[u] <= ks[v]
    maxk[ks[(0, 0)]] += 1
    found = lattice_search(ks, 2)
    # brute force: all nodes reaching k=2, minimal height
    ok = [nd for nd in NODES if ks[nd] >= 2]
    if ok:
        hmin = min(sum(nd) for nd in ok)
        assert found == sorted(nd for nd in ok if sum(nd) == hmin)
        # and every minimal-height node is minimal in the lattice order
        for nd in found:
            assert not any(o != nd and leq(o, nd) for o in ok)
        least2[sum(found[0])] += 1; ties[len(found)] += 1
    else:
        assert found is None
    minimal_sets_ok += 1
total = 16 ** N_ROWS
show("1. tables (4 rows, 2 attributes x 4 values)", sum(maxk.values()), total)
assert maxk[3] == 0 and set(maxk) <= {1, 2, 4}
# independent count: k=4 means all rows equal (16); k=2 means two pairs of distinct values: C(16,2)*C(4,2)
show("1. k=4 tables", maxk[4], 16)
show("1. k=2 tables", maxk[2], comb(16, 2) * comb(4, 2))
show("1. k=1 tables", maxk[1], total - 16 - comb(16, 2) * 6)
show("1. every table reaches k=2 at top node (*,*)", sum(least2.values()), total)
show("1. tables by least height reaching k=2, h=0..4", [least2[h] for h in range(5)], [736, 4064, 18368, 25984, 16384])
show("1. tables by number of tied least nodes, 1..3", [ties[t] for t in (1, 2, 3)], [60448, 5088, 0])
show("1. lattice search equals brute force, tables", minimal_sets_ok, total)

# ---------- 2. uniques ----------
def uniques_dist(n, D):
    c = Counter()
    for t in itertools.product(range(D), repeat=n):
        cnt = Counter(t); c[sum(1 for v in cnt.values() if v == 1)] += 1
    return {u: F(m, D ** n) for u, m in sorted(c.items())}
pairs = 0
for n in range(1, 7):
    for D in range(1, 6):
        if D ** n > 20000: continue
        dist = uniques_dist(n, D); STATES += D ** n
        assert sum(dist.values()) == 1
        E = sum(u * p for u, p in dist.items())
        assert E == n * (1 - F(1, D)) ** (n - 1), (n, D)
        pairs += 1
show("2. (n,D) pairs where exhaustive E[uniques] = n(1-1/D)^(n-1)", pairs, 30)
d = uniques_dist(4, 3)
show("2. n=4, D=3 P[0],P[1],P[2]", [d.get(0), d.get(1), d.get(2)], [F(7, 27), F(8, 27), F(4, 9)])
show("2. n=4, D=3 E[uniques]", sum(u*p for u, p in d.items()), F(32, 27))

# ---------- 3. randomized response ----------
def rr(p):  # report true bit with prob p
    return {(b, o): (p if o == b else 1 - p) for b in (0, 1) for o in (0, 1)}
def mech(db, P, reps=1):
    out = {}
    for o in itertools.product((0, 1), repeat=len(db) * reps):
        pr = F(1)
        for r in range(reps):
            for i, b in enumerate(db): pr *= P[(b, o[r * len(db) + i])]
        out[o] = pr
    return out
def max_loss(P, nmax, reps=1):
    global STATES
    worst = F(0); count = 0
    for n in range(1, nmax + 1):
        for db in itertools.product((0, 1), repeat=n):
            for i in range(n):
                nb = list(db); nb[i] ^= 1
                m1, m2 = mech(db, P, reps), mech(tuple(nb), P, reps)
                for o in m1:
                    worst = max(worst, m1[o] / m2[o]); STATES += 1
                count += 1
    return worst, count
for p, e in [(F(3, 4), 3), (F(2, 3), 2), (F(1, 2), 1)]:
    w, c = max_loss(rr(p), 4)
    show(f"3. RR p={p}: max ratio exp(eps), neighbour pairs n<=4", (w, c), (F(e), 2*1 + 4*2 + 8*3 + 16*4))
    w2, _ = max_loss(rr(p), 3, reps=2)
    show(f"3. RR p={p} run twice: max ratio", w2, F(e) ** 2)
# mixed composition p=3/4 then p=2/3
def mech2(db):
    a, b = mech(db, rr(F(3, 4))), mech(db, rr(F(2, 3)))
    return {(x, y): a[x] * b[y] for x in a for y in b}
w = F(0)
for n in range(1, 4):
    for db in itertools.product((0, 1), repeat=n):
        for i in range(n):
            nb = list(db); nb[i] ^= 1
            m1, m2 = mech2(db), mech2(tuple(nb))
            w = max(w, max(m1[o] / m2[o] for o in m1)); STATES += len(m1)
show("3. mixed composition 3 x 2", w, F(6))

# ---------- 4. set partitions ----------
def setparts(n):
    if n == 0: yield []; return
    for p in setparts(n - 1):
        for i in range(len(p)): yield p[:i] + [p[i] + [n]] + p[i+1:]
        yield p + [[n]]
def stirling(n, k):
    if n == k: return 1
    if k == 0 or k > n: return 0
    return k * stirling(n - 1, k) + stirling(n - 1, k - 1)
bell = []
for n in range(1, 9):
    ps = list(setparts(n)); STATES += len(ps)
    blocks = Counter(len(p) for p in ps)
    for k in blocks: assert blocks[k] == stirling(n, k)
    bell.append(len(ps))
show("4. Bell numbers n=1..8 (enumerated)", bell, [1, 2, 5, 15, 52, 203, 877, 4140])
# equality pattern of rows: tables over D values = sum_k S(n,k) D(D-1)..(D-k+1)
def fall(D, k):
    r = 1
    for i in range(k): r *= D - i
    return r
for n in range(1, 7):
    for D in range(1, 6):
        assert sum(stirling(n, k) * fall(D, k) for k in range(n + 1)) == D ** n
# uniques via partitions: count tables with u singleton blocks equals exhaustive count
agreed = []
for n, D in [(4, 3), (5, 3), (4, 4)]:
    c = Counter()
    for p in setparts(n):
        c[sum(1 for b in p if len(b) == 1)] += fall(D, len(p))
    ex = uniques_dist(n, D)
    assert {u: F(m, D ** n) for u, m in c.items() if m} == {u: q for u, q in ex.items() if q}
    agreed.append((n, D))
show("4. uniques from set partitions agree with enumeration", agreed, [(4, 3), (5, 3), (4, 4)])
show("4. Stirling S(5,k), k=1..5", [stirling(5, k) for k in range(1, 6)], [1, 15, 25, 10, 1])

sec = round(time.time() - T0, 2)
assert sec < 60
print("PASS")
print(json.dumps({"states": STATES, "seconds": sec}))
