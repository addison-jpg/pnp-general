"""Neurons join into networks: directed graphs, motifs, directed flag complexes.
Run from repo root: python3 -I biology/brain/network/check.py"""
import itertools, json, time
from fractions import Fraction
from math import factorial, comb

T0 = time.time()
STATES = 0

def arcs(n):
    return [(i, j) for i in range(n) for j in range(n) if i != j]

def graphs(n):
    A = arcs(n)
    for mask in range(1 << len(A)):
        yield frozenset(A[b] for b in range(len(A)) if mask >> b & 1)

def weakly_connected(n, E):
    if n == 0:
        return False
    seen, stack = {0}, [0]
    while stack:
        u = stack.pop()
        for (a, b) in E:
            for x, y in ((a, b), (b, a)):
                if x == u and y not in seen:
                    seen.add(y); stack.append(y)
    return len(seen) == n

def canon(n, E, perms):
    return min(tuple(sorted((p[a], p[b]) for a, b in E)) for p in perms)

# ---- 1. motifs by canonical forms, n = 1..4 ----
reps = {}
for n in range(1, 5):
    perms = list(itertools.permutations(range(n)))
    seen = {}
    for E in graphs(n):
        STATES += 1
        c = canon(n, E, perms)
        if c not in seen:
            seen[c] = E
    reps[n] = {c: E for c, E in seen.items()}
all_iso_enum = [len(reps[n]) for n in range(1, 5)]
conn_enum = [sum(1 for E in reps[n].values() if weakly_connected(n, E)) for n in range(1, 5)]
assert all_iso_enum == [1, 3, 16, 218], all_iso_enum
assert conn_enum == [1, 2, 13, 199], conn_enum
print("digraphs up to iso, n=1..4 (enumeration):", all_iso_enum)
print("weakly connected, n=1..4 (enumeration):  ", conn_enum)

# ---- Burnside for n = 1..6, then inverse Euler transform ----
def burnside(n):
    tot = 0
    for p in itertools.permutations(range(n)):
        seen, c = set(), 0
        for a in arcs(n):
            if a in seen: continue
            c += 1; x = a
            while x not in seen:
                seen.add(x); x = (p[x[0]], p[x[1]])
        tot += 2 ** c
    assert tot % factorial(n) == 0
    return tot // factorial(n)
N = 6
D = [burnside(n) for n in range(1, N + 1)]
assert D[:4] == all_iso_enum
assert D == [1, 3, 16, 218, 9608, 1540944], D
# Euler transform: a = all, c = connected. n*a_n = sum_{k=1..n} b_k a_{n-k}, b_k = sum_{d|k} d c_d
a = [1] + D
c = [0] * (N + 1); b = [0] * (N + 1)
for n in range(1, N + 1):
    s = sum(b[k] * a[n - k] for k in range(1, n))
    bn = n * a[n] - s
    c[n] = (bn - sum(d * c[d] for d in range(1, n) if n % d == 0)) // n
    b[n] = bn
CONN = c[1:]
assert CONN[:4] == conn_enum
assert CONN == [1, 2, 13, 199, 9364, 1530843], CONN
print("digraphs up to iso, n=1..6 (Burnside):", D)
print("weakly connected, n=1..6 (Burnside + Euler transform):", CONN)
print("three-node weakly connected patterns (Milo et al. motifs):", CONN[2])

# ---- 2. directed flag complex, Betti over GF(2), Euler-Poincare ----
def simplices(n, E):
    S = [[(v,) for v in range(n)]]
    while True:
        nxt = []
        for s in S[-1]:
            for v in range(n):
                if v not in s and all((u, v) in E for u in s):
                    nxt.append(s + (v,))
        if not nxt: return S
        S.append(nxt)

def rank2(rows):
    rows = [r for r in rows if r]; r = 0; piv = {}
    for x in rows:
        while x:
            h = x.bit_length() - 1
            if h in piv: x ^= piv[h]
            else: piv[h] = x; r += 1; break
    return r

def betti(S):
    idx = [{s: i for i, s in enumerate(L)} for L in S]
    ranks = [0]
    for k in range(1, len(S)):
        rows = []
        for s in S[k]:
            m = 0
            for i in range(len(s)):
                m |= 1 << idx[k - 1][s[:i] + s[i + 1:]]
            rows.append(m)
        ranks.append(rank2(rows))
    ranks.append(0)
    return [len(S[k]) - ranks[k] - ranks[k + 1] for k in range(len(S))]

ep_checked = 0
dist2 = {}
bsum = {}
for n in range(1, 5):
    d = {}
    for E in graphs(n):
        STATES += 1
        S = simplices(n, E); B = betti(S)
        chi = sum((-1) ** k * len(L) for k, L in enumerate(S))
        assert chi == sum((-1) ** k * x for k, x in enumerate(B))
        assert all(x >= 0 for x in B)
        ep_checked += 1
        t = len(S[2]) if len(S) > 2 else 0
        d[t] = d.get(t, 0) + 1
        key = tuple(B)
        bsum[(n, key)] = bsum.get((n, key), 0) + 1
    dist2[n] = [d.get(t, 0) for t in range(max(d) + 1)]
assert ep_checked == 1 + 4 + 64 + 4096
print("Euler-Poincare holds for all", ep_checked, "labelled digraphs on 1..4 nodes")
for n in (3, 4):  # independent check: total simplices = ordered triples * 2^(m-3)
    m = n * (n - 1)
    assert sum(dist2[n]) == 2 ** m
    assert sum(t * x for t, x in enumerate(dist2[n])) == factorial(n) // factorial(n - 3) * 2 ** (m - 3)
print("labelled digraphs on 3 nodes by number of directed 2-simplices:", dist2[3])
print("labelled digraphs on 4 nodes by number of directed 2-simplices:", dist2[4])
assert sum(dist2[4]) == 4096
b1pos = {n: sum(v for (m, k), v in bsum.items() if m == n and len(k) > 1 and k[1] > 0) for n in range(1, 5)}
b2pos = {n: sum(v for (m, k), v in bsum.items() if m == n and len(k) > 2 and k[2] > 0) for n in range(1, 5)}
print("labelled digraphs with beta1 > 0, n=1..4:", [b1pos[n] for n in range(1, 5)])
print("labelled digraphs with beta2 > 0, n=1..4:", [b2pos[n] for n in range(1, 5)])
assert b1pos[3] > 0  # e.g. the directed 3-cycle

# ---- 3. expected number of directed k-simplices in G(n, p) ----
def expected_formula(n, k, p):
    if k + 1 > n: return Fraction(0)
    return Fraction(factorial(n), factorial(n - k - 1)) * p ** comb(k + 1, 2)
checks3 = 0
for n in range(1, 5):
    m = n * (n - 1)
    byE = {}  # (k, edges) -> total simplex count
    for E in graphs(n):
        S = simplices(n, E)
        for k in range(n):
            cnt = len(S[k]) if k < len(S) else 0
            byE[(k, len(E))] = byE.get((k, len(E)), 0) + cnt
    for k in range(n):
        for p in [Fraction(j, m + 2) for j in range(m + 2)]:  # m+2 points > degree m: polynomial identity
            lhs = sum(Fraction(byE[(k, e)]) * p ** e * (1 - p) ** (m - e) for e in range(m + 1)) \
                  / 1  # byE already sums over graphs with e edges
            assert lhs == expected_formula(n, k, p), (n, k, p)
            checks3 += 1
print("E[#directed k-simplices] = n!/(n-k-1)! * p^C(k+1,2): exact identity checked,", checks3, "evaluations")

# ---- 4. tree against rhizome: critical connections ----
def critical_fraction(n, E):
    crit = sum(1 for e in E if not weakly_connected(n, E - {e}))
    return crit, len(E)
table = []
for n in range(1, 5):
    conn = [E for E in reps[n].values() if weakly_connected(n, E)]
    none_crit = all_crit = 0
    fr = {}
    for E in conn:
        cr, m = critical_fraction(n, E)
        und = {frozenset(e) for e in E}
        is_tree = len(und) == n - 1 and len(E) == n - 1
        if m: fr[Fraction(cr, m)] = fr.get(Fraction(cr, m), 0) + 1
        # convention: n=1 (no arcs) counts as all-critical (vacuous) but NOT as no-critical
        if m and cr == 0: none_crit += 1
        if cr == m: all_crit += 1
        assert (cr == m) == is_tree  # every connection critical iff an oriented tree
    table.append((n, len(conn), all_crit, none_crit))
    print("n=%d connected=%d all-critical(oriented trees)=%d no-critical=%d fractions=%s" %
          (n, len(conn), all_crit, none_crit, {str(k): v for k, v in sorted(fr.items())}))
assert [t[2] for t in table] == [1, 1, 3, 8]  # oriented trees (OEIS A000238)
assert [t[1] for t in table] == CONN[:4]

# regression values (computed by this script, not from memory)
assert dist2[3] == [39, 12, 6, 6, 0, 0, 1]
assert [b1pos[n] for n in range(1, 5)] == [0, 1, 26, 1842]
assert [b2pos[n] for n in range(1, 5)] == [0, 0, 1, 498]
assert [t[3] for t in table] == [0, 1, 8, 146]
print("PASS")
print(json.dumps({"states": STATES, "seconds": round(time.time() - T0, 2)}))
