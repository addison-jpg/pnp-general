#!/usr/bin/env python3
"""Monogamy and polyamory over the field Q: fractional matchings, exact vertices, and a weight-matrix reading.

A fractional matching gives each pair (i, j) a weight x_ij in Q, 0 <= x_ij <= 1, with row and column sums <= k.
The integer models of check.py are the points with every x_ij in {0, 1}. Everything here is exact (Fraction).
Vertices are enumerated by the double description method: start from the box [0,1]^d, whose vertices are
the 0/1 points, and cut by one inequality at a time. Two vertices are joined by an edge exactly when no third
vertex is tight on every inequality both are tight on. On n = 2 this is asserted equal to a brute force over
every square subsystem of tight inequalities (Gaussian elimination in Q).
1. Stable polytope, k = 1 (Vande Vate 1989, Rothblum 1992, cited from memory). Complete strict lists.
   x >= 0, x <= 1, row sums <= 1, column sums <= 1, and for each pair (i, j) the stability inequality
       x_ij + sum over j' that i ranks above j of x_ij' + sum over i' that j ranks above i of x_i'j >= 1.
   On a 0/1 point it says: (i, j) is matched, or i holds someone it prefers to j, or j does. That is "(i, j)
   does not block". Asserted: every vertex is integral, and the vertices are exactly the stable matchings of
   check.py (imported brute force). n = 2: all 16 profiles (checked-finite). n = 3: the profiles whose index in
   check.profiles(3) is a multiple of 97, 481 of 46656 (tested). All 46656 would take about 20 minutes (estimated).
2. Capacity as a rational number k. The direct k-version of the stability inequality,
       k x_ij + sum over j' above j of x_ij' + sum over i' above i of x_i'j >= k,
   is not exact: it holds on every stable 0/1 point, but at k = 2 it also holds on unstable ones (two partners
   who are each one short of full add up to k). Counted on all n = 2 profiles and the same n = 3 sample. So no stable polytope
   is claimed for k > 1. Instead the plain fractional b-matching polytope {0 <= x <= 1, row and column sums <= k}
   is enumerated for k in {1, 3/2, 2}, n = 2 and 3: k = 1 and k = 2 give exactly the 0/1 matchings of check.py
   (7, 34 and 16, 265); k = 3/2 has fractional vertices, and they are listed for n = 2.
3. Weight matrices (analogy, not a biology claim). A fractional matching is a nonnegative matrix with row and column
   sums <= k, the shape of a normalised weight matrix from a presynaptic set A to a postsynaptic set B.
   Birkhoff and von Neumann (cited from memory): every doubly stochastic matrix is a convex combination of
   permutation matrices. Decomposed exactly, and the sum asserted equal to the matrix, on every 3x3 doubly
   stochastic matrix with entries in (1/q)Z, q = 1..6, and every 4x4 one with q = 1..3 (checked-finite); and on a
   seeded sample of 5x5 ones with q = 7 (tested). biology/brain/network models unweighted digraphs only, so the link
   to neurons is analogy.
Run: python3 -I culture/love/field.py   (writes field_fingerprints.json beside it; last line is JSON)
"""
import importlib.util, itertools, json, os, random, time
from fractions import Fraction as Fr

SAMPLE = 97   # n = 3: keep profile number i (0-based, in check.profiles order) when i % SAMPLE == 0
HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("love_check", os.path.join(HERE, "check.py"))
L = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(L)

# ---- polytopes: an inequality is (coefficients, rhs) meaning coef . x >= rhs ----
def val(c, x): return sum(a * b for a, b in zip(c[0], x)) - c[1]

def tight(cons, x):
    return sum(1 << t for t, c in enumerate(cons) if val(c, x) == 0)

def box(d):
    # 0 <= x_e <= 1 and the 2^d corners
    cons = []
    for e in range(d):
        cons.append(([1 if f == e else 0 for f in range(d)], 0))
        cons.append(([-1 if f == e else 0 for f in range(d)], -1))
    V = [tuple(Fr(v) for v in p) for p in itertools.product((0, 1), repeat=d)]
    return cons, V

def cut(d, cons, V, g):
    # vertices of {x in P : g} from the vertices V of P (P = the inequalities cons); exact
    Z = [tight(cons, x) for x in V]; s = [val(g, x) for x in V]
    plus = [i for i in range(len(V)) if s[i] > 0]; minus = [i for i in range(len(V)) if s[i] < 0]
    out = [V[i] for i in range(len(V)) if s[i] >= 0]
    for i in plus:
        for j in minus:
            z = Z[i] & Z[j]
            if bin(z).count("1") < d - 1: continue
            if any(u != i and u != j and Z[u] & z == z for u in range(len(V))): continue
            t = s[i] / (s[i] - s[j])
            out.append(tuple(a + t * (b - a) for a, b in zip(V[i], V[j])))
    return sorted(set(out))

def vertices_dd(d, extra, start=None):
    # box, then each inequality of `extra` in turn; `start` = (cons, V) to begin from instead of the box
    cons, V = start if start else box(d)
    cons = list(cons)
    for g in extra:
        V = cut(d, cons, V, g); cons.append(g)
    return cons, V

def solve(A, b):
    # unique solution of the square system A x = b over Q, or None
    n = len(A); M = [[Fr(v) for v in row] + [Fr(r)] for row, r in zip(A, b)]
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None: return None
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]; M[r] = [a - f * bb for a, bb in zip(M[r], M[c])]
    return tuple(M[i][n] / M[i][i] for i in range(n))

def vertices_brute(d, cons):
    # every d-subset of inequalities made tight; keep the feasible unique solutions
    out = set()
    for S in itertools.combinations(cons, d):
        x = solve([c[0] for c in S], [c[1] for c in S])
        if x is not None and all(val(c, x) >= 0 for c in cons): out.add(x)
    return sorted(out)

# ---- matchings as weights x[i*n + j] ----
def degree_cons(n, k):
    # row sums <= k and column sums <= k, written as >= with negated coefficients
    out = []
    for i in range(n): out.append(([-1 if e // n == i else 0 for e in range(n * n)], -k))
    for j in range(n): out.append(([-1 if e % n == j else 0 for e in range(n * n)], -k))
    return out

def stab_cons(n, ra, rb, k=1):
    # k x_ij + sum_{j' above j for i} x_ij' + sum_{i' above i for j} x_i'j >= k
    out = []
    for i in range(n):
        for j in range(n):
            c = [0] * (n * n); c[i * n + j] = k
            for j2 in range(n):
                if ra[i][j2] < ra[i][j]: c[i * n + j2] += 1
            for i2 in range(n):
                if rb[j][i2] < rb[j][i]: c[i2 * n + j] += 1
            out.append((c, k))
    return out

def point(n, m): return tuple(Fr(1) if (e // n, e % n) in m else Fr(0) for e in range(n * n))

def integral(x): return all(v.denominator == 1 for v in x)

def show(n, x): return [[str(x[i * n + j]) for j in range(n)] for i in range(n)]

# ---- Birkhoff-von Neumann ----
def birkhoff(A):
    # greedy exact decomposition: find a permutation inside the support, subtract its smallest entry, repeat
    n = len(A); R = [list(r) for r in A]; out = []
    while any(v for r in R for v in r):
        p = next((p for p in itertools.permutations(range(n)) if all(R[i][p[i]] > 0 for i in range(n))), None)
        assert p is not None, "a doubly stochastic remainder with no permutation in its support (Birkhoff fails)"
        c = min(R[i][p[i]] for i in range(n))
        for i in range(n): R[i][p[i]] -= c
        out.append((c, p))
    return out

def rebuild(n, dec):
    M = [[Fr(0)] * n for _ in range(n)]
    for c, p in dec:
        for i in range(n): M[i][p[i]] += c
    return M

def line_sum_tables(n, q):
    # every n x n matrix of nonnegative integers with every row and column summing to q
    rows = [r for r in itertools.product(range(q + 1), repeat=n) if sum(r) == q]
    def rec(prefix, colrem):
        if len(prefix) == n - 1:
            if all(0 <= c <= q for c in colrem) and sum(colrem) == q: yield prefix + [tuple(colrem)]
            return
        for r in rows:
            if all(a <= b for a, b in zip(r, colrem)): yield from rec(prefix + [r], [b - a for a, b in zip(r, colrem)])
    yield from rec([], [q] * n)

def random_table(rng, n, q):
    # a random line-sum-q table, filled cell by cell inside the Frechet bounds (no permutations used)
    T = [[0] * n for _ in range(n)]; crem = [q] * n
    for i in range(n - 1):
        rrem = q
        for j in range(n - 1):
            lo = max(0, rrem - sum(crem[j + 1:])); hi = min(rrem, crem[j])
            T[i][j] = rng.randint(lo, hi); rrem -= T[i][j]; crem[j] -= T[i][j]
        assert rrem <= crem[n - 1]; T[i][n - 1] = rrem; crem[n - 1] -= rrem
    T[n - 1] = list(crem)
    return T

def check_birkhoff(n, T, q):
    A = [[Fr(v, q) for v in row] for row in T]
    assert all(sum(r) == 1 for r in A) and all(sum(A[i][j] for i in range(n)) == 1 for j in range(n))
    dec = birkhoff(A)
    assert rebuild(n, dec) == A, "the decomposition does not rebuild the matrix"
    assert all(c > 0 for c, _ in dec) and sum(c for c, _ in dec) == 1
    assert len(dec) <= n * n - n + 1   # greedy: each step zeros at least one entry, the last step zeros n
    return len(dec)

def main():
    t0 = time.time(); states = 0; res = {}
    # sanity: the double description method agrees with brute force on n = 2 polytopes
    perms2 = list(itertools.product(itertools.permutations(range(2)), repeat=2))
    for pa in perms2:
        for pb in perms2:
            ra, rb = L.ranks(pa), L.ranks(pb)
            extra = degree_cons(2, 1) + stab_cons(2, ra, rb)
            cons, V = vertices_dd(4, extra)
            assert V == vertices_brute(4, cons), "double description and brute force disagree"
    for k in (1, Fr(3, 2), 2):
        cons, V = vertices_dd(4, degree_cons(2, k))
        assert V == vertices_brute(4, cons), "double description and brute force disagree (b-matching)"
    print("double description = brute force on every n=2 stable polytope (16) and the n=2 b-matching polytopes k=1, 3/2, 2")

    # 1. stable polytope, k = 1, every profile, n = 2 and 3
    for n in (2, 3):
        d = n * n
        base = vertices_dd(d, degree_cons(n, 1))      # the matching polytope, cut once for all profiles
        assert sorted(base[1]) == sorted(point(n, m) for m in L.matchings(n, 1)), "matching polytope is not the matchings"
        prof = 0; hist = {}
        for idx, (pa, pb) in enumerate(L.profiles(n)):
            if n == 3 and idx % SAMPLE: continue
            ra, rb = L.ranks(pa), L.ranks(pb); prof += 1
            cons, V = vertices_dd(d, stab_cons(n, ra, rb), start=base); states += len(V)
            assert all(integral(x) for x in V), f"a fractional vertex of the stable polytope: {pa} {pb}"
            want = sorted(point(n, m) for m in L.matchings(n, 1) if L.stable(n, 1, ra, rb, m))
            assert V == want, "stable polytope vertices differ from the brute-force stable matchings"
            hist[len(V)] = hist.get(len(V), 0) + 1
        res[f"stable_n{n}"] = {"profiles": prof, "vertices_histogram": dict(sorted(hist.items())),
                               "vertices_total": sum(c * v for c, v in hist.items())}
        print(f"stable polytope k=1 n={n}: {prof} profiles, every vertex integral, vertices = stable matchings;"
              f" vertex count per profile: {dict(sorted(hist.items()))}, total {res[f'stable_n{n}']['vertices_total']}")

    # 2a. the direct k-version of stability is not exact at k = 2
    for n in (2, 3):
        M2 = L.matchings(n, 2); prof = differ = extra_pts = 0; example = None
        for idx, (pa, pb) in enumerate(L.profiles(n)):
            if n == 3 and idx % SAMPLE: continue
            ra, rb = L.ranks(pa), L.ranks(pb); prof += 1
            sc = stab_cons(n, ra, rb, 2); bad = []
            for m in M2:
                x = point(n, m); ok = all(val(c, x) >= 0 for c in sc); st = L.stable(n, 2, ra, rb, m); states += 1
                if st: assert ok, "a stable matching breaks the k-stability inequality"
                if ok and not st: bad.append(m)
            if bad:
                differ += 1; extra_pts += len(bad)
                if example is None: example = {"pa": [list(r) for r in pa], "pb": [list(r) for r in pb], "unstable": sorted(bad[0])}
        res[f"naive_k2_n{n}"] = {"profiles": prof, "profiles_with_unstable_points": differ, "unstable_points": extra_pts, "example": example}
        print(f"k=2 n={n}: the direct k-stability inequality admits unstable 0/1 points on {differ} of {prof} profiles"
              f" ({extra_pts} points); first: {example}")
    assert res["naive_k2_n3"]["profiles_with_unstable_points"] > 0

    # 2b. plain b-matching polytope with rational capacity
    bm = {}
    for n in (2, 3):
        for k in (1, Fr(3, 2), 2):
            cons, V = vertices_dd(n * n, degree_cons(n, k)); states += len(V)
            frac = [x for x in V if not integral(x)]
            if k in (1, 2):
                assert not frac and sorted(V) == sorted(point(n, m) for m in L.matchings(n, int(k))), "integer k is not the 0/1 model"
            bm[(n, str(k))] = (len(V), len(frac), frac)
            print(f"b-matching polytope n={n} k={k}: {len(V)} vertices, {len(frac)} fractional")
    assert bm[(2, "3/2")][1] > 0 and bm[(3, "3/2")][1] > 0, "k=3/2 should have fractional vertices"
    print("n=2 k=3/2 fractional vertices:", [show(2, x) for x in bm[(2, "3/2")][2]])

    # 3. Birkhoff-von Neumann, exact
    bv = {}
    for n, qs in ((3, range(1, 7)), (4, range(1, 4))):
        for q in qs:
            cnt = mx = 0
            for T in line_sum_tables(n, q):
                mx = max(mx, check_birkhoff(n, T, q)); cnt += 1; states += 1
            if n == 3: assert cnt == (q + 1) * (q + 2) * (q * q + 3 * q + 4) // 8, "3x3 count off MacMahon's formula"
            bv[f"{n}x{n} q={q}"] = (cnt, mx)
    rng = random.Random(20261125); mx5 = 0
    for _ in range(200):
        mx5 = max(mx5, check_birkhoff(5, random_table(rng, 5, 7), 7)); states += 1
    bv["5x5 q=7 sample"] = (200, mx5)
    for key, (c, m) in bv.items(): print(f"Birkhoff {key}: {c} matrices decomposed exactly, at most {m} permutations")

    fp = [
        {"name": "stable polytope k=1 vertices summed, n=2 all profiles, n=3 sample (every 97th)", "seq": [res["stable_n2"]["vertices_total"], res["stable_n3"]["vertices_total"]]},
        {"name": "profiles where direct k=2 stability admits unstable points, n=2..3", "seq": [res["naive_k2_n2"]["profiles_with_unstable_points"], res["naive_k2_n3"]["profiles_with_unstable_points"]]},
        {"name": "b-matching polytope vertices k=1, n=2..3", "seq": [bm[(2, "1")][0], bm[(3, "1")][0]]},
        {"name": "b-matching polytope vertices k=3/2, n=2..3", "seq": [bm[(2, "3/2")][0], bm[(3, "3/2")][0]]},
        {"name": "b-matching polytope fractional vertices k=3/2, n=2..3", "seq": [bm[(2, "3/2")][1], bm[(3, "3/2")][1]]},
        {"name": "b-matching polytope vertices k=2, n=2..3", "seq": [bm[(2, "2")][0], bm[(3, "2")][0]]},
        {"name": "3x3 doubly stochastic matrices in (1/q)Z, q=1..6", "seq": [bv[f"3x3 q={q}"][0] for q in range(1, 7)]},
        {"name": "4x4 doubly stochastic matrices in (1/q)Z, q=1..3", "seq": [bv[f"4x4 q={q}"][0] for q in range(1, 4)]},
    ]
    for e in fp: e["runner"] = "python3 -I culture/love/field.py"
    with open(os.path.join(HERE, "field_fingerprints.json"), "w", encoding="utf-8") as f:
        f.write("[\n" + ",\n".join(" " + json.dumps(e) for e in fp) + "\n]\n")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2),
                      "stable": {k: v for k, v in res.items() if k.startswith("stable")},
                      "direct_k2": {k: {x: y for x, y in v.items() if x != "example"} for k, v in res.items() if k.startswith("naive")},
                      "b_matching": {f"n{n}_k{k}": {"vertices": v[0], "fractional": v[1]} for (n, k), v in bm.items()},
                      "birkhoff": {k: {"matrices": c, "max_terms": m} for k, (c, m) in bv.items()}}))

if __name__ == "__main__":
    main()
