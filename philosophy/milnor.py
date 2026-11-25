#!/usr/bin/env python3
"""Milnor's link-homotopy invariants of polygonal links, in exact integer arithmetic.

Why it is here: Lacan models the psychic structure as the Borromean knot (three rings, no two linked, all three
inseparable) and its repair as a fourth ring. Those are statements about links, so they can be computed.
See PSYCHOSIS.md for the reading and its limits.

Method 1 (Milnor, "Link groups", Annals of Math. 59, 1954; "Isotopy of links", 1957). A link is a list of closed
polygons with integer vertices. An integer matrix of positive determinant turns it into a diagram (first two
coordinates; the third is height). From the diagram: the Wirtinger arcs, each component's longitude as a word in the
arcs, and the Magnus expansion of that word (x_i -> 1 + X_i) truncated at degree 3. The coefficient of X_i in the
longitude of j is the linking number lk(i, j); of X_i X_j in the longitude of k it is mu(ijk); of X_i X_j X_k in the
longitude of l it is mu(ijkl). Each is an invariant once the shorter ones vanish. Signs depend on orientations.

Method 2, independent of the first (Mellor and Melvin, Algebraic & Geometric Topology 3, 2003): mu(123) = m - t,
where t counts the triple points of three Seifert surfaces with sign and m counts ordered pairs of piercings.
Used here for three flat convex rings, with the flat discs as the surfaces.

Every step after the vertices are fixed is integer or rational arithmetic: there is no tolerance anywhere.
Run: python3 -I philosophy/milnor.py        (prints a table; last line is JSON for the board runner)
"""
import bisect, itertools, json, math, random, sys, time
from fractions import Fraction

SC = 1000                                   # vertices are rounded to 1/1000 and kept as integers
AX = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
D = 3                                       # Magnus expansions are truncated at this degree

# ------------------------------------------------------------------ the links

def ring(e1, a1, e2, a2, n=96, at=(0, 0, 0)):
    """Flat ellipse a1 cos(t) e1 + a2 sin(t) e2 + at. Half-step sampling: no vertex lies on a coordinate plane."""
    return [tuple(round(SC * (at[k] + a1 * math.cos(t) * e1[k] + a2 * math.sin(t) * e2[k])) for k in range(3))
            for t in (2 * math.pi * (i + .5) / n for i in range(n))]

def borromean():
    """R in z = 0, S in x = 0, I in y = 0; each ellipse's long axis is the next one's short axis."""
    return [ring(AX[0], 1, AX[1], 2), ring(AX[1], 1, AX[2], 2), ring(AX[2], 1, AX[0], 2)]

def unlink3():
    return [ring(AX[0], 1, AX[1], 2, at=(-6, 0, 0)), ring(AX[1], 1, AX[2], 2), ring(AX[2], 1, AX[0], 2, at=(6, 0, 0))]

def hopf():
    return [ring(AX[0], 1, AX[1], 1), ring(AX[0], 1, AX[2], 1, at=(1, 0, 0))]

def bing_double(e1, a1, e2, a2, r=0.2, delta=0.35, m=40):
    """Two clasped rings in the tube around a flat ellipse (Bing doubling). Ring A lies in the ellipse's plane and
    covers angles [-delta, pi + delta]; ring B stands across the plane and covers [pi - delta, 2 pi + delta].
    They hook each other at both ends, with linking number 0."""
    e3 = tuple(e1[(k + 1) % 3] * e2[(k + 2) % 3] - e1[(k + 2) % 3] * e2[(k + 1) % 3] for k in range(3))
    def point(th, u, v):
        c, s = math.cos(th), math.sin(th); nx, ny = c / a1, s / a2; L = math.hypot(nx, ny)
        return tuple(round(SC * (a1 * c * e1[k] + a2 * s * e2[k] + u * (nx * e1[k] + ny * e2[k]) / L + v * e3[k])) for k in range(3))
    def loop(t0, t1, u, v):
        ts = [t0 + (t1 - t0) * i / m for i in range(m + 1)]
        return [point(t, u, v) for t in ts] + [point(t, -u, -v) for t in reversed(ts)]
    return loop(-delta, math.pi + delta, r, 0.0), loop(math.pi - delta, 2 * math.pi + delta, 0.0, r)

def four_rings():
    """R, S, and the third Borromean ring replaced by its two Bing-double rings, named I and Sigma."""
    R, S, _ = borromean()
    return [R, S, *bing_double(AX[2], 1, AX[0], 2)]

def trefoil(n=150):
    return [[tuple(round(SC * x) for x in (math.sin(t) + 2 * math.sin(2 * t), math.cos(t) - 2 * math.cos(2 * t), -math.sin(3 * t)))
             for t in (2 * math.pi * i / n for i in range(n))]]

def kinked_unknot(n=120):
    return [[tuple(round(SC * x) for x in (math.cos(t), math.sin(2 * t), 0.5 * math.sin(t))) for t in (2 * math.pi * (i + .5) / n for i in range(n))]]

def mirror(link): return [[(x, y, -z) for x, y, z in comp] for comp in link]
def reverse(link, c): return [comp[::-1] if i == c else comp for i, comp in enumerate(link)]

# ------------------------------------------------------------------ the diagram

class Degenerate(Exception): pass

def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))

def views(seed, count):
    """Integer matrices of positive determinant. A linear map of positive determinant does not change the link."""
    rng = random.Random(seed); out = []
    while len(out) < count:
        M = [[rng.randint(-9, 9) for _ in range(3)] for _ in range(3)]
        if det3(M) > 0: out.append(M)
    return out

def diagram(link, M):
    """Crossings of the image of the link under M, as (over, under, sign). `over` and `under` are (component,
    position), position = segment index + exact fraction along the segment. Raises Degenerate if the view is not
    generic, ValueError if two segments of the link meet in space."""
    assert det3(M) > 0
    P = [[tuple(M[r][0] * p[0] + M[r][1] * p[1] + M[r][2] * p[2] for r in range(3)) for p in comp] for comp in link]
    segs = []
    for c, comp in enumerate(P):
        for i in range(len(comp)):
            p, q = comp[i], comp[(i + 1) % len(comp)]
            segs.append((c, i, p, q, min(p[0], q[0]), max(p[0], q[0]), min(p[1], q[1]), max(p[1], q[1])))
    X = []
    for a in range(len(segs)):
        ca, ia, p1, p2, ax0, ax1, ay0, ay1 = segs[a]
        dx1, dy1 = p2[0] - p1[0], p2[1] - p1[1]
        for b in range(a + 1, len(segs)):
            cb, ib, q1, q2, bx0, bx1, by0, by1 = segs[b]
            if ax1 < bx0 or bx1 < ax0 or ay1 < by0 or by1 < ay0: continue
            if ca == cb and (ib - ia == 1 or (ia == 0 and ib == len(P[ca]) - 1)): continue      # neighbours share a vertex
            dx2, dy2 = q2[0] - q1[0], q2[1] - q1[1]
            wx, wy = q1[0] - p1[0], q1[1] - p1[1]
            den = dx1 * dy2 - dy1 * dx2; ns = wx * dy2 - wy * dx2; nt = wx * dy1 - wy * dx1
            if den == 0:
                if ns == 0: raise Degenerate("two segments on one line")
                continue
            sign = 1
            if den < 0: den, ns, nt, sign = -den, -ns, -nt, -1
            if not (0 <= ns < den and 0 <= nt < den): continue
            if ns == 0 or nt == 0: raise Degenerate("a crossing at a vertex")
            ha = p1[2] * den + ns * (p2[2] - p1[2]); hb = q1[2] * den + nt * (q2[2] - q1[2])      # heights, times den
            if ha == hb: raise ValueError("the polygons intersect")
            pa, pb = (ca, ia + Fraction(ns, den)), (cb, ib + Fraction(nt, den))
            X.append((pa, pb, sign) if ha > hb else (pb, pa, -sign))
    return X

def flip(X, k):
    """Change crossing k: the strand that went over now goes under."""
    o, u, s = X[k]
    return X[:k] + [(u, o, -s)] + X[k + 1:]

# ------------------------------------------------------------------ method 1: Wirtinger arcs and Magnus expansion

def mul(a, b):
    out = {}
    for wa, ca in a.items():
        for wb, cb in b.items():
            if len(wa) + len(wb) <= D:
                w = wa + wb; v = out.get(w, 0) + ca * cb
                if v: out[w] = v
                else: out.pop(w, None)
    return out

def inv(a):
    """Inverse of a series with constant term 1: the sum of (1 - a)^k."""
    u = {w: -c for w, c in a.items() if w}; out = {(): 1}; p = {(): 1}
    for _ in range(D):
        p = mul(p, u)
        for w, c in p.items():
            v = out.get(w, 0) + c
            if v: out[w] = v
            else: out.pop(w, None)
    return out

def longitudes(X, ncomp):
    """Magnus expansion of each component's longitude, truncated at degree D.
    Walking along component c, the arc after passing under an arc g at a crossing of sign s is g^-s a g^s. So the
    k-th arc is w^-1 x_c w with w the product of the g^s met so far, and the longitude is the full product.
    The arcs are found by iterating from the degree-1 values; each pass makes them exact one degree higher."""
    under = [sorted((u[1], o, s) for o, u, s in X if u[0] == c) for c in range(ncomp)]
    cuts = [[p for p, _, _ in under[c]] for c in range(ncomp)]
    def arc(c, pos): return (c, bisect.bisect_left(cuts[c], pos) % max(len(cuts[c]), 1))
    base = [{(): 1, (c,): 1} for c in range(ncomp)]
    arcs = {(c, k): base[c] for c in range(ncomp) for k in range(max(len(cuts[c]), 1))}
    for _ in range(D + 2):
        new, lon = {}, []
        for c in range(ncomp):
            w = {(): 1}; new[(c, 0)] = base[c]
            for k, (_, o, s) in enumerate(under[c], start=1):
                g = arcs[arc(*o)]
                w = mul(w, g if s > 0 else inv(g))
                if k < len(under[c]): new[(c, k)] = mul(mul(inv(w), base[c]), w)
            lon.append(w)
        if new == arcs: return lon
        arcs = new
    raise AssertionError("the arcs did not settle")

def mu(lon, *idx): return lon[idx[-1]].get(tuple(idx[:-1]), 0)

def lk_by_count(X, i, j):
    """Linking number counted directly from the crossings, two ways; they must agree."""
    a = sum(s for o, u, s in X if o[0] == i and u[0] == j); b = sum(s for o, u, s in X if o[0] == j and u[0] == i)
    assert a == b, "crossing counts disagree: the diagram is wrong"
    return a

def invariants(X, ncomp):
    """All lk, mu(ijk), mu(ijkl) with distinct indices. Asserts the counted lk equals the Magnus coefficient."""
    lon = longitudes(X, ncomp); out = {}
    for r in (2, 3, 4):
        for idx in itertools.permutations(range(ncomp), r):
            out[idx] = mu(lon, *idx)
    for i, j in itertools.permutations(range(ncomp), 2): assert out[(i, j)] == lk_by_count(X, i, j)
    return out

def over_views(link, seed=1, count=4):
    """The invariants in several views. Skips views that are not generic. Returns the list of results."""
    res = []
    for M in views(seed, 3 * count):
        try: res.append((invariants(diagram(link, M), len(link)), M))
        except Degenerate: continue
        if len(res) == count: return res
    raise AssertionError("too few generic views")

def fox3(X):
    """Number of Fox 3-colourings of a knot diagram: 3 for an unknot, 9 for a trefoil."""
    under = sorted((u[1], o[1]) for o, u, s in X); m = len(under)
    if m == 0: return 3
    cuts = [p for p, _ in under]; rows = []
    for k, (_, opos) in enumerate(under):
        row = [0] * m
        row[bisect.bisect_left(cuts, opos) % m] += 2; row[k] -= 1; row[(k + 1) % m] -= 1
        rows.append([x % 3 for x in row])
    rank = 0
    for col in range(m):
        piv = next((r for r in range(rank, m) if rows[r][col]), None)
        if piv is None: continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        f = rows[rank][col]; rows[rank] = [(x * f) % 3 for x in rows[rank]]      # f is 1 or 2, its own inverse mod 3
        for r in range(m):
            if r != rank and rows[r][col]:
                g = rows[r][col]; rows[r] = [(x - g * y) % 3 for x, y in zip(rows[r], rows[rank])]
        rank += 1
    return 3 ** (m - rank)

# ------------------------------------------------------------------ method 2: Seifert discs

def seifert_triple(rings):
    """mu(123) = m - t for three flat convex rings, each in a plane across a different coordinate axis.
    Returns (m - t, m, t, the three words). A word lists, in order along a ring, which discs it pierces and how."""
    info = []
    for ring_ in rings:
        ax = next(k for k in range(3) if len({p[k] for p in ring_}) == 1)
        u, v = (ax + 1) % 3, (ax + 2) % 3; n = len(ring_)
        turn = [(ring_[(i + 1) % n][u] - ring_[i][u]) * (ring_[(i + 2) % n][v] - ring_[(i + 1) % n][v])
                - (ring_[(i + 1) % n][v] - ring_[i][v]) * (ring_[(i + 2) % n][u] - ring_[(i + 1) % n][u]) for i in range(n)]
        assert all(t > 0 for t in turn) or all(t < 0 for t in turn), "ring is not convex"
        info.append((ax, ring_[0][ax], 1 if turn[0] > 0 else -1, u, v))
    def inside(i, pu, pv):
        ax, c, orient, u, v = info[i]; r = rings[i]; n = len(r)
        return all(orient * ((r[(k + 1) % n][u] - r[k][u]) * (pv - r[k][v]) - (r[(k + 1) % n][v] - r[k][v]) * (pu - r[k][u])) > 0 for k in range(n))
    words = []
    for j, rj in enumerate(rings):
        hits = []
        for k in range(len(rj)):
            a, b = rj[k], rj[(k + 1) % len(rj)]
            for i in range(3):
                if i == j: continue
                ax, c, orient, u, v = info[i]
                assert a[ax] != c, "a vertex lies on a disc's plane"
                if (a[ax] - c) * (b[ax] - c) < 0:
                    t = Fraction(c - a[ax], b[ax] - a[ax])
                    if inside(i, a[u] + t * (b[u] - a[u]), a[v] + t * (b[v] - a[v])):
                        hits.append((k + t, i, orient * (1 if b[ax] > a[ax] else -1)))
        words.append([(i, s) for _, i, s in sorted(hits)])
    def e(w, a, b): return sum(s1 * s2 for p, (i1, s1) in enumerate(w) for i2, s2 in w[p + 1:] if i1 == a and i2 == b)
    m = e(words[0], 1, 2) + e(words[1], 2, 0) + e(words[2], 0, 1)
    t = 0
    axes = [x[0] for x in info]
    if sorted(axes) == [0, 1, 2]:
        pt = [None] * 3
        for ax, c, _, _, _ in info: pt[ax] = c
        if all(inside(i, pt[info[i][3]], pt[info[i][4]]) for i in range(3)):
            perm = 1 if tuple(axes) in ((0, 1, 2), (1, 2, 0), (2, 0, 1)) else -1
            t = perm * info[0][2] * info[1][2] * info[2][2]
    for i, j in itertools.permutations(range(3), 2):
        assert sum(s for k, s in words[j] if k == i) == 0, "a pair has nonzero linking number"
    return m - t, m, t, words

# ------------------------------------------------------------------ the checks

def main():
    t0 = time.time(); checks = 0; N = "RSI"
    def same(results, keys):
        vals = {tuple(r[k] for k in keys) for r, _ in results}
        assert len(vals) == 1, f"views disagree: {vals}"
        return dict(zip(keys, next(iter(vals))))

    # 1. The Borromean rings: no two linked, all three inseparable.
    B = borromean(); res = over_views(B); checks += len(res)
    pairs = list(itertools.permutations(range(3), 2)); triples = list(itertools.permutations(range(3), 3))
    v = same(res, pairs + triples)
    assert all(v[p] == 0 for p in pairs)
    m123 = v[(0, 1, 2)]
    assert abs(m123) == 1 and v[(1, 2, 0)] == v[(2, 0, 1)] == m123 and v[(1, 0, 2)] == v[(0, 2, 1)] == v[(2, 1, 0)] == -m123
    print(f"Borromean rings, {len(res)} views: every lk = 0; mu(RSI) = mu(SIR) = mu(IRS) = {m123:+d}; mu(SRI) = {-m123:+d}")
    vm = same(over_views(mirror(B)), triples); assert vm[(0, 1, 2)] == m123        # length 3: unchanged by a mirror
    vr = same(over_views(reverse(B, 0)), triples); assert vr[(0, 1, 2)] == -m123
    print(f"  mirror image: mu = {vm[(0, 1, 2)]:+d} (unchanged: a mirror multiplies an invariant of length r by (-1)^(r-1)); one ring reversed: mu = {vr[(0, 1, 2)]:+d}")
    checks += 8

    # 2. The same number by the second method.
    s, m, t, words = seifert_triple(B); sm = seifert_triple(mirror(B))[0]; su = seifert_triple(unlink3())
    assert s == m123 and m == 0 and sm == s and su[0] == 0 and su[2] == 0
    assert all(len({i for i, _ in w}) == 1 and len(w) == 2 for w in words)
    print(f"  Seifert discs: one triple point (t = {t:+d}), each ring pierces exactly one other disc twice (m = 0): mu = m - t = {s:+d}; mirror {sm:+d}")
    checks += 3

    # 3. Controls.
    vu = same(over_views(unlink3()), pairs + triples); assert not any(vu.values())
    vh = same(over_views(hopf()), [(0, 1)]); vhm = same(over_views(mirror(hopf())), [(0, 1)])
    assert abs(vh[(0, 1)]) == 1 and vhm[(0, 1)] == -vh[(0, 1)]
    print(f"Controls: three separate rings, every invariant 0; Hopf link, lk = {vh[(0, 1)]:+d}, its mirror image {vhm[(0, 1)]:+d}")
    checks += 8

    # 4. Cut one ring: the two that remain have lk = 0, so they come apart (up to link homotopy).
    for c in range(3):
        two = [B[i] for i in range(3) if i != c]; assert same(over_views(two, count=2), [(0, 1)])[(0, 1)] == 0
    print("Cut any one ring: the other two have lk = 0")
    checks += 6

    # 5. One wrong crossing between R and S (Lacan's 'error' in the knot).
    flips = 0
    for inv_, M in res:
        X = diagram(B, M)
        for k, (o, u, _) in enumerate(X):
            if {o[0], u[0]} == {0, 1}:
                w = invariants(flip(X, k), 3)
                assert abs(w[(0, 1)]) == 1 and w[(0, 2)] == 0 and w[(1, 2)] == 0
                flips += 1
    print(f"One wrong crossing between R and S ({flips} cases, every R-S crossing in every view): lk(R,S) = +-1, lk(R,I) = lk(S,I) = 0")
    checks += flips

    # 6. Four rings: the three alone fall apart, the fourth holds them.
    F = four_rings(); names = ["R", "S", "I", "Sigma"]; res4 = over_views(F, count=3); checks += len(res4)
    p4 = list(itertools.permutations(range(4), 2)); t4 = list(itertools.permutations(range(4), 3)); q4 = list(itertools.permutations(range(4), 4))
    v4 = same(res4, p4 + t4 + q4)
    assert all(v4[k] == 0 for k in p4 + t4), "a pair or triple of the four rings is linked"
    for a, b, c, d in q4:
        assert v4[(a, b, c, d)] + v4[(b, a, c, d)] + v4[(b, c, a, d)] == 0, "shuffle relation fails"
        assert v4[(a, b, c, d)] == v4[(b, c, d, a)], "cyclic symmetry fails"
    assert any(abs(x) == 1 for x in (v4[k] for k in q4)) and all(abs(v4[k]) <= 1 for k in q4)
    for c in range(4):
        three = [F[i] for i in range(4) if i != c]
        w = same(over_views(three, count=2), pairs + triples); assert not any(w.values()); checks += 2
    v4m = same(over_views(mirror(F), count=2), q4); assert all(v4m[k] == -v4[k] for k in q4); checks += 2     # length 4: a mirror flips the sign
    last = {"".join(names[i][0] for i in k[:3]): v4[k] for k in q4 if k[3] == 3}
    print(f"Four rings (R, S, I, Sigma), {len(res4)} views: every lk = 0 and every mu(ijk) = 0, also in each three-ring sublink computed alone")
    print(f"  mu(abc Sigma) for abc in every order: {last}")
    print("  so: remove any one ring and the other three come apart (up to link homotopy); all four cannot")

    # 7. One ring that is knotted (the trefoil), against a kinked plain ring.
    def colourings(link):
        vals = set()
        for M in views(7, 12):
            try: vals.add(fox3(diagram(link, M)))
            except Degenerate: continue
        assert len(vals) == 1, vals
        return vals.pop()
    ct, cu = colourings(trefoil()), colourings(kinked_unknot()); assert (ct, cu) == (9, 3)
    print(f"Trefoil: {ct} Fox 3-colourings; kinked plain ring: {cu}. The trefoil is knotted.")
    checks += 2

    print("PASS")
    print(json.dumps({"states": checks, "seconds": round(time.time() - t0, 2)}))

if __name__ == "__main__":
    main()
