#!/usr/bin/env python3
"""DNA topology, the lowest level of brain/: closed DNA carries linking numbers, and enzymes change them.

What is checked (every vertex of every curve below is an integer point; no tolerance outside section 7):
  1. Ribbons. A closed ribbon with n full right-handed twists, built as two integer polygons, has linking number n.
     With curls added (places where the ribbon's axis crosses over itself), Lk = twists + curls. This is the diagram
     form of Lk = Tw + Wr (Calugareanu 1961, White 1969, Fuller 1971).
  2. Strand passages. One passage between two different closed curves changes their linking number by exactly 1
     (type I topoisomerase on the two strands of a duplex). A duplex passed through a duplex changes Lk by exactly 2
     (type II). The crossing flip on a diagram is shown to be a real passage: the polygons with the bridge moved
     through give exactly the flipped diagram.
  3. Replication catenanes. The (2,2k) torus link, built on a round torus from integer points and again as the two
     edges of a k-twist ribbon, has linking number k. Every set of j passages on its 2k-crossing diagram leaves the
     (2,2(k-j)) torus link, so k passages are needed and k suffice.
  4. Kinetoplast chainmail. Rings on a honeycomb patch, each hooked once to each neighbour: the matrix of linking
     numbers is the adjacency matrix. No ring is critical. The catenated oligomers set free by cutting rings at
     random are the lattice animals of the pattern; they are counted, with their perimeters, for valence 3, 4 and 6.
  5. Borromean rings and knots. The Borromean rings (philosophy/milnor.py) need crossings of both signs, three and
     three. The twist knots with 1 to 6 half twists are 3_1, 4_1, 5_2, 6_1, 7_2, 8_1 by their Alexander polynomials,
     and one strand passage at the clasp unties each of them.
  6. Arithmetic on cited numbers (base pairs per turn, genome sizes).
  7. Tested, in floating point: the Gauss integral against the exact linking numbers, and Lk = Tw + Wr itself on
     ribbons whose axis is not planar and whose writhe is not a whole number.

Methods, all exact unless marked:
  a. crossing count in a diagram, both ways (philosophy/milnor.py: diagram, lk_by_count);
  b. the coefficient of the Magnus expansion of a longitude (philosophy/milnor.py: invariants);
  c. the cone: the curve A bounds the cone over A from a far point, and lk(A, B) is the signed number of times B
     goes through that cone (written here, independent of a and b);
  d. elementary triangle moves: a vertex is removed when the triangle it spans with its two neighbours is not
     touched by anything else. Reducing a curve to a triangle proves it is unknotted; reducing two curves to two
     triangles proves they are a Hopf link (lk = +-1) or can be pulled apart (lk = 0);
  e. the Alexander polynomial from the Wirtinger presentation, by exact integer determinants and interpolation.

Run from the repository root:  python3 -I brain/dna/check.py     (last line is JSON for the board runner)
"""
import bisect, functools, itertools, json, math, os, sys, time
from collections import defaultdict
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'philosophy'))
import milnor

TOP = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]                 # the view from above: project along z
STATES = [0]                                            # exact cases checked

def tick(n=1): STATES[0] += n

# ------------------------------------------------------------------ exact geometry

def sub(a, b): return (a[0] - b[0], a[1] - b[1], a[2] - b[2])
def dot(a, b): return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
def cross(a, b): return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])

class NotGeneric(Exception): pass

def pierce(p, q, a, b, c):
    """+1 if the segment pq goes through the triangle abc along its normal (b-a)x(c-a), -1 if against, 0 if it
    misses. Raises NotGeneric if it touches the triangle without going cleanly through its inside."""
    n = cross(sub(b, a), sub(c, a))
    sp, sq = dot(n, sub(p, a)), dot(n, sub(q, a))
    if sp == 0 or sq == 0:                               # an end lies in the triangle's plane: fine if it is off the triangle
        if seg_hits_tri(p, q, a, b, c): raise NotGeneric
        return 0
    if (sp > 0) == (sq > 0): return 0
    D = sp - sq                                          # the meeting point is X / D
    X = tuple(q[k] * sp - p[k] * sq for k in range(3))
    ws = [dot(n, cross(sub(e1, e0), tuple(X[k] - D * e0[k] for k in range(3)))) for e0, e1 in ((a, b), (b, c), (c, a))]
    if any(w != 0 and (w > 0) != (D > 0) for w in ws): return 0          # strictly outside one edge: a miss
    if any(w == 0 for w in ws): raise NotGeneric                           # on the border
    return 1 if sq > sp else -1

APEXES = [(1000003, 700001, 1300021), (-900007, 1100009, 800011), (600011, -1200007, 1000033)]

def lk_cone(A, B):
    """Method c. The cone over A from a far point is a surface with boundary A. Count how B goes through it."""
    for apex in APEXES:
        try:
            return sum(pierce(B[j], B[(j + 1) % len(B)], apex, A[i], A[(i + 1) % len(A)])
                       for i in range(len(A)) for j in range(len(B)))
        except NotGeneric: continue
    raise AssertionError("no generic apex")

def orient2(a, b, c): return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])

def seg_seg_2d(p, q, a, b):
    d1, d2, d3, d4 = orient2(a, b, p), orient2(a, b, q), orient2(p, q, a), orient2(p, q, b)
    if ((d1 > 0 and d2 < 0) or (d1 < 0 and d2 > 0)) and ((d3 > 0 and d4 < 0) or (d3 < 0 and d4 > 0)): return True
    def on(u, v, w): return min(u[0], v[0]) <= w[0] <= max(u[0], v[0]) and min(u[1], v[1]) <= w[1] <= max(u[1], v[1])
    return (d1 == 0 and on(a, b, p)) or (d2 == 0 and on(a, b, q)) or (d3 == 0 and on(p, q, a)) or (d4 == 0 and on(p, q, b))

def in_tri_2d(p, a, b, c):
    s = [orient2(a, b, p), orient2(b, c, p), orient2(c, a, p)]
    return all(x >= 0 for x in s) or all(x <= 0 for x in s)

def seg_hits_tri(p, q, a, b, c):
    """True if the closed segment pq meets the closed triangle abc."""
    n = cross(sub(b, a), sub(c, a))
    sp, sq = dot(n, sub(p, a)), dot(n, sub(q, a))
    if (sp > 0 and sq > 0) or (sp < 0 and sq < 0): return False
    if sp == 0 and sq == 0:                              # in the triangle's plane: decide in two dimensions
        k = max(range(3), key=lambda i: abs(n[i])); u, v = [i for i in range(3) if i != k]
        P, Q, A, B, C = [(w[u], w[v]) for w in (p, q, a, b, c)]
        return in_tri_2d(P, A, B, C) or in_tri_2d(Q, A, B, C) or any(seg_seg_2d(P, Q, e, f) for e, f in ((A, B), (B, C), (C, A)))
    D = sp - sq
    X = tuple(q[k] * sp - p[k] * sq for k in range(3))
    for e0, e1 in ((a, b), (b, c), (c, a)):
        w = dot(n, cross(sub(e1, e0), tuple(X[k] - D * e0[k] for k in range(3))))
        if w != 0 and (w > 0) != (D > 0): return False
    return True

def leaves_cone(apex, e1, e2, other, n):
    """The segment from `apex` to `other` shares only `apex` with the triangle (apex, e1, e2)."""
    if dot(n, sub(other, apex)) != 0: return True        # it leaves the triangle's plane at once
    k = max(range(3), key=lambda i: abs(n[i])); u, v = [i for i in range(3) if i != k]
    d, f1, f2 = [(w[u] - apex[u], w[v] - apex[v]) for w in (other, e1, e2)]
    den = f1[0] * f2[1] - f1[1] * f2[0]; al = d[0] * f2[1] - d[1] * f2[0]; be = f1[0] * d[1] - f1[1] * d[0]
    if den < 0: al, be = -al, -be
    return not (al >= 0 and be >= 0)

def simplify(link):
    """Method d: elementary triangle moves until none applies. Returns the reduced polygons."""
    link = [list(c) for c in link]; changed = True
    while changed:
        changed = False
        for ci, comp in enumerate(link):
            i = 0
            while len(comp) > 3 and i < len(comp):
                m = len(comp); a, b, c = comp[i - 1], comp[i], comp[(i + 1) % m]
                n = cross(sub(b, a), sub(c, a)); ok = True
                if n == (0, 0, 0): ok = dot(sub(b, a), sub(c, b)) > 0          # b lies on the segment ac
                else:
                    ok = leaves_cone(a, b, c, comp[i - 2], n) and leaves_cone(c, a, b, comp[(i + 2) % m], n)
                    for cj, other in enumerate(link):
                        if not ok: break
                        for k in range(len(other)):
                            if cj == ci and (k - i) % m in (m - 2, m - 1, 0, 1): continue   # the four edges at a, b, c
                            if seg_hits_tri(other[k], other[(k + 1) % len(other)], a, b, c): ok = False; break
                if ok: del comp[i]; changed = True
                else: i += 1
    return link

# ------------------------------------------------------------------ diagrams

def lk_matrix(X, n):
    """Signed crossing counts: entry [i][j], i != j, is lk(i, j) counted where i goes over j; it must equal the count
    where j goes over i. Entry [i][i] is the signed number of self-crossings of i in this view."""
    M = [[0] * n for _ in range(n)]
    for o, u, s in X: M[o[0]][u[0]] += s
    for i in range(n):
        for j in range(i): assert M[i][j] == M[j][i], "crossing counts disagree"
    return M

def generic_views(link, count, seed=1):
    out = []
    for M in milnor.views(seed, 6 * count + 6):
        try: out.append((M, milnor.diagram(link, M)))
        except milnor.Degenerate: continue
        if len(out) == count: return out
    raise AssertionError("too few generic views")

def flip_set(X, S):
    return [(u, o, -s) if k in S else (o, u, s) for k, (o, u, s) in enumerate(X)]

def point(link, cp):
    """The point of the link at (component, position), exactly."""
    c, pos = cp; comp = link[c]; i = int(pos // 1); t = pos - i
    p, q = comp[i], comp[(i + 1) % len(comp)]
    return tuple(p[k] + t * (q[k] - p[k]) for k in range(3))

def det_int(M):
    """Determinant of an integer matrix, exactly (Bareiss)."""
    n = len(M); M = [r[:] for r in M]; sign, prev = 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            sw = next((i for i in range(k + 1, n) if M[i][k]), None)
            if sw is None: return 0
            M[k], M[sw] = M[sw], M[k]; sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n): M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[-1][-1] if n else 1

def alexander(X):
    """Method e. Alexander polynomial of a knot diagram: coefficients, lowest degree first, no factor t, leading
    coefficient positive. Row of a crossing of sign s with over arc g, incoming under arc a, outgoing b (Fox
    derivative of b = g^-s a g^s, every generator sent to t): s = +1: (t-1) g + a - t b; s = -1: (1-t) g + t a - b."""
    under = sorted((u[1], o[1], s) for o, u, s in X); m = len(under)
    if m < 2: return (1,)
    cuts = [p for p, _, _ in under]; rows = []
    for k, (_, opos, s) in enumerate(under):
        row = defaultdict(lambda: [0, 0]); g = bisect.bisect_left(cuts, opos) % m
        for col, (c0, c1) in ((g, (-s, s)), (k, (1, 0) if s > 0 else (0, 1)), ((k + 1) % m, (0, -1) if s > 0 else (-1, 0))):
            row[col][0] += c0; row[col][1] += c1
        rows.append(row)
    ts = list(range(-(m // 2), m - m // 2))              # m points fix a polynomial of degree at most m - 1
    vals = [Fraction(det_int([[rows[i][j][0] + rows[i][j][1] * t if j in rows[i] else 0 for j in range(m - 1)] for i in range(m - 1)])) for t in ts]
    coef = [Fraction(0)] * m                             # Newton interpolation, then expand
    dd = vals[:]
    for k in range(1, m):
        for i in range(m - 1, k - 1, -1): dd[i] = (dd[i] - dd[i - 1]) / (ts[i] - ts[i - k])
    basis = [Fraction(1)]
    for k in range(m):
        for d, c in enumerate(basis): coef[d] += dd[k] * c
        basis = [Fraction(0)] + basis
        for d in range(len(basis) - 1): basis[d] -= ts[k] * basis[d + 1]
    assert all(c.denominator == 1 for c in coef)
    co = [int(c) for c in coef]
    while co and co[-1] == 0: co.pop()
    while co and co[0] == 0: co.pop(0)
    assert co, "the Alexander polynomial vanished"
    if co[-1] < 0: co = [-c for c in co]
    assert co == co[::-1] and abs(sum(co)) == 1, "not the Alexander polynomial of a knot"
    return tuple(co)

def poly(co):
    """2t^2 - 3t + 2 from (2, -3, 2)."""
    out = []
    for d in range(len(co) - 1, -1, -1):
        c = co[d]
        if c == 0: continue
        mag = abs(c); term = (str(mag) if mag != 1 or d == 0 else "") + ("t" if d else "") + (f"^{d}" if d > 1 else "")
        out.append(("-" if c < 0 else "+") + term)
    s = "".join(out)
    return (s[1:] if s[0] == "+" else s).replace("+", " + ").replace("-", " - ").strip()

# ------------------------------------------------------------------ 1. ribbons, built from integer points

R5 = [(5, 0), (3, 4), (-3, 4), (-5, 0), (-3, -4), (3, -4)]        # six integer points on the circle of radius 5

def build(mods, clasp=None, L=4, r=5, a=12, h=6):
    """Two strands side by side, 2r apart, running along +x from x = 0, then back around a rectangle.
    mods: ('H', s) is a half twist of sign s (right-handed for s = +1): the strands turn half way around each other
    in three steps of R5. ('C', c) is a curl: the pair makes a loop and crosses itself, over for c = +1, under for
    c = -1. clasp None: the two strands close up (two rings, or one ring after an odd number of half twists).
    clasp +1, -1: the pair is cut and its two ends hook each other (a twist knot); clasp 0: the ends lie over each
    other without hooking. Returns (polygons, curls) with curls the list of (x, y) origins of the curl modules."""
    j = 0; x = 0; y0 = 0; curls = []
    if clasp is None: PA = [(0, r, 0)]; PB = [(0, -r, 0)]; g = 10
    else: PA = [(-12, 2, 0), (-3, 2, 0), (0, r, 0)]; PB = [(-12, -2, 0), (-3, -2, 0), (0, -r, 0)]; g = 30
    for kind, s in mods:
        if kind == 'H':
            for _ in range(3):
                x += L; j += s; c = R5[j % 6]
                PA.append((x, y0 + c[0], c[1])); PB.append((x, y0 - c[0], -c[1]))
        else:
            z = s * h; curls.append((x, y0))
            left = [(2 * a - r, r, 0), (2 * a - r, 2 * a - r, 0), (a + r, 2 * a - r, 0), (a + r, r + 4, 0), (a + r, r + 2, z),
                    (a + r, -r - 2, z), (a + r, -r - 4, 0), (a + r, -2 * a + r, 0), (3 * a, -2 * a + r, 0)]
            right = [(2 * a + r, -r, 0), (2 * a + r, 2 * a + r, 0), (a - r, 2 * a + r, 0), (a - r, r + 4, 0), (a - r, r + 2, z),
                     (a - r, -r - 2, z), (a - r, -r - 4, 0), (a - r, -2 * a - r, 0), (3 * a, -2 * a - r, 0)]
            PL, PR = (PA, PB) if j % 6 == 0 else (PB, PA)
            PL += [(x + px, y0 + py, pz) for px, py, pz in left]; PR += [(x + px, y0 + py, pz) for px, py, pz in right]
            x += 3 * a; y0 -= 2 * a
    Y = y0 - 30 - 2 * x                                   # the way back: four right turns, far below
    PL, PR = (PA, PB) if j % 6 == 0 else (PB, PA)
    PL += [(x + g + r, y0 + r, 0), (x + g + r, Y - r, 0), (-g - r, Y - r, 0), (-g - r, r, 0)]
    PR += [(x + g - r, y0 - r, 0), (x + g - r, Y + r, 0), (-g + r, Y + r, 0), (-g + r, -r, 0)]
    if clasp is None: return ([PA, PB] if j % 6 == 0 else [PA + PB]), curls
    kl, kr = (-h, h) if clasp else (h, h)                 # hooked: one end dips, the other rises. clasp 0: both rise
    PL += [(-9, r, 0), (-7, r, kl * (clasp or 1))]; PR += [(-9, -r, 0), (-7, -r, kr * (clasp or 1))]
    return [PA + PB[::-1]], curls

def twists(n): return [('H', 1 if n > 0 else -1)] * (2 * abs(n))

def axis2(link): return [tuple(p[k] + q[k] for k in range(3)) for p, q in zip(*link)]     # twice the middle line
def twice(link): return [[tuple(2 * v for v in p) for p in comp] for comp in link]

def section_ribbons():
    # 1a. n full twists on a flat rectangle: Lk = n, four exact ways, for n = -8 .. 8.
    N = 8; magnus = 0
    for n in range(-N, N + 1):
        link, _ = build(twists(n)); X = milnor.diagram(link, TOP); M = lk_matrix(X, 2)
        assert len(X) == 2 * abs(n) and all(o[0] != u[0] and s == (1 if n > 0 else -1) for o, u, s in X)
        assert M[0][1] == n and M[0][0] == M[1][1] == 0                                   # a. the view from above
        for res, _M in milnor.over_views(link, count=3): assert res[(0, 1)] == res[(1, 0)] == n; magnus += 1   # a, b
        assert lk_cone(link[0], link[1]) == lk_cone(link[1], link[0]) == n                # c
        mid = axis2(link); big = twice(link)
        assert lk_cone(mid, big[0]) == lk_cone(mid, big[1]) == n                          # each edge winds n times round the middle line
        for comp in link: assert len(simplify([comp])[0]) == 3                            # d. each strand alone is unknotted
        tick(8)
    print(f"1a. Ribbon with n full twists, n = -{N}..{N} ({2 * N + 1} ribbons, two integer polygons each): Lk = n in every case.")
    print(f"    Four exact ways: crossings seen from above (2|n| of them, all of one sign); {magnus} other views with the Magnus")
    print("    coefficient; the cone surface; and each edge against the middle line. Each strand alone reduces to a triangle.")

    # 1b. twists and curls together: Lk = twists + curls, and seen from above the axis crosses itself `curls` times.
    T = 3; cases = 0; patterns = [p for m in range(3) for p in itertools.product((1, -1), repeat=m)]
    for t in range(-T, T + 1):
        for pat in patterns:
            link, curls = build(twists(t) + [('C', c) for c in pat]); want = t + sum(pat)
            X = milnor.diagram(link, TOP); M = lk_matrix(X, 2)
            assert len(X) == 2 * abs(t) + 4 * len(pat)
            assert M[0][1] == want and M[0][0] == M[1][1] == sum(pat)
            ax = milnor.diagram([axis2(link)], TOP)
            assert len(ax) == len(pat) and sum(s for _, _, s in ax) == sum(pat)           # the axis: one crossing per curl
            for res, _M in milnor.over_views(link, count=2): assert res[(0, 1)] == want
            assert lk_cone(link[0], link[1]) == want
            cases += 1; tick(5)
    assert cases == 49 and len(patterns) == 7
    print(f"1b. Twists t = -{T}..{T} with 0, 1 or 2 curls of either sign ({cases} ribbons): Lk = t + (sum of curl signs) in every case.")
    print("    Seen from above, the axis crosses itself once per curl, with the curl's sign: Lk = (twists) + (self-crossings of the axis).")

    # 1c. the two terms depend on the view, their sum does not (one curl, no twist).
    link, _ = build([('C', 1)]); ax = [axis2(link)]; seen = defaultdict(int)
    for Mv, X in generic_views(link, 40, seed=5):
        assert lk_matrix(X, 2)[0][1] == 1
        seen[sum(s for _, _, s in milnor.diagram(ax, Mv))] += 1; tick()
    assert dict(seen) == {1: 30, 0: 10}, dict(seen)
    print("1c. One curl, no twist, 40 views: Lk = 1 in all 40. The axis shows 1 signed self-crossing in 30 views and 0 in 10:")
    print("    how much of Lk is seen as writhe and how much as twist depends on the view. The sum does not.")

# ------------------------------------------------------------------ 2. strand passages

def section_passages():
    # 2a. every single crossing change in every diagram of a family: |change of lk| is 1 between two curves, 0 within one.
    between = within = magnus = 0
    family = [build(twists(t) + [('C', c) for c in pat])[0] for t in range(-2, 3) for pat in ((), (1,), (-1,), (1, -1))]
    for link in family:
        diagrams = [milnor.diagram(link, TOP)] + [X for _, X in generic_views(link, 1, seed=3)]
        for vi, X in enumerate(diagrams):
            base = lk_matrix(X, 2)[0][1]
            for k, (o, u, s) in enumerate(X):
                Y = milnor.flip(X, k); new = lk_matrix(Y, 2)[0][1]
                if o[0] != u[0]: assert new == base - s and abs(new - base) == 1; between += 1
                else: assert new == base; within += 1
                if vi == 0: assert milnor.invariants(Y, 2)[(0, 1)] == new; magnus += 1
                tick()
    assert (between, within, magnus) == (3120, 2992, 264), (between, within, magnus)
    print(f"2a. One strand passage (one crossing changed), {len(family)} ribbons, seen from above and in one other view each:")
    print(f"    {between} passages between the two strands, each changes Lk by exactly 1 (down at a positive crossing, up at a negative one);")
    print(f"    {within} passages of a strand through itself, each leaves Lk unchanged. {magnus} of these were recomputed with the Magnus coefficient.")

    # 2b. the flip is a real passage. Reverse the second half of one full twist: the strand goes back over, not under.
    link, _ = build(twists(1)); X = milnor.diagram(link, TOP)
    back, _ = build([('H', 1), ('H', -1)]); Xb = milnor.diagram(back, TOP)
    order = sorted(range(2), key=lambda k: max(point(link, X[k][0])[0], point(link, X[k][1])[0]))
    assert sorted(milnor.flip(X, order[1])) == sorted(Xb) and lk_matrix(Xb, 2)[0][1] == 0 and lk_cone(*back) == 0
    red = simplify(back); assert [len(c) for c in red] == [3, 3] and lk_cone(*red) == 0
    tick(3)
    print("2b. The flip is a real passage: the two polygons with one half twist turned back have exactly the flipped diagram,")
    print("    Lk goes from 1 to 0, and triangle moves then reduce them to two separate triangles.")

    # 2c. a duplex through a duplex: the four crossings of a curl change together, and Lk changes by exactly 2.
    cases = 0
    for t in range(-3, 4):
        for pat in [p for m in (1, 2) for p in itertools.product((1, -1), repeat=m)]:
            link, curls = build(twists(t) + [('C', c) for c in pat]); X = milnor.diagram(link, TOP); base = lk_matrix(X, 2)[0][1]
            for ci, (cx, cy) in enumerate(curls):
                four = {k for k, (o, u, s) in enumerate(X) if point(link, o)[0] - cx in (7, 17) and abs(point(link, o)[1] - cy) == 5}
                assert len(four) == 4 and {(X[k][0][0], X[k][1][0]) for k in four} == {(0, 0), (0, 1), (1, 0), (1, 1)}
                Y = flip_set(X, four); new = lk_matrix(Y, 2)[0][1]
                assert new == base - 2 * pat[ci] and abs(new - base) == 2
                other, _ = build(twists(t) + [('C', -c if k == ci else c) for k, c in enumerate(pat)])
                assert sorted(Y) == sorted(milnor.diagram(other, TOP)) and lk_cone(*other) == new
                cases += 1; tick(3)
    assert cases == 70
    print(f"2c. A duplex through a duplex ({cases} cases: every curl of every ribbon with 1 or 2 curls, t = -3..3): the four crossings")
    print("    change together, Lk changes by exactly 2, and the polygons with the bridge moved through have exactly that diagram.")

# ------------------------------------------------------------------ 3. catenanes: the (2,2k) torus link

def circle_points(R):
    """All integer points on the circle of radius R, counterclockwise from (R, 0)."""
    pts = set()
    for a in range(R + 1):
        b = math.isqrt(R * R - a * a)
        if b * b == R * R - a * a: pts |= {(a, b), (a, -b), (-a, b), (-a, -b)}
    def cmp(p, q):
        hp, hq = (0 if p[1] > 0 or (p[1] == 0 and p[0] > 0) else 1), (0 if q[1] > 0 or (q[1] == 0 and q[0] > 0) else 1)
        if hp != hq: return hp - hq
        c = p[0] * q[1] - p[1] * q[0]
        return -1 if c > 0 else (1 if c < 0 else 0)
    return sorted(pts, key=functools.cmp_to_key(cmp))

BIG = 1105                                               # 5 * 13 * 17: its circle carries 108 integer points
T8 = [(4, 3), (3, 4), (-3, 4), (-4, 3), (-4, -3), (-3, -4), (3, -4), (4, -3)]     # eight points on the circle of radius 5
RING = circle_points(BIG)

def torus_link(k, Q=16):
    """Two closed curves with every vertex on the round torus (rho - Q*BIG)^2 + z^2 = (5*BIG)^2. Each goes once the
    long way round and |k| times round the tube; they stay opposite each other on the tube. Right-handed for k > 0."""
    n = len(RING); out = []
    for j in (0, 1):
        comp = []
        for i, (a, b) in enumerate(RING):
            c, d = T8[(-(8 * abs(k) * i // n) + 4 * j) % 8]
            comp.append(((Q + c) * a, (Q + c) * b, BIG * d * (1 if k > 0 else -1)))
            assert comp[-1][0] ** 2 + comp[-1][1] ** 2 == ((Q + c) * BIG) ** 2 and c * c + d * d == 25     # on the torus
        out.append(comp)
    return out

def braid_word(link, X, centre, sense):
    """If each component runs once round `centre` in the view from above, always turning the same way, and never
    crosses itself, the diagram is a closed braid on two strands. Returns the crossing signs in order along it."""
    for comp in link:
        m = len(comp); turns = 0
        for i in range(m):
            u = (comp[i][0] - centre[0], comp[i][1] - centre[1]); v = (comp[(i + 1) % m][0] - centre[0], comp[(i + 1) % m][1] - centre[1])
            assert sense * (u[0] * v[1] - u[1] * v[0]) > 0, "not a closed braid"
            if (u[1] < 0) != (v[1] < 0) and (u[0] * v[1] - u[1] * v[0]) * (v[1] - u[1]) > 0: turns += 1   # crosses the ray y = 0, x > 0
        assert turns == 1
    assert all(o[0] != u[0] for o, u, s in X)
    return [s for _, s in sorted(((o[1] if o[0] == 0 else u[1]), s) for o, u, s in X)]

def section_catenanes():
    assert len(RING) == 108
    K = 8; magnus = 0
    for k in list(range(1, K + 1)) + [-k for k in range(1, K + 1)]:
        link = torus_link(k); X = milnor.diagram(link, TOP); sg = 1 if k > 0 else -1
        word = braid_word(link, X, (0, 0), 1)
        assert word == [sg] * (2 * abs(k)) and lk_matrix(X, 2)[0][1] == k
        for res, _M in milnor.over_views(link, count=2): assert res[(0, 1)] == k; magnus += 1
        assert lk_cone(link[0], link[1]) == k
        rib, _ = build(twists(k)); Xr = milnor.diagram(rib, TOP); xs = max(p[0] for p in rib[0]); ys = min(p[1] for p in rib[0])
        assert braid_word(rib, Xr, (xs // 2, ys // 2), -1) == word                        # the k-twist ribbon is the same closed braid
        tick(5)
    print(f"3a. The (2,2k) torus link on a round torus (108 integer points the long way round), k = 1..{K} and mirror images:")
    print(f"    seen from above it is a closed braid on two strands with 2k crossings of one sign; Lk = k ({magnus} other views, and the cone).")
    print("    The two edges of the k-twist ribbon of section 1 give the same braid word: they are the same link.")

    # 3b. every set of strand passages on the standard diagram, k = 1..6.
    KF = 6; subsets = 0; minimal = []
    for k in range(1, KF + 1):
        link = torus_link(k); X = milnor.diagram(link, TOP); zero = defaultdict(int)
        for S in range(1 << (2 * k)):
            chosen = {i for i in range(2 * k) if S >> i & 1}; Y = flip_set(X, chosen)
            lk = lk_matrix(Y, 2)[0][1]
            assert lk == k - len(chosen) and milnor.invariants(Y, 2)[(0, 1)] == lk
            assert sum(s for _, _, s in Y) == 2 * lk                                      # closed braid sigma^(2 lk): the (2, 2 lk) torus link
            if lk == 0: zero[len(chosen)] += 1
            subsets += 1; tick()
        assert list(zero) == [k]; minimal.append(zero[k])
    assert subsets == 5460 and minimal == [2, 6, 20, 70, 252, 924] == [math.comb(2 * k, k) for k in range(1, KF + 1)]
    print(f"3b. Every set of passages on the 2k-crossing diagram, k = 1..{KF} ({subsets} sets, counted and by Magnus coefficient):")
    print("    j passages leave Lk = k - j, and the closed braid with 2(k - j) crossings left over, the (2,2(k-j)) torus link.")
    print(f"    Lk = 0 is reached by exactly k passages, never fewer. Sets of k passages that do it: {minimal} (central binomial).")

    # 3c. k passages suffice, shown on the polygons: k half twists turned back, then triangle moves.
    for k in range(1, KF + 1):
        link, _ = build(twists(k)); X = milnor.diagram(link, TOP)
        order = sorted(range(len(X)), key=lambda i: point(link, X[i][0])[0])
        back, _ = build([('H', 1), ('H', -1)] * k)
        assert sorted(flip_set(X, set(order[1::2]))) == sorted(milnor.diagram(back, TOP))
        red = simplify(back); assert [len(c) for c in red] == [3, 3] and lk_cone(*red) == 0
        tick(2)
    print(f"3c. k passages are enough (k = 1..{KF}): with every second crossing passed, triangle moves reduce the two polygons to two")
    print("    triangles with Lk = 0, which can be pulled apart. So unlinking the (2,2k) catenane takes exactly k passages.")

    # 3d. the ladder T(2,n), n half twists: two rings for n even, one knotted ring for n odd.
    dets = []; lks = []
    for n in range(1, 10):
        link, _ = build([('H', 1)] * n); X = milnor.diagram(link, TOP)
        assert len(link) == 2 - n % 2 and len(X) == n
        if n % 2 == 0: lks.append(lk_matrix(X, 2)[0][1]); assert lk_cone(*link) == lks[-1]
        else:
            al = alexander(X); assert al == tuple((-1) ** i for i in range(n))            # t^(n-1) - t^(n-2) + ... + 1
            assert all(alexander(Y) == al for _, Y in generic_views(link, 2, seed=2))
            dets.append(abs(sum(c * (-1) ** i for i, c in enumerate(al))))
        tick(2)
    assert lks == [1, 2, 3, 4] and dets == [1, 3, 5, 7, 9]
    print("3d. The ladder of n half twists, n = 1..9: two rings with Lk = n/2 for even n; for odd n one ring, the (2,n) torus knot,")
    print(f"    with Alexander polynomial t^(n-1) - t^(n-2) + ... + 1 and determinants {dets} (n = 1 is unknotted).")

# ------------------------------------------------------------------ 4. kinetoplast chainmail on a honeycomb

DIRS = [(1, 1), (-2, 1), (1, -2)]                        # from an up site to its three neighbours (sheared lattice)
HEX = [(1, 1), (-1, 2), (-2, 1), (-1, -1), (1, -2), (2, -1)]                              # the six corners of a cell

def honeycomb(p):
    """The hexagon-shaped patch with p rings of cells. Sites are integer points of a sheared lattice (an affine
    picture of the regular honeycomb): 'up' sites have both coordinates = 1 mod 3, 'down' sites = 2 mod 3."""
    cells = [(i, j) for i in range(-p + 1, p) for j in range(-p + 1, p) if abs(i + j) < p]
    edges = set()
    for i, j in cells:
        cyc = [(3 * i + x, 3 * j + y) for x, y in HEX]
        for a, b in zip(cyc, cyc[1:] + cyc[:1]): edges.add((min(a, b), max(a, b)))
    sites = sorted({v for e in edges for v in e})
    adj = {v: set() for v in sites}
    for a, b in edges: adj[a].add(b); adj[b].add(a)
    for v in sites:                                       # the patch is the lattice restricted to its sites
        nb = {(v[0] + s * dx, v[1] + s * dy) for dx, dy in DIRS for s in ((1,) if v[0] % 3 == 1 else (-1,))}
        assert adj[v] == nb & set(sites)
    return cells, sites, adj

def chainmail(sites, adj, S=12, h=3):
    """One ring per site. Up sites: a flat hexagon in the plane z = 0, counterclockwise. Down sites: a ring that
    rises through the hexagon of each neighbour, once, and comes back down near its own site."""
    rings = []
    for v in sites:
        U = (S * v[0], S * v[1])
        if v[0] % 3 == 1:
            d0, d1, d2 = DIRS; order = [d0, (-d2[0], -d2[1]), d1, (-d0[0], -d0[1]), d2, (-d1[0], -d1[1])]
            rings.append([(U[0] + 4 * x, U[1] + 4 * y, 0) for x, y in order])
        else:
            e = [(-DIRS[2][0], -DIRS[2][1]), (-DIRS[0][0], -DIRS[0][1]), (-DIRS[1][0], -DIRS[1][1])]      # counterclockwise
            ring = []
            for m in range(3):
                if (v[0] + e[m][0], v[1] + e[m][1]) not in adj[v]: continue
                P = (U[0] + 10 * e[m][0], U[1] + 10 * e[m][1]); H = (U[0] - e[(m + 2) % 3][0], U[1] - e[(m + 2) % 3][1])
                ring += [(P[0], P[1], h), (P[0], P[1], -h), (H[0], H[1], -h), (H[0], H[1], h)]
            rings.append(ring[::-1])                      # reversed: it goes up through each hexagon
    return rings

def components(vs, adj):
    vs = set(vs); seen = set(); n = 0
    for s in vs:
        if s in seen: continue
        n += 1; todo = [s]; seen.add(s)
        while todo:
            x = todo.pop()
            for y in adj[x]:
                if y in vs and y not in seen: seen.add(y); todo.append(y)
    return n

def girth(sites, adj):
    best = None
    for s in sites:
        dist = {s: 0}; par = {s: None}; todo = [s]
        for x in todo:
            for y in adj[x]:
                if y not in dist: dist[y] = dist[x] + 1; par[y] = x; todo.append(y)
                elif par[x] != y: best = min(best or 10 ** 9, dist[x] + dist[y] + 1)
    return best

def section_chainmail():
    rows = []
    for p in (1, 2, 3, 4):
        cells, sites, adj = honeycomb(p); n = len(sites); idx = {v: i for i, v in enumerate(sites)}
        E = sum(len(adj[v]) for v in sites) // 2; deg = [len(adj[v]) for v in sites]
        assert n == 6 * p * p and E == 9 * p * p - 3 * p and len(cells) == 3 * p * p - 3 * p + 1 and n - E + len(cells) == 1
        assert deg.count(3) == 6 * p * p - 6 * p and deg.count(2) == 6 * p and set(deg) <= {2, 3}
        assert all(v[0] % 3 != w[0] % 3 for v in sites for w in adj[v]) and girth(sites, adj) == 6      # two kinds of site; shortest cycle 6
        A = [[1 if sites[j] in adj[sites[i]] else 0 for j in range(n)] for i in range(n)]
        rings = chainmail(sites, adj)
        L = [[0] * n for _ in range(n)]                   # c. the cone, every pair
        for i in range(n):
            for j in range(i + 1, n): L[i][j] = L[j][i] = lk_cone(rings[i], rings[j])
        assert L == A; tick(n * (n - 1) // 2)
        views = 0
        if p <= 3:                                        # a. crossing counts in other views, every pair
            for _M, X in generic_views(rings, 2, seed=11):
                M = lk_matrix(X, n); assert all(M[i][j] == A[i][j] for i in range(n) for j in range(n) if i != j); views += 1; tick(n * (n - 1) // 2)
        discs = 0                                         # the flat hexagon as a surface: each neighbour goes up through it once
        for i, v in enumerate(sites):
            if v[0] % 3 != 1: continue
            hub = (12 * v[0], 12 * v[1], 0); hexa = rings[i]
            for j, w in enumerate(sites):
                if w[0] % 3 != 2: continue
                hits = []
                for k in range(len(rings[j])):
                    a, b = rings[j][k], rings[j][(k + 1) % len(rings[j])]
                    if (a[2] > 0) != (b[2] > 0):         # a vertical edge: where does it meet z = 0?
                        assert a[:2] == b[:2]
                        if all(orient2(hexa[m][:2], hexa[(m + 1) % 6][:2], a[:2]) > 0 for m in range(6)): hits.append(1 if b[2] > a[2] else -1)
                assert hits == ([1] if A[i][j] else []); discs += 1
        tick(discs)
        hopf = split = 0
        if p <= 3:                                        # d. every pair of rings, alone, by triangle moves
            for i in range(n):
                for j in range(i + 1, n):
                    red = simplify([rings[i], rings[j]]); assert [len(c) for c in red] == [3, 3] and lk_cone(*red) == A[i][j]
                    hopf += A[i][j]; split += 1 - A[i][j]; tick()
            assert hopf == E and hopf + split == n * (n - 1) // 2
        cut = sum(components([w for w in sites if w != v], adj) > 1 for v in sites)       # rings whose removal splits the rest
        bridges = 0
        for a in sites:
            for b in list(adj[a]):
                if a < b:
                    adj[a].discard(b); adj[b].discard(a); bridges += components(sites, adj) > 1; adj[a].add(b); adj[b].add(a)
        assert cut == 0 and bridges == 0 and components(sites, adj) == 1; tick(n + E)
        rows.append((p, len(cells), n, E, deg.count(3), deg.count(2), views, hopf, split))
    assert rows == [(1, 1, 6, 6, 0, 6, 2, 6, 9), (2, 7, 24, 30, 12, 12, 2, 30, 246), (3, 19, 54, 72, 36, 18, 2, 72, 1359), (4, 37, 96, 132, 72, 24, 0, 0, 0)], rows
    print("4a. Chainmail on honeycomb patches. The matrix of linking numbers equals the adjacency matrix, entry by entry:")
    print("    p  cells  rings  links  valence 3  valence 2  how")
    for p, c, n, E, d3, d2, views, hopf, split in rows:
        how = f"cone, {views} views, discs; alone, {hopf} pairs are Hopf links and {split} come apart" if views else "cone, discs"
        print(f"    {p}  {c:5d}  {n:5d}  {E:5d}  {d3:9d}  {d2:9d}  {how}")
    print("    rings = 6p^2, links = 9p^2 - 3p, cells = 3p^2 - 3p + 1. Every ring off the rim has valence 3; the shortest cycle has 6 rings.")
    print("    No ring is critical: take any one ring away and the rest still hang together. No single link is critical either.")

    # 4b. orientation: reversing a ring changes the sign of its row and column, nothing else.
    cells, sites, adj = honeycomb(1); rings = chainmail(sites, adj); n = 6
    for mask in range(64):
        rs = [r[::-1] if mask >> i & 1 else r for i, r in enumerate(rings)]; prod = 1
        for i in range(n):
            j = sites.index(sorted(adj[sites[i]])[0])
            for w in adj[sites[i]]:
                j = sites.index(w); lk = lk_cone(rs[i], rs[j])
                assert lk == (-1) ** ((mask >> i & 1) + (mask >> j & 1))
                if i < j: prod *= lk
        assert prod == 1; tick()
    print("4b. One cell (6 rings), all 64 choices of direction: every linking number is +1 or -1, its absolute value is the adjacency,")
    print("    and the product of the six round the cell is +1 every time. That product does not depend on the directions chosen.")

def animals(nbrs, roots, cell, N):
    """Connected sets of sites ('animals') up to N sites, counted up to translation, by size and perimeter (the number
    of outside sites next to the animal). Two independent ways: (1) every connected set through a fixed root site,
    divided by size; (2) growing animals one site at a time and keeping one copy per translation class."""
    one = defaultdict(int)
    for root in roots:
        cells = [root]; seen = {root}
        def rec(untried, size):
            untried = list(untried)
            while untried:
                c = untried.pop(); cells.append(c)
                new = [x for x in nbrs(c) if x not in seen]; seen.update(new)
                inside = set(cells); per = {y for x in cells for y in nbrs(x)} - inside
                one[(size + 1, len(per))] += 1
                if size + 1 < N: rec(untried + new, size + 1)
                cells.pop(); seen.difference_update(new)
        cells.pop(); seen = {root}; rec([root], 0)
    for (n, t), c in one.items(): assert c % n == 0
    one = {k: c // k[0] for k, c in one.items()}
    def canon(s):
        x0, y0 = min(s); dx, dy = (x0 // cell) * cell, (y0 // cell) * cell
        return frozenset((x - dx, y - dy) for x, y in s)
    two = defaultdict(int); level = {canon({r}) for r in roots}
    for n in range(1, N + 1):
        for s in level: two[(n, len({y for x in s for y in nbrs(x)} - s))] += 1
        if n < N: level = {canon(s | {y}) for s in level for x in s for y in nbrs(x) if y not in s}
    assert one == dict(two), "the two enumerations disagree"
    return one

def section_oligomers():
    def honey(v): s = 1 if v[0] % 3 == 1 else -1; return [(v[0] + s * dx, v[1] + s * dy) for dx, dy in DIRS]
    def square(v): return [(v[0] + 1, v[1]), (v[0] - 1, v[1]), (v[0], v[1] + 1), (v[0], v[1] - 1)]
    def tri(v): return square(v) + [(v[0] + 1, v[1] - 1), (v[0] - 1, v[1] + 1)]
    lattices = [("honeycomb", 3, honey, [(1, 1), (2, 2)], 3, 10), ("square", 4, square, [(0, 0)], 1, 8), ("triangular", 6, tri, [(0, 0)], 1, 7)]
    want = {"honeycomb": [2, 3, 6, 14, 36, 94, 250, 675, 1838, 5053], "square": [1, 2, 6, 19, 63, 216, 760, 2725], "triangular": [1, 3, 11, 44, 186, 814, 3652]}
    half = {"honeycomb": ("1/16", "3/128", "3/256"), "square": ("1/32", "1/128", "5/1024"), "triangular": ("1/128", "3/1024", "13/8192")}
    print("4c. Cut each ring with the same chance q, independently. The pieces set free are the connected sets of sites (animals) of the")
    print("    pattern. An animal with n rings and t neighbours outside it comes free with chance (1-q)^n q^t. Counted up to translation,")
    print("    two independent ways that agree; the animals of each size:")
    for name, z, nb, roots, cell, N in lattices:
        G = animals(nb, roots, cell, N); sites = len(roots)
        counts = [sum(c for (n, t), c in G.items() if n == m) for m in range(1, N + 1)]
        assert counts == want[name]; tick(sum(counts))
        assert {t: c for (n, t), c in G.items() if n == 1} == {z: sites}                  # a single ring has `valence` neighbours
        assert sum(c for (n, t), c in G.items() if n == 2) * 2 == z * sites               # pairs per ring = valence / 2
        # every surviving ring lies in exactly one piece:  sum of n G(n,t) p^n (1-p)^t = sites * p, up to p^N
        series = [0] * (N + 1)
        for (n, t), c in G.items():
            for k in range(min(t, N - n) + 1): series[n + k] += n * c * math.comb(t, k) * (-1) ** k
        assert series == [0, sites] + [0] * (N - 1); tick()
        q = Fraction(1, 2); y = [sum(Fraction(c, sites) * (1 - q) ** n * q ** t for (n, t), c in G.items() if n == m) for m in (1, 2, 3)]
        assert tuple(str(v) for v in y) == half[name]
        print(f"    valence {z} ({name}, n = 1..{N}): {counts}")
        print(f"        singles, pairs, triples per ring when half the rings are cut: {', '.join(half[name])}")
        if name == "honeycomb":
            assert {t: c for (n, t), c in G.items() if n == 3} == {5: 6} and {t: c for (n, t), c in G.items() if n == 4} == {6: 14}
            assert {t: c for (n, t), c in G.items() if n == 6} == {6: 1, 7: 6, 8: 87}
            # tetramers: chains against stars (one ring hooked to three others)
            stars = sum(1 for r in roots for _ in [0]); chains = counts[3] - stars
            assert (chains, stars) == (12, 2)
    print("    In each pattern the series check holds: every uncut ring lies in exactly one piece (sum of n * count * (1-q)^n q^t = 1-q,")
    print("    to the order enumerated). The valence shows in the pieces: a single ring has `valence` neighbours to lose, and there are")
    print("    valence/2 kinds of pair per ring. On the honeycomb all 6 triples are chains, the 14 fours are 12 chains and 2 stars,")
    print("    and the first closed piece is the 6-ring cell (1 of the 94 sixes).")

# ------------------------------------------------------------------ 5. Borromean rings and knots

def section_borromean():
    B = milnor.borromean(); pairs = list(itertools.permutations(range(3), 2))
    for res, _M in milnor.over_views(B):
        assert all(res[p] == 0 for p in pairs) and res[(0, 1, 2)] == res[(1, 2, 0)] == res[(2, 0, 1)] == -1; tick()
    V = [[1, -1, 0], [1, 1, -2], [1, 1, 1]]              # the view along (1, 1, 1): the usual picture with threefold symmetry
    X = milnor.diagram(B, V); assert len(X) == 6
    for c in range(3):                                    # alternating: over, under, over, under along each ring
        seq = [kind for _, kind in sorted([(o[1], 'o') for o, u, s in X if o[0] == c] + [(u[1], 'u') for o, u, s in X if u[0] == c])]
        assert len(seq) == 4 and all(seq[i] != seq[i - 1] for i in range(4))
    for mask in range(8):                                 # every choice of directions
        Y = milnor.diagram([r[::-1] if mask >> i & 1 else r for i, r in enumerate(B)], V); signs = defaultdict(list)
        for o, u, s in Y: signs[frozenset((o[0], u[0]))].append(s)
        assert len(signs) == 3 and all(sorted(v) == [-1, 1] for v in signs.values()); tick()
    def r2(k):                                            # squared distance of a crossing from the centre of the picture
        P = point(B, X[k][0]); xy = [sum(V[r][i] * P[i] for i in range(3)) for r in range(2)]
        return xy[0] ** 2 + xy[1] ** 2
    order = sorted(range(6), key=r2); inner, outer = order[:3], order[3:]
    assert r2(inner[2]) < r2(outer[0]) and len({X[k][2] for k in inner}) == 1 and len({X[k][2] for k in outer}) == 1 and X[inner[0]][2] == -X[outer[0]][2]
    for k in range(6):                                    # one strand passage: those two rings become a Hopf link, the third is free
        o, u, s = X[k]; M = lk_matrix(milnor.flip(X, k), 3); third = 3 - o[0] - u[0]
        assert abs(M[o[0]][u[0]]) == 1 and M[o[0]][third] == M[u[0]][third] == 0; tick()
    print("5a. Borromean rings (the polygons of philosophy/milnor.py): every Lk = 0 and the triple number is -1, as computed there.")
    print("    In the six-crossing picture each pair of rings crosses twice, once with each sign, for all 8 choices of direction: 3 positive")
    print("    and 3 negative crossings, always. With the threefold-symmetric directions the 3 inner crossings share one sign and the 3 outer")
    print("    the other. One strand passage at any of the 6 crossings links those two rings (Lk = +-1) and frees the third.")

def section_knots():
    names = {(1, -1, 1): "3_1", (1, -3, 1): "4_1", (2, -3, 2): "5_2", (2, -5, 2): "6_1", (3, -5, 3): "7_2", (3, -7, 3): "8_1", (1,): "unknot"}
    table = []; dets = []
    for n in range(1, 7):
        row = []
        for cl in (1, -1):
            knot, _ = build([('H', 1)] * n, clasp=cl); X = milnor.diagram(knot, TOP); al = alexander(X)
            assert len(knot) == 1 and len(X) == n + 2
            seq = [kind for _, kind in sorted([(o[1], 'o') for o, u, s in X] + [(u[1], 'u') for o, u, s in X])]
            alt = all(seq[i] != seq[i - 1] for i in range(len(seq)))
            for _M, Y in generic_views(knot, 2, seed=4): assert alexander(Y) == al
            red = simplify(knot)[0]; assert alexander(generic_views([red], 1, seed=6)[0][1]) == al    # triangle moves keep the knot
            mirror, _ = build([('H', -1)] * n, clasp=-cl); assert alexander(milnor.diagram(mirror, TOP)) == al
            row.append((alt, al, len(red))); tick(5)
            # one passage at the clasp: the end that dipped under now stays above. Then triangle moves.
            loose, _ = build([('H', 1)] * n, clasp=0); Z = milnor.diagram(loose, TOP)
            hook = [k for k, (o, u, s) in enumerate(X) if point(knot, o)[0] == -7]
            assert len(hook) == 2 and any(sorted(milnor.flip(X, k)) == sorted(Z) for k in hook)
            assert len(simplify(loose)[0]) == 3; tick(2)
        (alt, al, sticks), (alt2, al2, sticks2) = sorted(row, reverse=True)
        assert alt and not alt2
        det = abs(sum(c * (-1) ** i for i, c in enumerate(al))); dets.append(det)
        table.append((n, names[al], poly(al), det, sticks, names[al2]))
    assert dets == [3, 5, 7, 9, 11, 13]
    assert [(r[1], r[2], r[5]) for r in table] == [("3_1", "t^2 - t + 1", "unknot"), ("4_1", "t^2 - 3t + 1", "3_1"), ("5_2", "2t^2 - 3t + 2", "4_1"),
                                                    ("6_1", "2t^2 - 5t + 2", "5_2"), ("7_2", "3t^2 - 5t + 3", "6_1"), ("8_1", "3t^2 - 7t + 3", "7_2")]
    assert [r[4] for r in table] == [6, 7, 8, 8, 9, 10], [r[4] for r in table]
    print("5b. Twist knots: a pair of strands with n half twists whose two ends hook each other. Seen from above: n + 2 crossings.")
    print("    n  knot  Alexander polynomial  determinant  edges left after triangle moves  with the hook the other way")
    for n, name, pl, det, sticks, other in table:
        print(f"    {n}  {name}   {pl:20s}  {det:11d}  {sticks:31d}  {other}")
    print("    The name is read from the polynomial and the crossing count (table of knots up to 8 crossings). The same polynomial comes")
    print("    out of two more views, of the mirror image, and of the polygon after triangle moves.")
    print("    One strand passage at the hook, and triangle moves reduce every one of them to a triangle: each is one passage from unknotted.")
    print("    n = 3 is the 5_2 knot: 5 crossings, polynomial 2t^2 - 3t + 2, determinant 7.")

# ------------------------------------------------------------------ 6. arithmetic on cited numbers

def section_numbers():
    mt, mini = 16569, 2500
    lo, mid, hi = Fraction(104, 10), Fraction(105, 10), Fraction(106, 10)
    assert mt / mid == 1578 and round(mt / lo) == 1593 and round(mt / hi) == 1563
    assert round(mini / lo) == 240 and round(mini / mid) == 238 and round(mini / hi) == 236
    assert 10 ** 6 // mid == 95238
    tick(3)
    print("6.  Arithmetic on cited numbers. A relaxed closed duplex of N base pairs has Lk near N/h, h = base pairs per turn (10.4 to 10.6).")
    print("    Human mitochondrial DNA, 16569 base pairs: 16569/10.5 = 1578 exactly; 1593 at h = 10.4, 1563 at h = 10.6.")
    print("    A kinetoplast minicircle of 2500 base pairs: about 238 (236 to 240). Reading 1,000,000 base pairs turns the helix 95238 times.")

# ------------------------------------------------------------------ 7. tested, floating point

def omega(p1, p2, p3, p4):
    """Signed solid angle of the directions in which the segments p1p2 and p3p4 appear to cross: the exact value of
    the Gauss double integral over the two segments, times 4 pi. Zero when the segments lie in one plane."""
    r12, r34, r13, r14, r23, r24 = sub(p2, p1), sub(p4, p3), sub(p3, p1), sub(p4, p1), sub(p3, p2), sub(p4, p2)
    tr = dot(cross(r34, r12), r13)
    if tr == 0: return 0.0
    ns = []
    for v in (cross(r13, r14), cross(r14, r24), cross(r24, r23), cross(r23, r13)):
        L = math.sqrt(dot(v, v)); ns.append((v[0] / L, v[1] / L, v[2] / L))
    om = sum(math.asin(max(-1.0, min(1.0, dot(ns[i], ns[(i + 1) % 4])))) for i in range(4))
    return om if tr > 0 else -om

def gauss_lk(A, B):
    return sum(omega(A[i], A[(i + 1) % len(A)], B[j], B[(j + 1) % len(B)]) for i in range(len(A)) for j in range(len(B))) / (4 * math.pi)

def writhe(P):
    n = len(P)
    return sum(omega(P[i], P[(i + 1) % n], P[j], P[(j + 1) % n]) for i in range(n) for j in range(i + 2, n) if (i, j) != (0, n - 1)) / (2 * math.pi)

def twist(Xs, Ws):
    """Twist of the ribbon with axis polygon Xs and edge Xs + Ws, in turns. Along an edge: the angle by which the
    part of W across the edge turns. At a vertex: the angle between the frame carried round the corner without
    twisting and the frame the next edge starts with."""
    def fsub(a, b): return (a[0] - b[0], a[1] - b[1], a[2] - b[2])
    def unit(v): L = math.sqrt(dot(v, v)); return (v[0] / L, v[1] / L, v[2] / L)
    def perp(w, t): d = dot(w, t); return unit((w[0] - d * t[0], w[1] - d * t[1], w[2] - d * t[2]))
    def angle(u, v, t): return math.atan2(dot(t, cross(u, v)), dot(u, v))
    n = len(Xs); T = [unit(fsub(Xs[(i + 1) % n], Xs[i])) for i in range(n)]; total = 0.0
    for i in range(n):
        total += angle(perp(Ws[i], T[i]), perp(Ws[(i + 1) % n], T[i]), T[i])
        t0, t1 = T[i - 1], T[i]; u = perp(Ws[i], t0); b = cross(t0, t1); s = math.sqrt(dot(b, b))
        if s > 1e-12:                                     # carry u round the corner: turn it about b by the corner's angle
            b = (b[0] / s, b[1] / s, b[2] / s); c = dot(t0, t1); bu = cross(b, u); d = dot(b, u)
            u = tuple(u[k] * c + bu[k] * s + b[k] * d * (1 - c) for k in range(3))
        total += angle(u, perp(Ws[i], t1), t1)
    return total / (2 * math.pi)

def bumpy(shape, m, n=96, scale=20000, width=700):
    """A ribbon on a space curve that is not planar, with m extra turns of the frame. Vertices rounded to integers."""
    a, b, c, d = shape; X = []; W = []
    def pos(s): return ((math.cos(s) + a * math.cos(2 * s)), (math.sin(s) - b * math.sin(3 * s)), (c * math.sin(2 * s) + d * math.cos(3 * s)))
    for i in range(n):
        s = 2 * math.pi * i / n; p = pos(s); e = 1e-4; q0, q1 = pos(s - e), pos(s + e)
        t = tuple(q1[k] - q0[k] for k in range(3)); L = math.sqrt(dot(t, t)); t = tuple(x / L for x in t)
        ref = (0.3, 0.5, 0.81); u = cross(ref, t); L = math.sqrt(dot(u, u)); u = tuple(x / L for x in u); v = cross(t, u)
        ph = m * s
        X.append(tuple(round(scale * x) for x in p))
        W.append(tuple(round(width * (math.cos(ph) * u[k] + math.sin(ph) * v[k])) for k in range(3)))
    A = [tuple(x[k] + w[k] for k in range(3)) for x, w in zip(X, W)]; B = [tuple(x[k] - w[k] for k in range(3)) for x, w in zip(X, W)]
    return X, W, A, B

def section_tested():
    worst = 0.0; count = 0
    for n in range(-4, 5):
        link, _ = build(twists(n)); worst = max(worst, abs(gauss_lk(*link) - n)); count += 1
    for k in (1, 3, -2):
        link = torus_link(k); worst = max(worst, abs(gauss_lk(*link) - k)); count += 1
    assert worst < 1e-9 and count == 12
    print(f"7a. Tested (floating point): the Gauss double integral, summed in closed form over pairs of segments, gives the exact Lk for")
    print(f"    {count} links of sections 1 and 3 to within 1e-9.")
    worst = 0.0; rows = []
    for t, pat in ((0, (1,)), (2, (1,)), (-1, (-1,)), (1, (1, 1)), (3, (1, -1))):
        link, _ = build(twists(t) + [('C', c) for c in pat]); mid = axis2(link); big = twice(link)
        W = [tuple(p[k] - x[k] for k in range(3)) for p, x in zip(big[0], mid)]
        wr, tw = writhe(mid), twist(mid, W); lk = lk_cone(*link)
        worst = max(worst, abs(wr - sum(pat)), abs(tw - t), abs(lk - tw - wr))
    assert worst < 1e-9
    print("7b. Tested: on the curled ribbons of section 1 the writhe of the axis (Gauss integral of the axis with itself) equals the")
    print("    number of curls and the twist equals the number of twists, to within 1e-9. There the two terms are whole numbers.")
    worst = 0.0
    for shape in ((0.3, 0.2, 0.4, 0.3), (0.25, -0.15, 0.5, -0.2), (0.0, 0.3, 0.6, 0.25)):
        for m in (-2, -1, 0, 1, 2):
            X, W, A, B = bumpy(shape, m); lk = lk_cone(A, B)
            assert lk == lk_cone(X, A) == lk_cone(X, B) and all(r[(0, 1)] == lk for r, _M in milnor.over_views([A, B], count=2))
            wr, tw = writhe(X), twist(X, W); worst = max(worst, abs(lk - tw - wr)); rows.append((lk, wr, tw))
    assert worst < 1e-9 and len(rows) == 15
    frac = [abs(wr - round(wr)) for _, wr, _ in rows]; assert min(frac) > 0.05
    ex = rows[3]
    print(f"7c. Tested: Lk = Tw + Wr on 15 ribbons whose axis is a bumpy space curve (3 curves, -2..2 extra turns). Lk is exact (cone,")
    print(f"    views, and against the axis); Tw and Wr are floating point; |Lk - Tw - Wr| < 1e-9 in all 15. The writhe is not a whole")
    print(f"    number in any of them (for example Lk = {ex[0]}, Wr = {ex[1]:.6f}, Tw = {ex[2]:.6f}).")
    return rows

# ------------------------------------------------------------------ main

def main():
    t0 = time.time()
    section_ribbons(); section_passages(); section_catenanes(); section_chainmail(); section_oligomers()
    section_borromean(); section_knots(); section_numbers()
    exact = STATES[0]
    section_tested()
    print("PASS")
    print(json.dumps({"states": exact, "seconds": round(time.time() - t0, 2)}))

if __name__ == "__main__":
    main()
