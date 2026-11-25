#!/usr/bin/env python3
"""DNA topology, checked with exact integer arithmetic on polygons (reuses philosophy/milnor.py, unmodified).

1. A closed two-strand ribbon with n full twists about a flat circle: lk(strand 1, strand 2) = n.
2. Strand passage = crossing flip: every inter-strand flip changes lk by exactly 1 in absolute value;
   a duplex passage (all four strand crossings of a duplex self-crossing) changes Lk by exactly 2.
3. Replication catenanes T(2,2k): lk = k; |lk| drops by 1 per flip, so k passages are needed, and k suffice for lk = 0.
4. Kinetoplast chainmail on a honeycomb patch: |lk| matrix = adjacency matrix; interior valence 3.
5. Borromean rings: all pairwise lk = 0, Milnor mu(123) = +-1.
Run: python3 -I brain/dna/check.py
"""
import json, math, os, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'philosophy'))
import milnor
from milnor import diagram, flip, lk_by_count, invariants, views, Degenerate, SC

T0 = time.time(); STATES = 0
VIEWS = views(7, 40)

def gen_diagram(link):
    for M in VIEWS:
        try: return diagram(link, M)
        except Degenerate: continue
    raise AssertionError("no generic view")

def P(v): return tuple(round(SC * c) for c in v)

def ribbon(n, core=None, m=None, w=0.12):
    """Two strands: the core curve and an edge turning n full times around it (frame z, radial: right-handed with the tangent)."""
    m = m or 16 * abs(n) + 64
    A, B = [], []
    for i in range(m):
        t = 2 * math.pi * (i + .5) / m
        if core is None:
            c = (2 * math.cos(t), 2 * math.sin(t), 0.0); r = (math.cos(t), math.sin(t), 0.0)
        else:
            c, r = core(t)
        u = (0.0, 0.0, 1.0); a = n * t
        A.append(P(c)); B.append(P(tuple(c[k] + w * (math.cos(a) * u[k] + math.sin(a) * r[k]) for k in range(3))))
    return [A, B]

# ---- 1. ribbon twist = linking number
res1 = {}
for n in range(-6, 7):
    X = gen_diagram(ribbon(n)); inv = invariants(X, 2)
    lk = lk_by_count(X, 0, 1); assert lk == n == inv[(0, 1)], (n, lk); res1[n] = lk; STATES += 1
print("1. ribbon, n full twists -> lk:", res1)

# ---- 2a. every inter-strand flip changes lk by exactly +-1
nflips = 0
for n in (-3, 0, 2, 5):
    X = gen_diagram(ribbon(n)); lk = lk_by_count(X, 0, 1)
    for k, (o, u, s) in enumerate(X):
        if o[0] != u[0]:
            d = lk_by_count(flip(X, k), 0, 1) - lk; assert abs(d) == 1 and d == -s; nflips += 1
print("2a. single strand passages checked:", nflips, "each |delta lk| = 1")
STATES += nflips

# ---- 2b. duplex passage on a figure-eight core changes Lk by 2
def eight(t):
    c = (2 * math.cos(t), math.sin(2 * t), 0.6 * math.sin(t))
    d = (-2 * math.sin(t), 2 * math.cos(2 * t), 0.0); L = math.hypot(d[0], d[1])
    return c, (d[1] / L, -d[0] / L, 0.0)
res2 = {}
for n in (-2, 0, 1, 3):
    link = ribbon(n, core=eight, m=160, w=0.08); m = 160
    X = gen_diagram(link); lk = lk_by_count(X, 0, 1); assert lk == n + 1   # the core itself has writhe-like +1 in this frame
    far = [k for k, (o, u, s) in enumerate(X) if min(abs(o[1] - u[1]), m - abs(o[1] - u[1])) > m // 4]
    assert len(far) == 4, len(far)
    Y = X
    for k in far: Y = flip(Y, k)
    d = lk_by_count(Y, 0, 1) - lk
    assert abs(d) == 2 and d == -sum(X[k][2] for k in far if X[k][0][0] != X[k][1][0])
    res2[n] = (lk, lk + d); STATES += 1
print("2b. duplex passage (4 strand crossings flipped), (Lk before, after):", res2)

# ---- 3. torus links T(2,2k)
def torus(k, m=None):
    m = m or 24 * abs(k) + 48; comps = []
    for j in (0, 1):
        pts = []
        for i in range(m):
            th = 2 * math.pi * (i + .5) / m; ph = k * th + math.pi * j
            R = 3 + math.cos(ph); pts.append(P((R * math.cos(th), R * math.sin(th), math.sin(ph))))
        comps.append(pts)
    return comps
res3 = {}
for k in list(range(-5, 0)) + list(range(1, 6)):
    X = gen_diagram(torus(k)); lk = lk_by_count(X, 0, 1); assert lk == invariants(X, 2)[(0, 1)] and abs(lk) == abs(k), (k, lk)
    steps = 0; X0lk = lk
    while lk != 0:
        j = next(i for i, (o, u, s) in enumerate(X) if o[0] != u[0] and s == (1 if lk > 0 else -1))
        X = flip(X, j); new = lk_by_count(X, 0, 1); assert abs(new) == abs(lk) - 1; lk = new; steps += 1
    assert lk == 0 and X0lk == -k and steps == abs(k); res3[k] = (X0lk, steps); STATES += 1
print("3. T(2,2k): k -> (lk, passages used to reach lk 0; lower bound |lk|):", res3)

# ---- 4. kinetoplast honeycomb chainmail
def honeycomb(R=2):
    pts = {}; global NHEX; NHEX = 0
    s3 = math.sqrt(3)
    for a in range(-R - 1, R + 2):
        for b in range(-R - 1, R + 2):
            cx, cy = 1.5 * a, s3 * (b + a / 2)              # hexagon centres
            if math.hypot(cx, cy) > 1.5 * R + 1e-9: continue
            NHEX += 1
            for q in range(6):
                v = (round(cx + math.cos(q * math.pi / 3), 6) + 0.0, round(cy + math.sin(q * math.pi / 3), 6) + 0.0)
                pts[v] = None
    V = sorted(pts); E = [(i, j) for i in range(len(V)) for j in range(i + 1, len(V))
                          if abs(math.dist(V[i], V[j]) - 1) < 1e-6]
    return V, E
V, E = honeycomb(2)
nb = {i: [] for i in range(len(V))}
for i, j in E: nb[i].append(j); nb[j].append(i)
col = {0: 0}; st = [0]
while st:
    i = st.pop()
    for j in nb[i]:
        if j not in col: col[j] = 1 - col[i]; st.append(j)
assert all(col[i] != col[j] for i, j in E)
rho = 0.35; rings = []
for i, v in enumerate(V):
    if col[i] == 0:
        rings.append([P((v[0] + rho * math.cos(t), v[1] + rho * math.sin(t), 0.0))
                      for t in (2 * math.pi * (q + .5) / 24 for q in range(24))])
    else:
        pts = []
        for idx, j in enumerate(nb[i]):
            a = V[j]; dx, dy = a[0] - v[0], a[1] - v[1]
            ang = math.atan2(dy, dx); e1, e2 = 0.12 * math.cos(ang + 1.2), 0.12 * math.sin(ang + 1.2)
            f1, f2 = 0.12 * math.cos(ang - 1.2), 0.12 * math.sin(ang - 1.2)
            tx, ty = a[0] - 0.12 * dx, a[1] - 0.12 * dy          # pierce a's disc off-centre, toward v
            pts += [P((v[0] + e1, v[1] + e2, 0.5)), P((tx, ty, 0.5)), P((tx, ty, -0.5)), P((v[0] + f1, v[1] + f2, -0.5))]
        # make consecutive low->high transitions at distinct points: already distinct by angle offsets
        rings.append(pts)
X = gen_diagram(rings); N = len(V)
LK = [[0 if i == j else lk_by_count(X, i, j) for j in range(N)] for i in range(N)]
ADJ = [[1 if (min(i, j), max(i, j)) in set(E) else 0 for j in range(N)] for i in range(N)]
assert [[abs(x) for x in r] for r in LK] == ADJ
deg = sorted(len(nb[i]) for i in range(N))
n3 = deg.count(3); assert max(deg) == 3, (N, deg)
assert (NHEX, N, len(E), n3) == (13, 42, 54, 24) and N - len(E) + NHEX == 1 and sum(deg) == 2 * len(E) and set(deg) == {2, 3}   # Euler for a disc, handshake
STATES += N * N
print("4. kinetoplast patch,", NHEX, "hexagons: rings", N, "links", len(E), "valence-3 rings", n3, "valence-2 (rim)", deg.count(2), "; |lk| matrix == adjacency: True")

# ---- 5. Borromean
inv = invariants(gen_diagram(milnor.borromean()), 3)
assert all(inv[(i, j)] == 0 for i in range(3) for j in range(3) if i != j) and abs(inv[(0, 1, 2)]) == 1
print("5. Borromean rings: pairwise lk 0, mu(123) =", inv[(0, 1, 2)]); STATES += 1

print("PASS")
print(json.dumps({"states": STATES, "seconds": round(time.time() - T0, 2)}))
