"""Membranes and cages: Euler characteristic checks inside the cell.
Run from repo root: python3 -I brain/membrane/check.py   (add --n11 to also enumerate n = 11)
"""
import sys, time, json, math, cmath
from collections import deque
T0 = time.time(); STATES = 0

# ---------- 1. triangulations of the sphere, by edge flips ----------
def rotation(faces):
    """faces: oriented triples. nxt[v][a] = neighbour after a around v (ccw)."""
    nxt = {}
    for (a, b, c) in faces:
        for (x, y, z) in ((a, b, c), (b, c, a), (c, a, b)):
            nxt.setdefault(x, {})[y] = z
    return nxt

def canon(faces):
    """canonical code up to isomorphism including mirror images."""
    nxt = rotation(faces)
    prv = {v: {b: a for a, b in d.items()} for v, d in nxt.items()}
    best = None
    md = max(len(d) for d in nxt.values())
    for rot in (nxt, prv):
        for u in rot:
            if len(rot[u]) != md: continue
            for v in rot[u]:
                lab = {u: 0}; order = [u]; first = {u: v}; code = []; i = 0
                while i < len(order):
                    x = order[i]; i += 1
                    y0 = first[x]; y = y0
                    while True:
                        if y not in lab:
                            lab[y] = len(order); order.append(y); first[y] = x
                        code.append(lab[y])
                        y = rot[x][y]
                        if y == y0: break
                    code.append(-1)
                    if best is not None and code > best[:len(code)] and len(code) <= len(best):
                        break
                else:
                    pass
                if i == len(order) and (best is None or code < best):
                    best = code
    return tuple(best)

def flips(faces):
    fs = set(faces)
    nxt = rotation(faces)
    for (a, b, c) in faces:
        if a < b:
            d = nxt[b][a]  # face (b,a,d)
            if d in nxt[c] or len(nxt[a]) <= 3 or len(nxt[b]) <= 3: continue
            g = set(fs); g.discard((a, b, c)); g.discard((b, c, a)); g.discard((c, a, b))
            for t in ((b, a, d), (a, d, b), (d, b, a)): g.discard(t)
            g.add((c, a, d)); g.add((d, b, c))
            yield norm(g)

def norm(g):
    out = set()
    for (a, b, c) in g:
        m = min(a, b, c)
        while a != m: a, b, c = b, c, a
        out.add((a, b, c))
    return frozenset(out)

def start(n):
    # bipyramid over an (n-2)-gon: poles 0,1; rim 2..n-1
    r = list(range(2, n)); fs = []
    for i in range(len(r)):
        x, y = r[i], r[(i + 1) % len(r)]
        fs.append((0, x, y)); fs.append((1, y, x))
    return norm(fs)

def enumerate_tri(n):
    global STATES
    s = start(n); seen = {canon(s): s}; q = deque([s])
    while q:
        f = q.popleft()
        for g in flips(f):
            STATES += 1
            c = canon(g)
            if c not in seen:
                seen[c] = g; q.append(g)
    return list(seen.values())

def check_tri(faces, V=None):
    nxt = rotation(faces)
    V = len(nxt); F = len(faces); E = sum(len(d) for d in nxt.values()) // 2
    edges = {}
    for (a, b, c) in faces:
        for (x, y) in ((a, b), (b, c), (c, a)):
            assert (x, y) not in edges; edges[(x, y)] = 1
    assert all((y, x) in edges for (x, y) in edges)  # closed, oriented
    assert V - E + F == 2 and E == 3 * V - 6 and F == 2 * V - 4
    assert sum(6 - len(d) for d in nxt.values()) == 12
    for v, d in nxt.items():  # link of each vertex is one cycle
        y0 = next(iter(d)); y = d[y0]; k = 1
        while y != y0: y = d[y]; k += 1
        assert k == len(d)
    return V, E, F

NMAX = 11 if "--n11" in sys.argv else 10
if "--quick" in sys.argv: NMAX = 9
EXPECT = {4: 1, 5: 1, 6: 2, 7: 5, 8: 14, 9: 50, 10: 233, 11: 1249}
counts = []
for n in range(4, NMAX + 1):
    ts = enumerate_tri(n)
    for t in ts: check_tri(t)
    counts.append(len(ts))
    assert len(ts) == EXPECT[n], (n, len(ts))
    print(f"n={n}: {len(ts)} triangulations; each has E=3V-6, F=2V-4, sum(6-deg)=12")

# ---------- 2. icosahedral triangulations and their cages ----------
ICO = norm([(0,1,2),(0,2,3),(0,3,4),(0,4,5),(0,5,1),(1,6,2),(2,7,3),(3,8,4),(4,9,5),(5,10,1),
            (2,6,7),(3,7,8),(4,8,9),(5,9,10),(1,10,6),(11,7,6),(11,8,7),(11,9,8),(11,10,9),(11,6,10)])

def subdivide(faces, h):
    """each triangle -> h^2 triangles; exact, vertices named by barycentric data on shared edges."""
    def name(a, b, c, i, j):  # point a*(h-i-j)/h + b*i/h + c*j/h
        w = {a: h - i - j, b: i, c: j}
        return tuple(sorted((v, x) for v, x in w.items() if x))
    out = []
    for (a, b, c) in faces:
        P = lambda i, j: name(a, b, c, i, j)
        for i in range(h):
            for j in range(h - i):
                out.append((P(i, j), P(i + 1, j), P(i, j + 1)))
                if i + j < h - 1:
                    out.append((P(i + 1, j), P(i + 1, j + 1), P(i, j + 1)))
    return norm(out)

def sqrt3(faces):
    """kis every face then flip every old edge: T -> 3T."""
    nxt = rotation(faces); out = []
    cen = {f: ("c", f) for f in faces}
    fid = {}
    for f in faces:
        a, b, c = f
        for (x, y) in ((a, b), (b, c), (c, a)): fid[(x, y)] = f
    for (x, y), f in fid.items():
        if (x, y) < (y, x):
            g = fid[(y, x)]
            out.append((cen[f], x, cen[g])); out.append((cen[g], y, cen[f]))
    return norm(out)

def relabel(faces):
    m = {}
    for f in sorted(faces, key=repr):
        for v in f: m.setdefault(v, len(m))
    return norm([tuple(m[v] for v in f) for f in faces])

def dual_cage(faces):
    """cage = dual: one corner per triangle, one face per vertex."""
    nxt = rotation(faces); fid = {}
    for f in faces:
        a, b, c = f
        for (x, y) in ((a, b), (b, c), (c, a)): fid[(x, y)] = f
    cagefaces = []
    for v, d in nxt.items():
        y0 = next(iter(d)); y = y0; poly = []
        while True:
            poly.append(fid[(v, y)]); y = d[y]
            if y == y0: break
        cagefaces.append(poly)
    corners = {}
    for p in cagefaces:
        for k in p: corners[k] = corners.get(k, 0) + 1
    edges = sum(len(p) for p in cagefaces) // 2
    assert all(x == 3 for x in corners.values())
    return cagefaces, len(corners), edges

Tlist = []
cases = []
for h in (1, 2, 3, 4, 5):
    cases.append(((h, 0), h * h, subdivide(ICO, h)))
    cases.append(((h, h), 3 * h * h, sqrt3(subdivide(ICO, h))))
cases.append((("sqrt3^2", None), 9, sqrt3(relabel(sqrt3(ICO)))))
for (hk, T, tri) in cases:
    tri = relabel(tri)
    if hk[1] is not None:
        h, k = hk; assert T == h * h + h * k + k * k
    V, E, F = check_tri(tri)
    nxt = rotation(tri)
    degs = sorted(len(d) for d in nxt.values())
    assert V == 10 * T + 2 and F == 20 * T
    assert degs.count(5) == 12 and degs.count(6) == V - 12
    cf, cV, cE = dual_cage(tri)
    pent = sum(1 for p in cf if len(p) == 5); hexa = sum(1 for p in cf if len(p) == 6)
    assert pent == 12 and hexa == len(cf) - 12 and cV - cE + len(cf) == 2
    assert cV == 20 * T and 3 * F == 60 * T  # 60T subunits: 3 per triangle
    print(f"(h,k)={hk} T={T}: V={V}=10T+2, 12 deg-5; cage {cV} corners, {pent} pentagons, {hexa} hexagons")
    if hk[1] is not None: Tlist.append(T)
Tseq = sorted(set(h * h + h * k + k * k for h in range(0, 8) for k in range(0, 8) if h + k > 0))[:12]
assert Tseq == [1, 3, 4, 7, 9, 12, 13, 16, 19, 21, 25, 27]
print("T numbers h^2+hk+k^2:", Tseq)

# ---------- 3. nuclear envelope: two spheres joined by N pores ----------
def envelope(N):
    V, E, F = set(), [], []
    def sq(s, i): return [(s, i, t) for t in range(4)]
    for s in ("in", "out"):
        for i in range(N):
            for v in sq(s, i): V.add(v)
            for t in range(4): E.append(((s, i, t), (s, i, (t + 1) % 4)))
        for i in range(N - 1): E.append(((s, i, 0), (s, i + 1, 0)))
        walk = []  # boundary walk of the single disk face, as edge indices of E
        def eid(x, y):
            for k, (p, q) in enumerate(E):
                if {p, q} == {x, y}: return k
        for i in range(N):
            for t in range(4): walk.append(eid((s, i, t), (s, i, (t + 1) % 4)))
            if i < N - 1: walk.append(eid((s, i, 0), (s, i + 1, 0)))
        for i in range(N - 2, -1, -1): walk.append(eid((s, i, 0), (s, i + 1, 0)))
        F.append(walk)
    base = len(E)
    for i in range(N):
        for t in range(4): E.append((("in", i, t), ("out", i, t)))
    def eid2(x, y):
        for k, (p, q) in enumerate(E):
            if {p, q} == {x, y}: return k
    for i in range(N):
        for t in range(4):
            u = (t + 1) % 4
            F.append([eid2(("in", i, t), ("in", i, u)), eid2(("in", i, u), ("out", i, u)),
                      eid2(("out", i, u), ("out", i, t)), eid2(("out", i, t), ("in", i, t))])
    use = [0] * len(E)
    for w in F:
        for k in w: assert k is not None; use[k] += 1
    assert all(x == 2 for x in use)  # closed surface: every edge on two face sides
    return len(V), len(E), len(F)
for N in range(1, 9):
    v, e, f = envelope(N); g = N - 1
    assert v - e + f == 2 - 2 * g
    print(f"N={N} pores: V={v} E={e} F={f}, V-E+F={v-e+f} = 2-2*{g}")

# ---------- 4. line fields on the sphere: defects sum to 2 (tested, floating point) ----------
roots = [1, -1, 2j, -0.5j]
def phi_z(z):
    p = 1
    for r in roots: p *= (z - r)
    return 0.5 * cmath.phase(p)
def phi_w(w):  # same line field in the chart w = 1/z: angle of dw = angle of dz + 2 arg w - pi
    return phi_z(1 / w) + 2 * cmath.phase(w) - math.pi
def wind(f, c, r, n=4000):
    tot = 0.0; prev = f(c + r)
    for k in range(1, n + 1):
        cur = f(c + r * cmath.exp(2j * math.pi * k / n))
        d = cur - prev; d = (d + math.pi / 2) % math.pi - math.pi / 2  # line field: mod pi
        tot += d; prev = cur
    return tot / (2 * math.pi)
charges = [wind(phi_z, r, 0.05) for r in roots] + [wind(phi_w, 0, 0.05)]
assert all(abs(c - 0.5) < 1e-9 for c in charges[:4]) and abs(charges[4]) < 1e-9
assert abs(sum(charges) - 2) < 1e-9
print("line field defects (tested):", [round(c, 6) for c in charges], "sum", round(sum(charges), 6))

assert counts == [EXPECT[n] for n in range(4, NMAX + 1)]
print("fingerprint triangulations:", counts)
print("PASS")
print(json.dumps({"states": STATES, "seconds": round(time.time() - T0, 2)}))
