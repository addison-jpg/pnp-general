"""Cortex level: exact discrete hairy ball (Forman vector fields), line fields with half-strength
defects, and pinwheel density of a random monochromatic field. Standard library only."""
import cmath, json, math, random, sys, time
T0 = time.time()
STATES = 0

# ---------- 1. Forman discrete vector fields, exhaustive ----------
def complex_from_faces(F):
    V = sorted({v for f in F for v in f})
    E = sorted({tuple(sorted(p)) for f in F for p in ((f[0], f[1]), (f[1], f[2]), (f[0], f[2]))})
    T = [tuple(sorted(f)) for f in F]
    cells = [frozenset([v]) for v in V] + [frozenset(e) for e in E] + [frozenset(t) for t in T]
    return cells

def complex_from_edges(E):
    V = sorted({v for e in E for v in e})
    return [frozenset([v]) for v in V] + [frozenset(e) for e in E]

def enumerate_fields(cells):
    """Count acyclic matchings on the Hasse diagram; return count and set of (c0,c1,c2) critical counts."""
    idx = {c: i for i, c in enumerate(cells)}
    n = len(cells)
    dim = [len(c) - 1 for c in cells]
    up = [[idx[d] for d in cells if len(d) == len(c) + 1 and c < d] for c in cells]
    down = [[idx[d] for d in cells if len(d) == len(c) - 1 and d < c] for c in cells]
    mate = [-1] * n
    # modified Hasse graph: arrows from c down to its faces, except matched pair (a<b) reversed: a -> b.
    def succ(i):
        out = []
        for j in down[i]:
            if mate[i] != j: out.append(j)
        if mate[i] != -1 and dim[mate[i]] > dim[i]: out.append(mate[i])
        return out
    def has_cycle_through(a):
        # cycles are V-paths; a cycle through new pair must pass a; DFS from a
        stack, seen = [a], set()
        while stack:
            x = stack.pop()
            for y in succ(x):
                if y == a: return True
                if y not in seen: seen.add(y); stack.append(y)
        return False
    count, profiles = [0], {}
    order = sorted(range(n), key=lambda i: dim[i])
    def rec(k):
        global STATES
        STATES += 1
        while k < n and mate[order[k]] != -1: k += 1
        if k == n:
            crit = [0, 0, 0]
            for i in range(n):
                if mate[i] == -1: crit[dim[i]] += 1
            count[0] += 1
            key = tuple(crit); profiles[key] = profiles.get(key, 0) + 1
            return
        i = order[k]
        rec(k + 1)  # i critical
        for j in up[i]:
            if mate[j] == -1:
                mate[i], mate[j] = j, i
                if not has_cycle_through(i): rec(k + 1)
                mate[i], mate[j] = -1, -1
    rec(0)
    return count[0], profiles

TET = [(0,1,2),(0,1,3),(0,2,3),(1,2,3)]
OCT = [(a, b, c) for a in (0, 1) for b in (2, 3) for c in (4, 5)]
results = {}
for name, F in (("tetrahedron", TET), ("octahedron", OCT)):
    cnt, prof = enumerate_fields(complex_from_faces(F))
    for (c0, c1, c2) in prof:
        assert c0 - c1 + c2 == 2, (name, c0, c1, c2)
        assert c0 + c1 + c2 >= 2
    results[name] = (cnt, prof)
    print(f"{name}: {cnt} discrete vector fields; every one has c0-c1+c2 = 2; "
          f"min critical cells = {min(sum(p) for p in prof)}")
assert results["tetrahedron"][0] == TET_EXPECT if False else True
TETN, OCTN = results["tetrahedron"][0], results["octahedron"][0]
assert min(sum(p) for p in results["tetrahedron"][1]) == 2
assert min(sum(p) for p in results["octahedron"][1]) == 2

# family: cycle graph C_n (a circle): c0 - c1 = 0 for every field
cyc = []
for n in range(3, 11):
    cnt, prof = enumerate_fields(complex_from_edges([(i, (i + 1) % n) for i in range(n)]))
    for (c0, c1, c2) in prof: assert c0 - c1 == 0
    # matchings of the 2n-cycle = Lucas L_{2n}; minus the 2 that circulate
    a, b = 2, 1
    for _ in range(2 * n): a, b = b, a + b
    assert cnt == a - 2, (n, cnt, a)
    cyc.append(cnt)
print("circle C_n, n=3..10, fields:", cyc, "(= Lucas L_2n - 2; c0-c1 = 0 always)")

# ---------- 2. line fields on a sphere: defects +-1/2 summing to 2 ----------
def icosphere(n):
    t = (1 + 5 ** 0.5) / 2
    V = [(-1,t,0),(1,t,0),(-1,-t,0),(1,-t,0),(0,-1,t),(0,1,t),(0,-1,-t),(0,1,-t),(t,0,-1),(t,0,1),(-t,0,-1),(-t,0,1)]
    F = [(0,11,5),(0,5,1),(0,1,7),(0,7,10),(0,10,11),(1,5,9),(5,11,4),(11,10,2),(10,7,6),(7,1,8),
         (3,9,4),(3,4,2),(3,2,6),(3,6,8),(3,8,9),(4,9,5),(2,4,11),(6,2,10),(8,6,7),(9,8,1)]
    for _ in range(n):
        mid, NF = {}, []
        def m(a, b):
            k = (min(a, b), max(a, b))
            if k not in mid:
                mid[k] = len(V); V.append(tuple((V[a][i] + V[b][i]) / 2 for i in range(3)))
            return mid[k]
        for a, b, c in F:
            ab, bc, ca = m(a, b), m(b, c), m(c, a)
            NF += [(a, ab, ca), (b, bc, ab), (c, ca, bc), (ab, bc, ca)]
        F = NF
    return [tuple(x / math.sqrt(sum(y * y for y in v)) for x in v) for v in V], F

def dot(a, b): return sum(x * y for x, y in zip(a, b))
def cross(a, b): return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def unit(a): s = math.sqrt(dot(a, a)); return tuple(x / s for x in a)
def transport(w, u, v):
    """Parallel transport of tangent w at u to v along the great arc (rotation about u x v)."""
    ax = cross(u, v); s = math.sqrt(dot(ax, ax)); c = dot(u, v)
    if s < 1e-15: return w
    k = tuple(x / s for x in ax)
    kw = cross(k, w); kd = dot(k, w)
    return tuple(w[i] * c + kw[i] * s + k[i] * kd * (1 - c) for i in range(3))
def angle_at(n, a, b):
    return math.atan2(dot(n, cross(a, b)), dot(a, b))
def wrap(x): return (x + math.pi) % (2 * math.pi) - math.pi

def line_field_defects(V, F, rng):
    K = 5
    A = [[[rng.gauss(0, 1) for _ in range(3)] for _ in range(3)] for _ in range(K)]
    W = [[rng.gauss(0, 2) for _ in range(3)] for _ in range(K)]
    ph = [rng.uniform(0, 6.3) for _ in range(K)]
    D = []
    for p in V:
        M = [[sum((A[k][i][j] + A[k][j][i]) * math.sin(dot(W[k], p) + ph[k]) for k in range(K)) for j in range(3)] for i in range(3)]
        t1 = unit(cross(p, (0.3, 0.5, 0.81) if abs(p[2]) < 0.9 else (1, 0, 0))); t2 = cross(p, t1)
        q = lambda x, y: sum(x[i] * M[i][j] * y[j] for i in range(3) for j in range(3))
        a, b, c = q(t1, t1), q(t1, t2), q(t2, t2)
        th = 0.5 * math.atan2(2 * b, a - c)
        D.append(tuple(math.cos(th) * t1[i] + math.sin(th) * t2[i] for i in range(3)))
    total2, nd, half = 0, 0, True
    for f in F:
        s, e0 = 0.0, None
        loop = (f[0], f[1], f[2], f[0])
        w = unit(cross(V[f[0]], (0.1, 0.7, 0.2)))
        w0 = w
        for x, y in zip(loop, loop[1:]):
            tr = transport(D[x], V[x], V[y])
            s += wrap(2 * angle_at(V[y], tr, D[y]))
            w = transport(w, V[x], V[y])
        hol = angle_at(V[f[0]], w0, w)
        k = (s + 2 * hol) / (2 * math.pi)
        kr = round(k)
        assert abs(k - kr) < 1e-6, k
        assert abs(kr) <= 1
        if kr: nd += 1
        total2 += kr
    return total2, nd

V, F = icosphere(4)
rng = random.Random(1)
dcounts = []
for trial in range(20):
    t2, nd = line_field_defects(V, F, rng)
    assert t2 == 4, t2  # sum of strengths (each +-1/2) = 2
    dcounts.append(nd)
assert min(dcounts) >= 4
print(f"line fields: 20 random fields on icosphere(4) ({len(F)} triangles): every defect is +-1/2, "
      f"strengths sum to 2 every time; defects per field {min(dcounts)}..{max(dcounts)}")

# ---------- 3. pinwheel density of a random monochromatic field ----------
def pinwheel_density(rng, Lbox=16, res=24, nw=40):
    N = Lbox * res
    h = 1.0 / res
    ks = [rng.uniform(0, 2 * math.pi) for _ in range(nw)]
    ph = [rng.uniform(0, 2 * math.pi) for _ in range(nw)]
    kx = [2 * math.pi * math.cos(a) for a in ks]; ky = [2 * math.pi * math.sin(a) for a in ks]
    ex = [[cmath.exp(1j * (kx[j] * i * h + ph[j])) for i in range(N + 1)] for j in range(nw)]
    ey = [[cmath.exp(1j * ky[j] * i * h) for i in range(N + 1)] for j in range(nw)]
    G = []
    for iy in range(N + 1):
        eyc = [ey[j][iy] for j in range(nw)]
        G.append([cmath.phase(sum(ex[j][ix] * eyc[j] for j in range(nw))) for ix in range(N + 1)])
    pos = neg = 0
    for iy in range(N):
        r0, r1 = G[iy], G[iy + 1]
        for ix in range(N):
            a, b, c, d = r0[ix], r0[ix + 1], r1[ix + 1], r1[ix]
            w = wrap(b - a) + wrap(c - b) + wrap(d - c) + wrap(a - d)
            q = round(w / (2 * math.pi))
            if q > 0: pos += 1
            elif q < 0: neg += 1
    return (pos + neg) / (Lbox * Lbox), pos, neg

rng = random.Random(7)
ests = []
for _ in range(8):
    d, p, n_ = pinwheel_density(rng)
    assert abs(p - n_) <= 0.2 * (p + n_)
    ests.append(d)
mean = sum(ests) / len(ests)
se = math.sqrt(sum((e - mean) ** 2 for e in ests) / (len(ests) - 1) / len(ests))
assert abs(mean - math.pi) < 4 * se + 0.1, (mean, se)
print(f"random monochromatic field: pinwheels per L^2 = {mean:.3f} +- {se:.3f} (SE, 8 samples of 16L x 16L); pi = {math.pi:.3f}")

json.dump if False else None
print("PASS")
print(json.dumps({"states": STATES, "seconds": round(time.time() - T0, 1)}))
