"""Fable W: explicit MONOTONE circuit for the line-ORs of the affine plane AG(2, q^2) that is correct on every
input of Hamming weight <= k (default k = 2), and smaller than base = sum(|S|-1) once q is large enough.

Points V = F_p^2, p = q^2 (F_p = F_q[w]/(w^2 - nu)); n = q^4.  Lines: y = a x + b (a, b in F_p) and x = b.
pi_a(x, y) = y - a x, pi_inf(x, y) = x: the 'coordinate' of a point in direction a.

Construction (hub direction h, spoke directions j_1..j_S, S = k(k-1)+1, T = k^2 + 1 <= q evaluation points):
 1. line rails of the S+1 special directions: plain ORs (these are outputs too).
 2. cylinder rails C[i, f, d] = OR of the lines (i, c) with f(c) = d, f a nonzero F_q-functional on F_p.
 3. for each other slope a, t < T, d in F_q, spoke j: sloppy hyperplane rail
        H[j] = OR_{d1} C[h, f1, d1] AND C[j, f2, d - d1],   psi_t o pi_a = f1 o pi_h + f2 o pi_j,
    psi_t(c0 + c1 w) = c0 + c1 t  (Reed-Solomon functionals);   G[a, t, d] = AND_j H[j].
 4. line (a, b) = AND_t G[a, t, psi_t(b)].
Usage: python3 plane2.py q [k] [--verify] [--w3 samples]
"""
import sys, itertools, random
import numpy as np


class Field2:
    """F_{q^2} as pairs over F_q (q prime), w^2 = nu."""
    def __init__(s, q):
        s.q = q
        s.nu = next(c for c in range(2, q) if all((x * x - c) % q for x in range(q)))
        s.p = q * q
        s.els = [(a, b) for a in range(q) for b in range(q)]
        s.idx = {e: i for i, e in enumerate(s.els)}

    def add(s, x, y): return ((x[0] + y[0]) % s.q, (x[1] + y[1]) % s.q)
    def sub(s, x, y): return ((x[0] - y[0]) % s.q, (x[1] - y[1]) % s.q)
    def mul(s, x, y):
        return ((x[0] * y[0] + s.nu * x[1] * y[1]) % s.q, (x[0] * y[1] + x[1] * y[0]) % s.q)


class Circ:
    def __init__(s, n):
        s.n = n; s.g = []          # gates: (op, a, b), op 0 = OR, 1 = AND
        s.memo = {}

    def gate(s, op, a, b):
        if a == b: return a
        key = (op, min(a, b), max(a, b))
        if key in s.memo: return s.memo[key]
        s.g.append(key); s.memo[key] = s.n + len(s.g) - 1
        return s.memo[key]

    def many(s, op, xs):
        xs = list(xs); r = xs[0]
        for x in xs[1:]: r = s.gate(op, r, x)
        return r


def solve_mod(M, rhs, q):
    """solve z M = rhs over F_q (M square, invertible), row vector z."""
    m = len(M)
    A = [[M[r][c] for r in range(m)] + [rhs[c]] for c in range(m)]   # transpose system M^T z^T = rhs^T
    for c in range(m):
        piv = next(r for r in range(c, m) if A[r][c] % q)
        A[c], A[piv] = A[piv], A[c]
        inv = pow(A[c][c], q - 2, q)
        A[c] = [(v * inv) % q for v in A[c]]
        for r in range(m):
            if r != c and A[r][c]:
                f = A[r][c]
                A[r] = [(v - f * u) % q for v, u in zip(A[r], A[c])]
    return [A[r][m] for r in range(m)]


def build(q, k=2, T=None):
    F = Field2(q); p = F.p; n = p * p
    S = k * (k - 1) + 1
    T = T or (k * k + 1)
    assert T <= q, "need T <= q for Reed-Solomon functionals"
    pts = [(x, y) for x in F.els for y in F.els]
    pid = {u: i for i, u in enumerate(pts)}
    INF = 'inf'
    dirs = [INF] + F.els

    def pi(a, u):
        return u[0] if a == INF else F.sub(u[1], F.mul(a, u[0]))

    def pimat(a):
        """2x4 matrix over F_q of pi_a in coordinates (x0, x1, y0, y1)."""
        cols = []
        for e in range(4):
            v = [0, 0, 0, 0]; v[e] = 1
            cols.append(pi(a, ((v[0], v[1]), (v[2], v[3]))))
        return [[cols[e][r] for e in range(4)] for r in range(2)]

    C = Circ(n)
    lines = {}                      # (dir, b) -> point list
    for a in dirs:
        for u in pts:
            lines.setdefault((a, pi(a, u)), []).append(pid[u])
    special = [INF] + F.els[:S]     # hub = INF, spokes = first S slopes
    hub, spokes = special[0], special[1:]
    out = {}
    for a in special:
        for b in F.els:
            out[(a, b)] = C.many(0, lines[(a, b)])
    n_special = len(C.g)
    cyl = {}

    def cylinder(i, f, d):
        # normalise (f, d) projectively
        lead = f[0] if f[0] else f[1]
        inv = pow(lead, q - 2, q)
        f = ((f[0] * inv) % q, (f[1] * inv) % q); d = (d * inv) % q
        key = (i, f, d)
        if key not in cyl:
            cyl[key] = C.many(0, [out[(i, c)] for c in F.els if (f[0] * c[0] + f[1] * c[1]) % q == d])
        return cyl[key]

    stats = dict(special=n_special)
    for a in dirs:
        if a in special: continue
        Ma = pimat(a)
        G = {}
        for t in range(T):
            phi = [(Ma[0][e] + t * Ma[1][e]) % q for e in range(4)]      # psi_t o pi_a
            hs = {d: [] for d in range(q)}
            for j in spokes:
                M = pimat(hub) + pimat(j)                                # 4x4, rows = coordinate functionals
                z = solve_mod(M, phi, q)
                f1, f2 = (z[0], z[1]), (z[2], z[3])
                assert f1 != (0, 0) and f2 != (0, 0)
                for d in range(q):
                    terms = [C.gate(1, cylinder(hub, f1, d1), cylinder(j, f2, (d - d1) % q)) for d1 in range(q)]
                    hs[d].append(C.many(0, terms))
            for d in range(q):
                G[(t, d)] = C.many(1, hs[d])
        for b in F.els:
            out[(a, b)] = C.many(1, [G[(t, (b[0] + b[1] * t) % q)] for t in range(T)])
    base = sum(len(v) - 1 for v in lines.values())
    stats.update(n=n, m=len(lines), base=base, size=len(C.g), cyl=len(cyl), ands=sum(1 for g in C.g if g[0]))
    return C, lines, out, stats


def evaluate(C, rows_by_var, nrows, outs):
    """bit-parallel evaluation with freeing; rows_by_var[v] = packed uint8 array."""
    n = C.n
    last = {}
    for gi, (op, a, b) in enumerate(C.g):
        last[a] = gi; last[b] = gi
    keep = set(outs)
    val = {}
    def get(i):
        return rows_by_var[i] if i < n else val[i]
    for gi, (op, a, b) in enumerate(C.g):
        x, y = get(a), get(b)
        val[n + gi] = (x & y) if op else (x | y)
        for c in (a, b):
            if c >= n and last[c] == gi and c not in keep:
                del val[c]
    return val


def verify_w2(C, lines, out):
    n = C.n
    iu, ju = np.triu_indices(n, 1)
    nrows = 1 + n + len(iu)
    print("rows (weight <= 2):", nrows, flush=True)
    rows = []
    base_idx = 1 + n
    order_i = np.argsort(iu, kind='stable'); order_j = np.argsort(ju, kind='stable')
    ci = np.searchsorted(iu[order_i], np.arange(n + 1)); cj = np.searchsorted(ju[order_j], np.arange(n + 1))
    for v in range(n):
        bits = np.zeros(nrows, dtype=bool)
        bits[1 + v] = True
        bits[base_idx + order_i[ci[v]:ci[v + 1]]] = True
        bits[base_idx + order_j[cj[v]:cj[v + 1]]] = True
        rows.append(np.packbits(bits))
    outs = set(out.values())
    val = evaluate(C, rows, nrows, outs)
    bad = 0
    for key, node in out.items():
        exp = rows[lines[key][0]].copy()
        for v in lines[key][1:]:
            exp |= rows[v]
        got = val[node] if node >= n else rows[node]
        if not np.array_equal(exp, got):
            bad += 1
    return bad


def sample_w(C, lines, out, w, samples, seed=1):
    n = C.n; rnd = random.Random(seed)
    X = np.zeros((n, samples), dtype=bool)
    for s_ in range(samples):
        for v in rnd.sample(range(n), w):
            X[v, s_] = True
    rows = [np.packbits(X[v]) for v in range(n)]
    val = evaluate(C, rows, samples, set(out.values()))
    wrong = 0; total = 0
    for key, node in out.items():
        exp = rows[lines[key][0]].copy()
        for v in lines[key][1:]:
            exp |= rows[v]
        got = val[node] if node >= n else rows[node]
        diff = np.unpackbits(exp ^ got)[:samples]
        wrong += int(diff.sum()); total += samples
        assert not np.any(np.unpackbits(exp & ~got)[:samples]), "monotone under-approximation?!"
    return wrong, total


if __name__ == '__main__':
    q = int(sys.argv[1]); k = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 2
    C, lines, out, st = build(q, k)
    print(st, "saving" if st['size'] < st['base'] else "no saving", st['base'] - st['size'], flush=True)
    if '--verify' in sys.argv:
        print("bad outputs on weight<=2:", verify_w2(C, lines, out))
    if '--w3' in sys.argv:
        s_ = int(sys.argv[sys.argv.index('--w3') + 1])
        for w in (1, 2, 3, 4, 6):
            print("weight", w, "wrong output bits / total:", sample_w(C, lines, out, w, s_))
