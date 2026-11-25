#!/usr/bin/env python3
"""LIT2: a point program shorter than base on the affine plane AG(2, q), q = 2^m, without verticals.

Family W: the q^2 sets S_(a,b) = {(x, y) : y = a*x + b} over F_q (a, b in F_q), on the q^2 points.
Two sets meet in at most one point, |S| = q, base(W) = q^2 (q - 1).
Leaves (free): partial transversals of W (sets meeting every S_w in at most one point). Used here:
the vertical lines V_c = {(c, y)} and the single points {(x, y)}; the script checks that each leaf
used is a partial transversal.
Lines: X = A op B, op in {union, inter, diff}; A, B a leaf or an earlier line.
Point lemma (B6_thin_basis.md s2): no program of base - 1 lines has every S_w among its lines.
This script builds a program with every S_w among its lines, checks it twice (bitmasks while
building; frozensets, recomputed from the recorded program) and prints lines against base.

Idea (the weight <= 1 barrier: Wegener 1987 s6.13-6.15, Hiltgen-Paterson 1995, Tsukiji 1995): at
unit vectors a circuit only has to decode the index of the point. Y_t = points whose y has bit t;
L_c = points with <c, x> = 1 over F_2 (a union of verticals); D_(a,t) = Y_t xor L_(row t of a);
S_(a,b) is the atom of D_(a,0), ..., D_(a,m-1) with pattern b. About 2 q^2 + O(q m) lines.

Usage: python3 LIT2_point_counterexample.py [m ...]   (default 2 3 4)
"""
import sys

IRRED = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101}


def gf_mul(a, b, m):
    r = 0
    for i in range(m):
        if (b >> i) & 1:
            r ^= a << i
    for i in range(2 * m - 2, m - 1, -1):
        if (r >> i) & 1:
            r ^= IRRED[m] << (i - m)
    return r


def leaf_points(r, q):
    if r[0] == 'V':
        return [(r[1], y) for y in range(q)]
    return [(r[1], r[2])]


def build(m):
    q = 1 << m
    pt = lambda x, y: x * q + y
    prog, val = [], []

    def get(r):
        if r[0] == 'X':
            return val[r[1]]
        return sum(1 << pt(x, y) for x, y in leaf_points(r, q))

    def line(op, A, B):
        a, b = get(A), get(B)
        prog.append((op, A, B))
        val.append(a | b if op == 'u' else a & b if op == 'i' else a & ~b)
        return ('X', len(prog) - 1)

    def union(rs):
        r = rs[0]
        for s in rs[1:]:
            r = line('u', r, s)
        return r

    def xor(A, B):
        return line('u', line('d', A, B), line('d', B, A))

    def atoms(D, U):
        """all 2^k atoms of the sets D[0..k-1] inside U; returns dict pattern -> ref."""
        if len(D) == 1:
            return {1: D[0], 0: line('d', U, D[0])}
        h = len(D) // 2
        lo, hi = atoms(D[:h], U), atoms(D[h:], U)
        return {pl | (ph << h): line('i', rl, rh) for pl, rl in lo.items() for ph, rh in hi.items()}

    U = union([('V', c) for c in range(q)])
    H = [union([('P', x, d) for x in range(q)]) for d in range(q)]          # S_(0,d)
    Y = [union([H[d] for d in range(q) if (d >> t) & 1]) for t in range(m)]
    L = {}
    for c in range(1, q):
        vs = [('V', x) for x in range(q) if bin(c & x).count('1') & 1]
        L[c] = union(vs)
    out = {(0, d): H[d] for d in range(q)}
    for a in range(1, q):
        # bit t of a*x is <row_t, x> over F_2; row_t has bit j = bit t of a * 2^j
        D = []
        for t in range(m):
            row = sum(((gf_mul(a, 1 << j, m) >> t) & 1) << j for j in range(m))
            D.append(xor(Y[t], L[row]) if row else Y[t])
        for b, r in atoms(D, U).items():      # y xor a*x = b  <=>  y = a*x + b
            out[(a, b)] = r
    return q, prog, out, val


def check(m):
    q, prog, out, val = build(m)
    sets = {(a, b): frozenset((x, gf_mul(a, x, m) ^ b) for x in range(q))
            for a in range(q) for b in range(q)}
    fam = list(sets.values())
    assert all(len(s & t) <= 1 for i, s in enumerate(fam) for t in fam[:i])
    # second evaluation, independent of the bitmasks
    v = []
    for op, A, B in prog:
        ab = []
        for r in (A, B):
            if r[0] == 'X':
                assert r[1] < len(v)
                ab.append(v[r[1]])
            else:
                s = frozenset(leaf_points(r, q))
                assert all(len(s & t) <= 1 for t in fam), 'leaf is not a partial transversal'
                ab.append(s)
        a, b = ab
        v.append(a | b if op == 'u' else a & b if op == 'i' else a - b)
    assert all(val[i] == sum(1 << (x * q + y) for x, y in s) for i, s in enumerate(v))
    for k, s in sets.items():
        assert out[k][0] == 'X' and v[out[k][1]] == s, k
    assert len({out[k][1] for k in sets}) == q * q
    base = q * q * (q - 1)
    print(f"q={q} points={q*q} sets={q*q} base={base} lines={len(prog)} "
          f"{'BELOW base (point lemma fails here)' if len(prog) <= base - 1 else 'not below base'}")


if __name__ == '__main__':
    for m in [int(a) for a in sys.argv[1:]] or [2, 3, 4]:
        check(m)
