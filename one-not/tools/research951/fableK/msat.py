"""Monotone-circuit SAT for PARTIAL multi-output functions (Sokolov: = dag-like KW game size).
solve(n, s, specs): is there a circuit of s fan-in-2 AND/OR gates over inputs 0..n-1 such that for each spec
(ones, zeros) some wire (input or gate) is 1 on every row in ones and 0 on every row in zeros?  Rows are ints (bitmasks).
Only minimal ones / maximal zeros are kept (the circuit is monotone by construction).
Returns (sat, circuit, outs): circuit = list of ('and'|'or', i, j); outs = wire index per spec."""
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType


def minimal(rows):
    rows = sorted(set(rows), key=lambda r: bin(r).count('1'))
    out = []
    for r in rows:
        if not any(m & r == m for m in out):
            out.append(r)
    return out


def maximal(rows):
    rows = sorted(set(rows), key=lambda r: -bin(r).count('1'))
    out = []
    for r in rows:
        if not any(m & r == r for m in out):
            out.append(r)
    return out


def solve(n, s, specs, want_model=True, time_limit=None):
    specs = [(minimal(o), maximal(z)) for o, z in specs]
    for o, z in specs:
        for a in o:
            for b in z:
                if a & b == a:
                    return False, None, None      # inconsistent
    rows = sorted(set(r for o, z in specs for r in o + z))
    top = [0]
    def nv():
        top[0] += 1
        return top[0]
    cl = []
    W = {}
    def exact1(L):
        enc = CardEnc.equals(lits=L, bound=1, top_id=top[0], encoding=EncType.seqcounter)
        cl.extend(enc.clauses); top[0] = max(top[0], enc.nv)
    SEL = []
    for k in range(s):
        m = n + k
        A = [nv() for _ in range(m)]
        B = [nv() for _ in range(m)]
        op = nv()
        SEL.append((A, B, op))
        exact1(A); exact1(B)
        for i in range(m):               # A index < B index
            for j in range(i + 1):
                cl.append([-A[i], -B[j]])
        for r in rows:
            g = nv(); W[(m, r)] = g
            a = nv(); b = nv()
            for i in range(m):
                if i < n:
                    v = r >> i & 1
                    cl.append([-A[i], a if v else -a])
                    cl.append([-B[i], b if v else -b])
                else:
                    v = W[(i, r)]
                    cl += [[-A[i], -v, a], [-A[i], v, -a], [-B[i], -v, b], [-B[i], v, -b]]
            cl += [[-op, -g, a], [-op, -g, b], [-op, g, -a, -b],
                   [op, g, -a], [op, g, -b], [op, -g, a, b]]
    OS = []
    for (o, z) in specs:
        sel = [nv() for _ in range(n + s)]
        OS.append(sel)
        exact1(sel)
        for i in range(n + s):
            if i < n:
                if any(not (r >> i & 1) for r in o) or any(r >> i & 1 for r in z):
                    cl.append([-sel[i]])
            else:
                for r in o: cl.append([-sel[i], W[(i, r)]])
                for r in z: cl.append([-sel[i], -W[(i, r)]])
    # every gate is used: an output or an input of a later gate
    for k in range(s):
        m = n + k
        use = [sel[m] for sel in OS]
        for k2 in range(k + 1, s):
            use += [SEL[k2][0][m], SEL[k2][1][m]]
        cl.append(use)
    with Cadical153(bootstrap_with=cl) as sv:
        if not sv.solve():
            return False, None, None
        if not want_model:
            return True, None, None
        mdl = set(l for l in sv.get_model() if l > 0)
        circ = []
        for k in range(s):
            A, B, op = SEL[k]
            ia = next(i for i, x in enumerate(A) if x in mdl)
            ib = next(i for i, x in enumerate(B) if x in mdl)
            circ.append(('and' if op in mdl else 'or', ia, ib))
        outs = [next(i for i, x in enumerate(sel) if x in mdl) for sel in OS]
        return True, circ, outs


def opt(n, specs, lo=0, hi=40):
    """smallest s with a circuit (linear search upward from lo)."""
    for s in range(lo, hi + 1):
        ok, c, o = solve(n, s, specs)
        if ok:
            return s, c, o
    return None, None, None


def evalc(n, circ, x):
    w = [(x >> i) & 1 for i in range(n)]
    for g in circ:
        w.append(w[g[1]] & w[g[2]] if g[0] == 'and' else w[g[1]] | w[g[2]])
    return w
