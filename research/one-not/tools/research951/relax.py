"""Relaxed 951 SAT: is there a circuit of <= s fan-in-2 AND/OR gates plus <= 1 NOT that computes
OR(S_w) correctly on every input in a ROW SET R (not necessarily all 2^n inputs)?
rows modes: 'w<=k' (all inputs of weight <= k), 'all', or an explicit list of ints.
Usage: python3 relax.py '<json sets>' n s mode [--mono]"""
import sys, json, itertools
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType


def rowset(n, mode):
    if mode == 'all':
        return list(range(1 << n))
    if mode.startswith('w<='):
        k = int(mode[3:])
        return [r for r in range(1 << n) if bin(r).count('1') <= k]
    raise ValueError(mode)


def solve(n, sets, s, rows, mono=False, p_list=None, want_model=False):
    """returns (sat?, circuit or None). NOT position p ranges over p_list (default all); mono => no NOT."""
    ps = [None] if mono else (p_list if p_list is not None else list(range(s)))
    for p in ps:
        top = [0]
        def nv():
            top[0] += 1
            return top[0]
        cl = []
        W = {}
        def val(i, r):  # literal or bool
            return (r >> i & 1) if i < n else W[(i, r)]
        SEL = {}
        for k in range(s):
            m = n + k
            A = [nv() for _ in range(m)]
            B = [nv() for _ in range(m)]
            op = nv()
            SEL[k] = (A, B, op)
            for L in ((A,) if k == p else (A, B)):
                enc = CardEnc.equals(lits=L, bound=1, top_id=top[0], encoding=EncType.seqcounter)
                cl += enc.clauses; top[0] = max(top[0], enc.nv)
            if k != p:
                for i in range(m):           # A <= B
                    for j in range(i):
                        cl.append([-A[i], -B[j]])
            for r in rows:
                g = nv(); W[(m, r)] = g
                a = nv(); b = nv() if k != p else None
                for i in range(m):
                    v = val(i, r)
                    if isinstance(v, int) and i < n:
                        cl.append([-A[i], a if v else -a])
                        if b: cl.append([-B[i], b if v else -b])
                    else:
                        cl += [[-A[i], -v, a], [-A[i], v, -a]]
                        if b: cl += [[-B[i], -v, b], [-B[i], v, -b]]
                if k == p:
                    cl += [[a, g], [-a, -g]]
                else:
                    # op true = AND
                    cl += [[-op, -g, a], [-op, -g, b], [-op, g, -a, -b],
                           [op, g, -a], [op, g, -b], [op, -g, a, b]]
        for S in sets:
            o = [nv() for _ in range(s)]
            enc = CardEnc.equals(lits=o, bound=1, top_id=top[0], encoding=EncType.seqcounter)
            cl += enc.clauses; top[0] = max(top[0], enc.nv)
            for k in range(s):
                for r in rows:
                    t = any(r >> v & 1 for v in S)
                    cl.append([-o[k], W[(n + k, r)] if t else -W[(n + k, r)]])
        with Cadical153(bootstrap_with=cl) as sv:
            if sv.solve():
                if not want_model:
                    return True, p
                mdl = set(l for l in sv.get_model() if l > 0)
                circ = []
                for k in range(s):
                    A, B, op = SEL[k]
                    ia = next(i for i, x in enumerate(A) if x in mdl)
                    if k == p:
                        circ.append(('not', ia)); continue
                    ib = next(i for i, x in enumerate(B) if x in mdl)
                    circ.append(('and' if op in mdl else 'or', ia, ib))
                return True, (p, circ)
    return False, None


def evalc(n, circ, x):
    w = [(x >> i) & 1 for i in range(n)]
    for g in circ:
        if g[0] == 'not': w.append(1 - w[g[1]])
        elif g[0] == 'and': w.append(w[g[1]] & w[g[2]])
        else: w.append(w[g[1]] | w[g[2]])
    return w


if __name__ == '__main__':
    sets = json.loads(sys.argv[1]); n = int(sys.argv[2]); s = int(sys.argv[3]); mode = sys.argv[4]
    mono = '--mono' in sys.argv
    print(solve(n, sets, s, rowset(n, mode), mono=mono, want_model=True))
