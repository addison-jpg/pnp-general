"""SAT encodings that generate one-NOT circuits for a set system (needs python-sat).

One builder replaces the three stacked ones of research/tools/l951_charging:
    build(n, sets, s, p)                       ov951.py:4-49        `build`
    build(..., live=True)                      live951.py:9-22      `build_live`
    build(..., live=True, clean=True)          clean951_scaffold.py:10-38 `build_clean`
The clause lists are identical to the originals (same variable numbering), so models, blocking
clauses and enumeration order carry over.

Encoding: s gates, gate p is the NOT; gate k selects inputs A_k, B_k among the earlier wires
(one-hot, A >= B as wire index for k != p) and an op bit (true = AND); W[(wire, row)] is the value
of a gate wire on row r (bit i of r = x_i); output selector O[i] is one-hot over the gate wires and
forces the selected wire to equal OR(S_i) on all rows; some later gate reads the NOT.
"""
from itertools import combinations

from .circuit import Circuit

__all__ = ['build', 'build_channel', 'decode', 'decode_circuit', 'block', 'enumerate_circuits']


def build(n, sets, s, p, blocks=(), live=False, clean=False, with_W=False):
    """Clauses for 'a circuit with s gates, NOT at gate p, computing OR(S_i) for every set'.
    live   the NOT lies in the cone of some output
    clean  (use with live) every gate is non-constant and differs from every other wire, inputs included
    Returns (clauses, SEL, O) (+ W if with_W): SEL[k] = (A, B, op) selector variables, O[i][w] output selectors."""
    from pysat.card import CardEnc
    rows = range(1 << n)
    top = [0]

    def nv():
        top[0] += 1
        return top[0]
    cl, W, SEL = [], {}, {}
    for k in range(s):
        m = n + k
        A = [nv() for _ in range(m)]
        B = [nv() for _ in range(m)]
        op = nv()
        for L in (A, B):
            enc = CardEnc.equals(lits=L, bound=1, top_id=top[0])
            cl += enc.clauses
            top[0] = max(top[0], enc.nv)
        SEL[k] = (A, B, op)
        if k != p:
            for i in range(m):
                for j in range(i):
                    cl.append([-A[i], -B[j]])
        for r in rows:
            g = nv()
            W[(m, r)] = g
            for i in range(m):
                wi = (r >> i & 1) if i < n else W[(i, r)]
                if k == p:                                   # NOT of the A-selected wire
                    if i < n:
                        cl.append([-A[i], -g if wi else g])
                    else:
                        cl += [[-A[i], -wi, -g], [-A[i], wi, g]]
                    continue
                for j in range(i, m):
                    wj = (r >> j & 1) if j < n else W[(j, r)]
                    for opv in (1, 0):
                        for va in (0, 1):
                            for vb in (0, 1):
                                c = [-A[i], -B[j], -op if opv else op]
                                skip = False
                                for w, vv, isin in ((wi, va, i < n), (wj, vb, j < n)):
                                    if isin:
                                        if w != vv:
                                            skip = True
                                    else:
                                        c.append(-w if vv else w)
                                if skip:
                                    continue
                                out = (va and vb) if opv else (va or vb)
                                c.append(g if out else -g)
                                cl.append(c)
    O = []
    for S in sets:
        o = [nv() for _ in range(n + s)]
        O.append(o)
        enc = CardEnc.equals(lits=o, bound=1, top_id=top[0])
        cl += enc.clauses
        top[0] = max(top[0], enc.nv)
        for w in range(n, n + s):
            for r in rows:
                t = any(r >> v & 1 for v in S)
                cl.append([-o[w], W[(w, r)] if t else -W[(w, r)]])
        for w in range(n):
            cl.append([-o[w]])
    cl.append([SEL[k][0][n + p] for k in range(p + 1, s)] + [SEL[k][1][n + p] for k in range(p + 1, s)])
    cl += list(blocks)
    _extras(cl, SEL, O, W, n, sets, s, p, live, clean)
    return (cl, SEL, O, W) if with_W else (cl, SEL, O)


def _extras(cl, SEL, O, W, n, sets, s, p, live, clean):
    """The `live` / `clean` clauses (shared by `build` and `build_channel`); appended to cl."""
    top = [0]

    def nv():
        top[0] += 1
        return top[0]
    if live or clean:
        top[0] = max(abs(l) for c in cl for l in c)
    if live:                                                 # c[k] <-> wire n+k is an output or read by a live gate
        c = [nv() for _ in range(s)]
        for k in range(s):
            w = n + k
            reasons = [O[i][w] for i in range(len(sets))]
            for j in range(k + 1, s):
                A, B, _ = SEL[j]
                u = nv()
                reasons.append(u)
                cl.append([-u, c[j]])
                cl.append([-u, A[w], B[w]] if j != p else [-u, A[w]])
            cl.append([-c[k]] + reasons)
        cl.append([c[p]])
    if clean:
        R = 1 << n
        for k in range(s):
            cl.append([W[(n + k, r)] for r in range(R)])
            cl.append([-W[(n + k, r)] for r in range(R)])
        for k in range(s):
            for i in range(n):
                cl.append([(-W[(n + k, r)] if (r >> i) & 1 else W[(n + k, r)]) for r in range(R)])
        for k, l in combinations(range(s), 2):
            ds = []
            for r in range(R):
                d = nv()
                ds.append(d)
                a, b = W[(n + k, r)], W[(n + l, r)]
                cl += [[-d, a, b], [-d, -a, -b]]
            cl.append(ds)


def build_channel(n, sets, s, p, blocks=(), live=False, clean=False, with_W=False):
    """Same instance / sets / output conventions as `build`, with the LINEAR channel encoding (scaffold-951
    `scaffold_runs/chan_sat.py` `build`): per gate and truth-table row one value variable per gate input,
    selector A[k][i] -> (a_r == W_i,r), so O(wires) clauses per gate and row instead of O(wires^2 * 8).
    Gate k reads wires A_k <= B_k (one-hot), so exact size s also covers every size <= s (padding op(w, w)).
    The clause list starts with exactly the clauses of chan_sat.py (same variable numbering); output
    selectors O[i] have the same length n+s as in `build` (the n input entries are forced false, their
    variables and unit clauses come after the legacy part). SEL[p] = (A, A, op): the NOT has no B.
    Returns (clauses, SEL, O) (+ W if with_W); decode / block / enumerate_circuits work unchanged."""
    from pysat.card import CardEnc, EncType
    rows = range(1 << n)
    top = [0]
    cl = []

    def nv():
        top[0] += 1
        return top[0]

    def exactly1(lits):
        enc = CardEnc.equals(lits=lits, bound=1, top_id=top[0], encoding=EncType.seqcounter)
        cl.extend(enc.clauses)
        top[0] = max(top[0], enc.nv)
    SEL, W = {}, {}
    for k in range(s):
        m = n + k
        A = [nv() for _ in range(m)]
        exactly1(A)
        op = nv()
        if k != p:
            B = [nv() for _ in range(m)]
            exactly1(B)
            for i in range(m):
                for j in range(i):
                    cl.append([-A[i], -B[j]])                 # A <= B
        else:
            B = A
        SEL[k] = (A, B, op)
        for r in rows:
            W[(m, r)] = nv()

    def chan(sel, r, a):                                       # a == value of the wire selected by sel, on row r
        for i, v in enumerate(sel):
            if i < n:
                cl.append([-v, a if r >> i & 1 else -a])
            else:
                x = W[(i, r)]
                cl.extend([[-v, -x, a], [-v, x, -a]])
    for k in range(s):
        A, B, op = SEL[k]
        for r in rows:
            g = W[(n + k, r)]
            a = nv()
            chan(A, r, a)
            if k == p:
                cl += [[g, a], [-g, -a]]
                continue
            b = nv()
            chan(B, r, b)
            cl += [[-op, -g, a], [-op, -g, b], [-op, g, -a, -b], [op, g, -a], [op, g, -b], [op, -g, a, b]]
    cl.append([SEL[k][0][n + p] for k in range(p + 1, s)] + [SEL[k][1][n + p] for k in range(p + 1, s)])
    O = []
    for S in sets:
        o = [nv() for _ in range(s)]
        exactly1(o)
        O.append(o)
        for k in range(s):
            for r in rows:
                cl.append([-o[k], W[(n + k, r)] if any(r >> v & 1 for v in S) else -W[(n + k, r)]])
    for i in range(len(sets)):                                # input entries of O (never selectable), as in `build`
        z = [nv() for _ in range(n)]
        cl += [[-x] for x in z]
        O[i] = z + O[i]
    cl += list(blocks)
    _extras(cl, SEL, O, W, n, sets, s, p, live, clean)
    return (cl, SEL, O, W) if with_W else (cl, SEL, O)


def decode(model, n, s, p, SEL, O):
    """(gates, outs) from a model: gates are (op, a, b) triples, NOT as ('not', a, a) (ov951.py:50-57)."""
    M = set(x for x in model if x > 0)
    gates = []
    for k in range(s):
        A, B, op = SEL[k]
        a = [i for i, v in enumerate(A) if v in M][0]
        if k == p:
            gates.append(('not', a, a))
            continue
        b = [i for i, v in enumerate(B) if v in M][0]
        gates.append(('and' if op in M else 'or', a, b))
    outs = [[w for w, v in enumerate(o) if v in M][0] for o in O]
    return gates, outs


def decode_circuit(model, n, sets, s, p, SEL, O):
    """The model as a `Circuit`."""
    gates, outs = decode(model, n, s, p, SEL, O)
    return Circuit(n, gates, sets, outs)


def block(model, gates, outs, s, p, SEL, O, ops=True, with_outs=False):
    """Blocking clause for the decoded circuit: forbids the same input selection (and, with ops, the same
    AND/OR choice; with with_outs, the same outputs). ops=False is the clause of restr951.py:47 / ov951;
    ops=True that of scaffold_opus/rules.py:72-73; with_outs=True adds gen_clean.py:52."""
    pos = set(l for l in model if l > 0)
    b = [-SEL[k][0][gates[k][1]] for k in range(s)] + [-SEL[k][1][gates[k][2]] for k in range(s) if k != p]
    if ops:
        b += [(-SEL[k][2] if SEL[k][2] in pos else SEL[k][2]) for k in range(s) if k != p]
    if with_outs:
        b += [-O[i][outs[i]] for i in range(len(outs))]
    return b


def enumerate_circuits(n, sets, s, p, limit=None, live=True, clean=False, ops=True, solver='cadical153',
                      encoding='quadratic'):
    """Yield circuits with s gates and the NOT at gate p (blocking each one found).
    encoding: 'quadratic' (`build`) or 'channel' (`build_channel`; size <= s via padding)."""
    from pysat.solvers import Solver
    cl, SEL, O = {'quadratic': build, 'channel': build_channel}[encoding](n, sets, s, p, live=live, clean=clean)
    with Solver(name=solver, bootstrap_with=cl) as sol:
        k = 0
        while (limit is None or k < limit) and sol.solve():
            model = sol.get_model()
            gates, outs = decode(model, n, s, p, SEL, O)
            sol.add_clause(block(model, gates, outs, s, p, SEL, O, ops=ops))
            k += 1
            yield Circuit(n, gates, sets, outs)
