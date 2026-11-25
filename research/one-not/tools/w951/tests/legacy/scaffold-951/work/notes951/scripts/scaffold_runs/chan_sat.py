# Exact-size one-NOT circuit SAT with a linear "channel" encoding (O(wires) clauses per gate per row), for larger n.
# Gate k reads wires A_k <= B_k (one-hot); op_k true = AND; the gate at position p is the NOT (reads A_p).
# Every output o_i is a gate wire computing OR(S_i) on all 2^n rows. The NOT is read by a later gate.
# A <= B allows op(w,w) padding, so exact size s covers every size <= s. SAT = counterexample to 951 if s < base.
#   python3 chan_sat.py SYSTEM S P_LO P_HI TIMEOUT        SYSTEM: grid43 | r0 | fano
import sys, time, threading, itertools
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
SYSTEMS = {
 'grid43': (12, [tuple(range(3*r, 3*r+3)) for r in range(4)] + [tuple(range(c, 12, 3)) for c in range(3)]),
 'r0': (8, [(0,1,2,3),(0,4,5),(1,4,6),(2,5,6),(3,4,7),(1,5,7)]),
 'c11': (8, [(0,1,2),(0,3,4),(1,5,6),(3,5,7),(2,4,6,7)]),
 'c12': (8, [(0,1,2),(0,3,4),(0,5,6),(1,3,5,7),(2,4,6,7)]),
 'fano': (7, [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)])}
name, s = sys.argv[1], int(sys.argv[2])
if name.startswith('core:'):   # core:INDEX = line INDEX (0-based) of cores.txt next to this script
    import os, json as _j
    _l = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cores.txt')).read().splitlines()[int(name[5:])].split(' ', 2)
    SYSTEMS[name] = (int(_l[0]), [tuple(x) for x in _j.loads(_l[2])])
plo, phi = int(sys.argv[3]), int(sys.argv[4]); TMO = float(sys.argv[5])
n, sets = SYSTEMS[name]; R = 1 << n
assert all(len(set(a) & set(b)) <= 1 for a, b in itertools.combinations(sets, 2))
def build(p):
    top = [0]; cl = []
    def nv(): top[0] += 1; return top[0]
    def exactly1(lits):
        enc = CardEnc.equals(lits=lits, bound=1, top_id=top[0], encoding=EncType.seqcounter); cl.extend(enc.clauses); top[0] = max(top[0], enc.nv)
    A, B, OP, V = {}, {}, {}, {}
    for k in range(s):
        m = n + k; A[k] = [nv() for _ in range(m)]; exactly1(A[k]); OP[k] = nv()
        if k != p:
            B[k] = [nv() for _ in range(m)]; exactly1(B[k])
            for i in range(m):
                for j in range(i): cl.append([-A[k][i], -B[k][j]])       # A <= B
        for r in range(R): V[(m, r)] = nv()
    def val(i, r): return ('T' if (r >> i) & 1 else 'F') if i < n else V[(i, r)]
    for k in range(s):
        m = n + k
        for r in range(R):
            g = V[(m, r)]; a = nv()
            for i in range(m):
                x = val(i, r)
                if isinstance(x, str): cl.append([-A[k][i], a if x == 'T' else -a])
                else: cl += [[-A[k][i], -x, a], [-A[k][i], x, -a]]
            if k == p: cl += [[g, a], [-g, -a]]; continue
            b = nv()
            for i in range(m):
                x = val(i, r)
                if isinstance(x, str): cl.append([-B[k][i], b if x == 'T' else -b])
                else: cl += [[-B[k][i], -x, b], [-B[k][i], x, -b]]
            o = OP[k]
            cl += [[-o, -g, a], [-o, -g, b], [-o, g, -a, -b], [o, g, -a], [o, g, -b], [o, -g, a, b]]
    # NOT read later
    cl.append([A[k][n + p] for k in range(p + 1, s)] + [B[k][n + p] for k in range(p + 1, s) if k != p])
    # outputs
    O = []
    for S in sets:
        o = [nv() for _ in range(s)]; exactly1(o); O.append(o)
        for k in range(s):
            for r in range(R):
                want = any((r >> v) & 1 for v in S); cl.append([-o[k], V[(n + k, r)] if want else -V[(n + k, r)]])
    return cl, A, B, OP, O
for p in range(plo, min(phi, s - 2) + 1):
    t0 = time.time(); cl, A, B, OP, O = build(p); sol = Cadical153(bootstrap_with=cl); tb = time.time() - t0
    tm = threading.Timer(TMO, sol.interrupt); tm.start(); r = sol.solve_limited(expect_interrupt=True); tm.cancel()
    res = 'TIMEOUT' if r is None else ('SAT' if r else 'UNSAT')
    line = f'{name} s={s} p={p} clauses={len(cl)} build={tb:.0f}s solve={time.time()-t0-tb:.0f}s {res}'
    if r:
        M = set(l for l in sol.get_model() if l > 0); gates = []
        for k in range(s):
            a = [i for i, v in enumerate(A[k]) if v in M][0]
            if k == p: gates.append(('not', a)); continue
            b = [i for i, v in enumerate(B[k]) if v in M][0]; gates.append(('and' if OP[k] in M else 'or', a, b))
        outs = [n + [k for k, v in enumerate(o) if v in M][0] for o in O]
        def ev(x):
            w = [(x >> i) & 1 for i in range(n)]
            for g in gates: w.append(1 - w[g[1]] if g[0] == 'not' else (w[g[1]] & w[g[2]] if g[0] == 'and' else w[g[1]] | w[g[2]]))
            return w
        ok = all(ev(x)[o] == int(any((x >> v) & 1 for v in S)) for x in range(R) for S, o in zip(sets, outs))
        line += f' gates={gates} outs={outs} recheck={ok}'
        try:   # independent re-check with tractability's shared package research/tools/w951 (branch pytools-951)
            sys.path.insert(0, '/home/user/pw-tools/tools'); from w951 import Circuit
            v = Circuit.from_dict({'n': n, 'sets': [list(S) for S in sets], 'gates': [list(g) for g in gates], 'outs': outs}).verify()
            line += f' w951_verify={v}'
        except Exception as e: line += f' w951_verify_error={e!r}'
    print(line, flush=True); sol.delete()
