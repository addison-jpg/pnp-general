"""Guided SAT for one-NOT circuits of a (1,1)-disjoint system under a FIXED scenario (sigma=1, B, class vector).
Sound constraints only (each is a proved property of a minimal counterexample, see NOTES.md):
 canonical gate order, live, syntactic clean, h(0)=0, >=2 AND, N2/rule p reader caps, absorbing lemma for single readers,
 tight => OR readers only, scenario/class reader counts.
usage: python3 enc.py RANK SCEN_INDEX [timeout_s] [extra]"""
import sys, json, time, itertools
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

class Enc:
    def __init__(s, n, sets, ng):
        s.n, s.sets, s.ng = n, [sorted(S) for S in sets], ng
        s.top = 0; s.cl = []
        s.build()
    def nv(s):
        s.top += 1; return s.top
    def add(s, c): s.cl.append(c)
    def card(s, lits, lo=None, hi=None, cond=None):
        """lo <= sum(lits) <= hi, optionally only if literal cond holds"""
        for kind, b in (('atleast', lo), ('atmost', hi)):
            if b is None: continue
            if kind == 'atleast' and b <= 0: continue
            if kind == 'atmost' and b >= len(lits): continue
            if kind == 'atleast' and b > len(lits):
                s.add([] if cond is None else [-cond]); continue
            e = getattr(CardEnc, kind)(lits=lits, bound=b, top_id=s.top, encoding=EncType.seqcounter)
            s.top = max(s.top, e.nv)
            for c in e.clauses: s.add(c if cond is None else c + [-cond])
    def build(s):
        n, ng = s.n, s.ng; R = 1 << n
        s.A, s.B, s.AND, s.NOT, s.W = [], [], [], [], []
        for k in range(ng):
            m = n + k
            A = [s.nv() for _ in range(m)]; B = [s.nv() for _ in range(m)]
            s.A.append(A); s.B.append(B); s.AND.append(s.nv()); s.NOT.append(s.nv())
            s.card(A, 1, 1); s.card(B, 1, 1)
            s.add([-s.AND[k], -s.NOT[k]])
            for i in range(m):
                s.add([-s.NOT[k], -A[i], B[i]])            # NOT: B = A
                s.add([s.NOT[k], -A[i], -B[i]])            # else A != B
                for j in range(i + 1, m):
                    s.add([-A[i], -B[j]])                  # A >= B
        s.card(s.NOT, 1, 1); s.card(s.AND, 2, None)
        # canonical order: (A,B) nondecreasing; equal pair => OR then AND
        for k in range(ng - 1):
            m = n + k
            A, B, A2, B2 = s.A[k], s.B[k], s.A[k + 1], s.B[k + 1]
            for j in range(m):
                for i in range(j): s.add([-A[j], -A2[i]])
                e = s.nv(); s.add([-A[j], -A2[j], e])      # e: same A
                for b in range(j + 1):
                    for b2 in range(b): s.add([-A[j], -A2[j], -B[b], -B2[b2]])
                    s.add([-A[j], -A2[j], -B[b], -B2[b], -s.AND[k]])
                    s.add([-A[j], -A2[j], -B[b], -B2[b], -s.NOT[k]])
                    s.add([-A[j], -A2[j], -B[b], -B2[b], s.AND[k + 1], s.NOT[k+1]])
        # values
        for k in range(ng):
            m = n + k; row = []
            for r in range(R):
                a, b, g = s.nv(), s.nv(), s.nv(); row.append(g)
                for i in range(m):
                    if i < n:
                        bit = r >> i & 1
                        s.add([-s.A[k][i], a if bit else -a]); s.add([-s.B[k][i], b if bit else -b])
                    else:
                        w = s.W[i - n][r]
                        s.add([-s.A[k][i], -a, w]); s.add([-s.A[k][i], a, -w])
                        s.add([-s.B[k][i], -b, w]); s.add([-s.B[k][i], b, -w])
                AN, NO = s.AND[k], s.NOT[k]
                s.add([-NO, -a, -g]); s.add([-NO, a, g])
                s.add([-AN, -a, -b, g]); s.add([-AN, a, -g]); s.add([-AN, b, -g])
                s.add([AN, NO, a, b, -g]); s.add([AN, NO, -a, g]); s.add([AN, NO, -b, g])
            s.W.append(row)
            s.add([-s.NOT[k], row[0]])                     # h(0)=0
        # outputs
        s.O = []
        for S in s.sets:
            o = [s.nv() for _ in range(ng)]; s.O.append(o); s.card(o, 1, 1)
            for k in range(ng):
                s.add([-o[k], -s.NOT[k]])
                for r in range(R):
                    t = any(r >> v & 1 for v in S)
                    s.add([-o[k], s.W[k][r] if t else -s.W[k][r]])
        # live: every gate read later or output
        for k in range(ng):
            w = n + k
            s.add([o[k] for o in s.O] + [s.A[j][w] for j in range(k + 1, ng)] + [s.B[j][w] for j in range(k + 1, ng)])
        # reader literals
        s.rd = [[None] * n for _ in range(ng)]
        for k in range(ng):
            for u in range(n):
                x = s.nv(); s.rd[k][u] = x
                s.add([-x, s.A[k][u], s.B[k][u]]); s.add([x, -s.A[k][u]]); s.add([x, -s.B[k][u]])
    def scenario(s, Bset, cls):
        """cls: dict point -> 'U','T','M','S' for B points"""
        n, ng, sets = s.n, s.ng, s.sets
        d = [sum(u in S for S in sets) for u in range(n)]
        l = [sum(u in S and len(S) >= 3 for S in sets) for u in range(n)]
        P = [sorted(set(v for S in sets if len(S) == 2 and u in S for v in S) - {u}) for u in range(n)]
        s.pg = {}
        for u in range(n):
            for w in P[u]:
                if w < u:
                    for k in range(ng):
                        x = s.nv(); s.pg[(k, w, u)] = x
                        s.add([-x, s.A[k][u]]); s.add([-x, s.B[k][w]]); s.add([-x, -s.AND[k]])
                        s.add([x, -s.A[k][u], -s.B[k][w], s.AND[k]])
        s.np = [[None] * n for _ in range(ng)]
        for k in range(ng):
            for u in range(n):
                x = s.nv(); s.np[k][u] = x
                pgs = [s.pg[(k, min(u, w), max(u, w))] for w in P[u]]
                s.add([-x, s.rd[k][u]])
                for q in pgs: s.add([-x, -q])
                s.add([x, -s.rd[k][u]] + pgs)
        for u in range(n):
            rds = [s.rd[k][u] for k in range(ng)]; nps = [s.np[k][u] for k in range(ng)]
            s.card(rds, None, d[u] - 1)                    # N2
            s.card(nps, None, l[u] - 1)                    # rule p
            # tight (readers = d-1) => only OR readers
            t = s.nv(); s.card(rds, None, d[u] - 2, cond=t)
            for k in range(ng):
                s.add([-s.rd[k][u], -s.AND[k], t]); s.add([-s.rd[k][u], -s.NOT[k], t])
            if u not in Bset:
                s.card(rds, 1, 1)
                for k in range(ng):                        # absorbing lemma: reader is x_u o gate, not NOT
                    s.add([-s.rd[k][u], -s.NOT[k]])
                    for i in range(n):
                        if i != u:
                            s.add([-s.rd[k][u], -s.A[k][i]]); s.add([-s.rd[k][u], -s.B[k][i]])
                    if l[u] == 2 and True: s.add([-s.rd[k][u], -s.AND[k]])   # (T2) p-tight V1: OR-type (l = sigma+1)
            else:
                s.card(rds, 2, None)
                c = cls.get(u)
                if c in ('U', 'S'):
                    s.card(nps, 1, 1)
                    s.card([s.pg[(k, min(u, w), max(u, w))] for k in range(ng) for w in P[u] if w in Bset], 1, None)
                    for k in range(ng):
                        s.add([-s.np[k][u], -s.NOT[k]])    # h_t != N
                        if c == 'U':
                            s.add([-s.np[k][u], -s.AND[k]])
                            for i in range(n):
                                if i != u: s.add([-s.np[k][u], -s.A[k][i]]); s.add([-s.np[k][u], -s.B[k][i]])
                elif c == 'T':
                    s.card(nps, l[u] - 1, l[u] - 1)
                elif c == 'M':
                    s.card(nps, 2, l[u] - 2)
            for w in P[u]:                                 # P2: no pair-gate at a V1 point
                if u not in Bset or w not in Bset:
                    for k in range(ng): s.add([-s.pg[(k, min(u, w), max(u, w))]])
    def implied(s, Bset, cls):
        """sound implied constraints: monotone prefix, nonconstant gates, AL for V1 readers, (U3) for class U/S"""
        n, ng, sets = s.n, s.ng, s.sets; R = 1 << n
        P = [sorted(set(v for S in sets if len(S) == 2 and u in S for v in S) - {u}) for u in range(n)]
        bef = []
        for k in range(ng):
            b = s.nv(); bef.append(b)                      # b: no NOT among gates 0..k
            s.add([-b, -s.NOT[k]])
            if k: s.add([-b, bef[k - 1]]); s.add([b, -bef[k - 1], s.NOT[k]])
            else: s.add([b, s.NOT[k]])
            s.add([-b, -s.W[k][0]])
            for r in range(R):
                for i in range(n):
                    if not r >> i & 1: s.add([-b, -s.W[k][r], s.W[k][r | 1 << i]])
            s.add(list(s.W[k])); s.add([-x for x in s.W[k]])
        # channel value of the A input (the gate input of a variable reader): recover via aux vars
        for u in range(n):
            if u in Bset and cls.get(u) not in ('U', 'S'): continue
            lines = [S for S in sets if u in S and (len(S) >= 3 or u not in Bset)]
            mask1 = sum(1 << w for w in P[u] if w in Bset) if u in Bset else 0
            rows = set()
            for S in lines:
                m0 = sum(1 << w for w in S if w != u)
                for r in range(R):
                    if r & m0 == 0 and r & mask1 == mask1: rows.add(r)
            for k in range(ng):
                sel = s.rd[k][u] if u not in Bset else s.np[k][u]
                for i in range(n, n + k):
                    for r in rows:
                        # reader k of x_u with gate input i: OR-type -> W[i][r]=0, AND-type -> W[i][r]=1
                        s.add([-sel, -s.A[k][i], s.AND[k], -s.W[i - n][r]])
                        s.add([-sel, -s.A[k][i], -s.AND[k], s.W[i - n][r]])
    def solve(s, timeout=None, assumptions=()):
        from threading import Timer
        sol = Solver(name='cadical153', bootstrap_with=s.cl)
        t0 = time.time()
        if timeout:
            # cadical153 in pysat has no interrupt; run in a subprocess wrapper instead (see run.py)
            pass
        ok = sol.solve(assumptions=list(assumptions))
        res = None
        if ok:
            m = set(x for x in sol.get_model() if x > 0)
            gates = []
            for k in range(s.ng):
                a = next(i for i, v in enumerate(s.A[k]) if v in m); b = next(i for i, v in enumerate(s.B[k]) if v in m)
                gates.append(['not', a] if s.NOT[k] in m else ['and' if s.AND[k] in m else 'or', a, b])
            outs = [s.n + next(k for k, v in enumerate(o) if v in m) for o in s.O]
            res = dict(n=s.n, sets=s.sets, gates=gates, outs=outs)
        return ok, res, time.time() - t0

def verify(c):
    sys.path.insert(0, '/home/user/coord951/tools')
    from w951 import Circuit
    C = Circuit.from_dict(c)
    return C.verify()

SCEN = None
def load():
    J = json.load(open('/home/user/adv16/uncovered16.json'))
    return J
if __name__ == '__main__':
    J = load(); rank = int(sys.argv[1]); si = int(sys.argv[2]); cv = sys.argv[3]; ng = int(sys.argv[4]) if len(sys.argv) > 4 else None
    r = J[rank]; sets = r['sets']; n = 8
    base = sum(len(S) - 1 for S in sets); ng = ng or base - 1
    Bs = r['scen'][si]
    cls = dict(zip(Bs, cv)) if cv != '-' else {}
    E = Enc(n, sets, ng); E.scenario(set(Bs), cls); E.implied(set(Bs), cls)
    print('rank', rank, 'B', Bs, 'cls', cv, 'ng', ng, 'vars', E.top, 'clauses', len(E.cl), flush=True)
    ok, res, t = E.solve()
    print('RESULT', 'SAT' if ok else 'UNSAT', round(t, 1), flush=True)
    if ok:
        print(json.dumps(res)); print(verify(res))
        json.dump(res, open(f'/home/user/adv16/sat_r{rank}_s{si}_{cv}_{ng}.json', 'w'))
