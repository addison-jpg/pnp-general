#!/usr/bin/env python3
"""B3: SAT search for circuits with <= t NOT gates and fewer than base gates on OR-systems.

System = list of input sets; output k = OR of its set.  Gate count = every fan-in-2 AND/OR and every NOT
(same as research/one-not/tools/beyond_one_not/enum_small.c).  base = least gate count with no NOT gate (found here by SAT,
t = 0, increasing s).  Then ask: s = base-1 total gates, at most t NOT gates, all outputs correct on all 2^n inputs.
A SAT hit is decoded, re-evaluated by an independent truth-table evaluator, and written as .bench.
Usage: B3_sat_manynot.py n m [t,...] [timeout_s]   (all systems up to isomorphism: m antichain sets, size>=2, covering n)
"""
import sys, itertools, time, os, multiprocessing as mp
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

def encode(n, sets, s, t):
    R = 1 << n; nv = [0]
    def new():
        nv[0] += 1; return nv[0]
    cl = []
    val = {}  # (wire, row) -> literal or bool
    for i in range(n):
        for r in range(R): val[(i, r)] = bool(r >> i & 1)
    typ = []; A = []; B = []
    for g in range(s):
        w = n + g
        ta, to, tn = new(), new(), new(); typ.append((ta, to, tn))
        cl.append([ta, to, tn]); cl += [[-ta, -to], [-ta, -tn], [-to, -tn]]
        a = [new() for _ in range(w)]; b = [new() for _ in range(w)]
        A.append(a); B.append(b)
        for sel in (a, b):
            cl.append(sel[:])
            for x, y in itertools.combinations(sel, 2): cl.append([-x, -y])
        cl.append([-tn, b[0]])
        for j in range(w):
            for j2 in range(j, w): cl.append([-a[j2], -b[j], tn])  # a < b unless NOT
        for r in range(R):
            av, bv, gv = new(), new(), new()
            for j in range(w):
                for sel, x in ((a, av), (b, bv)):
                    v = val[(j, r)]
                    if v is True: cl.append([-sel[j], x])
                    elif v is False: cl.append([-sel[j], -x])
                    else: cl += [[-sel[j], -x, v], [-sel[j], x, -v]]
            cl += [[-ta, -gv, av], [-ta, -gv, bv], [-ta, gv, -av, -bv],
                   [-to, gv, -av], [-to, gv, -bv], [-to, -gv, av, bv],
                   [-tn, gv, av], [-tn, -gv, -av]]
            val[(w, r)] = gv
    # outputs
    for S in sets:
        o = [new() for _ in range(s)]
        cl.append(o[:])
        for x, y in itertools.combinations(o, 2): cl.append([-x, -y])
        for g in range(s):
            for r in range(R):
                tgt = any(r >> i & 1 for i in S); v = val[(n + g, r)]
                cl.append([-o[g], v if tgt else -v])
    nots = [typ[g][2] for g in range(s)]
    if t < s:
        enc = CardEnc.atmost(lits=nots, bound=t, top_id=nv[0], encoding=EncType.seqcounter)
        cl += enc.clauses
    return cl, typ, A, B

def solve(n, sets, s, t):
    cl, typ, A, B = encode(n, sets, s, t)
    sol = Cadical153(bootstrap_with=cl)
    ok = sol.solve()
    circ = None
    if ok:
        m = set(l for l in sol.get_model() if l > 0)
        circ = []
        for g in range(s):
            ty = 'and' if typ[g][0] in m else 'or' if typ[g][1] in m else 'not'
            a = next(j for j, x in enumerate(A[g]) if x in m); b = next(j for j, x in enumerate(B[g]) if x in m)
            circ.append((ty, a) if ty == 'not' else (ty, a, b))
    sol.delete()
    return ok, circ

def evaluate(n, circ, sets):
    """independent evaluator: bitmask truth tables over 2^n rows, returns list of wire tables"""
    R = 1 << n; M = (1 << R) - 1
    w = [sum(1 << r for r in range(R) if r >> i & 1) for i in range(n)]
    for g in circ:
        if g[0] == 'not': w.append(M ^ w[g[1]])
        elif g[0] == 'and': w.append(w[g[1]] & w[g[2]])
        else: w.append(w[g[1]] | w[g[2]])
    return w

def check(n, circ, sets):
    w = evaluate(n, circ, sets); R = 1 << n
    for S in sets:
        want = sum(1 << r for r in range(R) if any(r >> i & 1 for i in S))
        if want not in w[n:]: return False
    return True

def bench(n, circ, sets, path, note):
    w = evaluate(n, circ, sets); R = 1 << n; out = []
    for S in sets:
        want = sum(1 << r for r in range(R) if any(r >> i & 1 for i in S))
        out.append(n + w[n:].index(want))
    L = [f'# {note}'] + [f'INPUT(x{i})' for i in range(n)] + [f'OUTPUT(g{o})' for o in out]
    for g, c in enumerate(circ):
        nm = lambda j: f'x{j}' if j < n else f'g{j}'
        L.append(f'g{n+g} = ' + (f'NOT({nm(c[1])})' if c[0] == 'not' else f'{c[0].upper()}({nm(c[1])}, {nm(c[2])})'))
    open(path, 'w').write('\n'.join(L) + '\n')

def systems(n, m):
    subs = [frozenset(c) for k in range(2, n + 1) for c in itertools.combinations(range(n), k)]
    perms = list(itertools.permutations(range(n))); seen = set()
    for fam in itertools.combinations(subs, m):
        if any(a < b for a in fam for b in fam): continue
        if set().union(*fam) != set(range(n)): continue
        key = min(tuple(sorted(tuple(sorted(p[i] for i in S)) for S in fam)) for p in perms)
        if key in seen: continue
        seen.add(key); yield [list(S) for S in key]

def work(args):
    n, sets, ts, tmo = args
    t0 = time.time(); base = None
    for s in range(len(sets), 40):
        if time.time() - t0 > tmo: return (n, sets, None, {}, None)
        ok, _ = solve(n, sets, s, 0)
        if ok: base = s; break
    res = {}; hit = None
    for t in ts:
        ok, circ = solve(n, sets, base - 1, t) if base - 1 >= len(sets) else (False, None)
        res[t] = 'SAT' if ok else 'UNSAT'
        if ok: hit = (t, circ)
    return (n, sets, base, res, hit)

if __name__ == '__main__':
    n, m = int(sys.argv[1]), int(sys.argv[2])
    ts = [int(x) for x in (sys.argv[3] if len(sys.argv) > 3 else '2,3').split(',')]
    tmo = int(sys.argv[4]) if len(sys.argv) > 4 else 1200
    jobs = [(n, S, ts, tmo) for S in systems(n, m)]
    print(f'n={n} m={m} systems={len(jobs)} t={ts}', flush=True)
    cnt = {}
    here = os.path.dirname(os.path.abspath(__file__))
    with mp.Pool(int(os.environ.get('JOBS', 8))) as p:
        for n_, sets, base, res, hit in p.imap_unordered(work, jobs):
            print(sets, 'base', base, res, flush=True)
            for t, v in res.items(): cnt[(t, v)] = cnt.get((t, v), 0) + 1
            if hit:
                t, circ = hit; ok = check(n_, circ, sets)
                print('HIT', sets, t, circ, 'independent check:', ok, flush=True)
                if ok: bench(n_, circ, sets, os.path.join(here, f'B3_hit_n{n_}_{len(sets)}sets.bench'), f'{sets} s={base-1} base={base}')
    print('SUMMARY', cnt)
