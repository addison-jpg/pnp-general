"""B11 (copy of B9_two_sets.py + mode r2sat). B9: point lemma for two sets S, T (B9_point_two_sets.md). S = {0..p-1}; T = {p..p+q-1} (d) or {0} + q-1 new points (s).
Modes (python3 -I B9_two_sets.py MODE p q s|d [K] [trials]):
  lemma  : point program with p+q-3 lines (B6 encoding)                 -> UNSAT = point lemma holds for (p,q)
  xor    : same, XOR allowed as a fifth op                              -> SAT shows the bound needs the no-XOR basis
  ruleR  : K lines, no dead gate, and NO single private point removal makes a gate redundant (PT / = child / = earlier)
           -> SAT = rule R fails (a witness is printed)
  r2sat  : EXACT R2 (B9 s3.2): K lines, no dead/redundant line, and NO private u with <=K-1 lines after cleanup
           and NO private pair (a in S, e in T) with <=K-2 after cleanup. SAT = R2 false (witness, independently re-checked)
  r2     : sample ruleR witnesses (random phases) and test rule R2 (one private point kills >= 1 gate after cleanup,
           or one private pair a in S, e in T kills >= 2)
"""
import sys, time, random, itertools
from pysat.solvers import Solver

def build(n, W, K, xor=False):
    cnt = [0]
    def new():
        cnt[0] += 1; return cnt[0]
    cl = []; X = []; meta = []
    for i in range(K):
        sides = []; sm = []
        for _ in range(2):
            A = [new() for _ in range(n)]; g = new(); sel = [g]
            for S in W:
                for u, v in itertools.combinations(S, 2): cl.append([-g, -A[u], -A[v]])
            for j in range(i):
                p = new(); sel.append(p)
                for u in range(n): cl.append([-p, -A[u], X[j][u]]); cl.append([-p, A[u], -X[j][u]])
            cl.append(sel); sides.append(A); sm.append(sel)
        A, B = sides; F = [new() for _ in range(n)]; o = [new() for _ in range(5 if xor else 4)]; cl.append(o)
        for u in range(n):
            a, b, f = A[u], B[u], F[u]
            cl += [[-o[0], -f, a, b], [-o[0], f, -a], [-o[0], f, -b]]          # A | B
            cl += [[-o[1], f, -a, -b], [-o[1], -f, a], [-o[1], -f, b]]         # A & B
            cl += [[-o[2], -f, a], [-o[2], -f, -b], [-o[2], f, -a, b]]         # A - B
            cl += [[-o[3], -f, b], [-o[3], -f, -a], [-o[3], f, -b, a]]         # B - A
            if xor: cl += [[-o[4], -f, a, b], [-o[4], -f, -a, -b], [-o[4], f, -a, b], [-o[4], f, a, -b]]
        X.append(F); meta.append((A, B, o, sm))
    for S in W:
        sel = []
        for i in range(K):
            p = new(); sel.append(p)
            for u in range(n): cl.append([-p, X[i][u] if u in S else -X[i][u]])
        cl.append(sel)
    return cl, X, meta, new

def decode(model, X, meta, n):
    M = set(v for v in model if v > 0); prog = []
    for i, (A, B, o, sm) in enumerate(meta):
        ks = []
        for side, Z in ((0, A), (1, B)):
            if sm[side][0] in M: ks.append(('L', frozenset(u for u in range(n) if Z[u] in M)))
            else: ks.append(('X', [j for j in range(i) if sm[side][1 + j] in M][0]))
        prog.append(([k for k in range(4) if o[k] in M][0], ks[0], ks[1]))
    return prog

def needed(prog, W, rm, targets):
    """gates left after removing points rm and deleting redundant (PT / = child / = earlier) and dead gates"""
    rm = frozenset(rm); Wr = [set(S) - rm for S in W]
    isPT = lambda x: all(len(x & S) <= 1 for S in Wr)
    vals, rep = [], {}
    get = lambda k: ('L', k[1] - rm) if k[0] == 'L' else rep.get(k[1], k)
    val = lambda k: k[1] if k[0] == 'L' else vals[k[1]]
    for i, (op, ka, kb) in enumerate(prog):
        a, b = get(ka), get(kb); A, B = val(a), val(b)
        v = frozenset([A | B, A & B, A - B, B - A][op]); vals.append(v)
        if isPT(v): rep[i] = ('L', v)
        elif v == A: rep[i] = a
        elif v == B: rep[i] = b
        else:
            for j in range(i):
                if j not in rep and vals[j] == v: rep[i] = ('X', j); break
    need, stack = set(), []
    for t in targets:
        t = frozenset(t) - rm
        if not isPT(t): stack.append([i for i in range(len(prog)) if i not in rep and vals[i] == t][0])
    while stack:
        i = stack.pop()
        if i in need: continue
        need.add(i)
        for k in (get(prog[i][1]), get(prog[i][2])):
            if k[0] == 'X': stack.append(k[1])
    return len(need)

def ruleR_cnf(n, W, K, priv):
    cl, X, meta, new = build(n, W, K)
    def differ(F, G, skip):
        ds = []
        for w in range(n):
            if w == skip: continue
            d = new(); ds.append(d); cl.append([-d, F[w], G[w]]); cl.append([-d, -F[w], -G[w]])
        return ds
    for i, (A, B, o, sm) in enumerate(meta):
        F = X[i]
        for u in priv:
            zs = []
            for St in W:
                for a, b in itertools.combinations([v for v in St if v != u], 2):
                    z = new(); zs.append(z); cl.append([-z, F[a]]); cl.append([-z, F[b]])
            cl.append(zs); cl.append(differ(F, A, u)); cl.append(differ(F, B, u))
            for j in range(i): cl.append(differ(F, X[j], u))
    for j in range(K):   # no dead gate
        lits = [meta[i][3][s][1 + j] for i in range(j + 1, K) for s in (0, 1)]
        for St in W:
            e = new(); lits.append(e)
            for u in range(n): cl.append([-e, X[j][u] if u in St else -X[j][u]])
        cl.append(lits)
    return cl, X, meta, new


def r2sat_cnf(n, W, K, priv):
    cl, X, meta, new = build(n, W, K)
    S, T = W
    def removal_sets():
        for u in priv: yield (u,), 0
        for a in priv:
            for e in priv:
                if a in S and e in T: yield (a, e), 1
    def block(rm, allow_dead):
        rm = set(rm); keep = [w for w in range(n) if w not in rm]
        def differ(F, G):
            ds = []
            for w in keep:
                d = new(); ds.append(d); cl.append([-d, F[w], G[w]]); cl.append([-d, -F[w], -G[w]])
            return ds
        need = [new() for _ in range(K)]
        if allow_dead:                      # at most one line fails to survive
            for i in range(K):
                for j in range(i + 1, K): cl.append([need[i], need[j]])
        else:
            for i in range(K): cl.append([need[i]])
        tg = [St for St in W if len(set(St) - rm) >= 2]
        for i, (A, B, o, sm) in enumerate(meta):
            F = X[i]; nd = need[i]
            zs = []                          # value not PT after removal
            for St in W:
                for a, b in itertools.combinations([v for v in St if v not in rm], 2):
                    z = new(); zs.append(z); cl.append([-z, F[a]]); cl.append([-z, F[b]])
            cl.append([-nd] + zs); cl.append([-nd] + differ(F, A)); cl.append([-nd] + differ(F, B))
            for j in range(i): cl.append([-nd] + differ(F, X[j]))
            ways = []
            for St in tg:                    # root: equals a surviving target
                r = new(); ways.append(r)
                for w in keep: cl.append([-r, F[w] if w in St else -F[w]])
            for m in range(i + 1, K):
                for side in (0, 1):
                    Z = meta[m][side]; e = new(); c = new(); ways.append(c)
                    cl.append([-c, need[m]]); cl.append([-c, e])
                    for w in keep: cl.append([-e, -Z[w], F[w]]); cl.append([-e, Z[w], -F[w]])
            cl.append([-nd] + ways)
    for rm, kind in removal_sets(): block(rm, kind == 1)
    # original: no dead line (as in ruleR) and no redundant line
    for j in range(K):
        lits = [meta[i][3][s][1 + j] for i in range(j + 1, K) for s in (0, 1)]
        for St in W:
            e = new(); lits.append(e)
            for u in range(n): cl.append([-e, X[j][u] if u in St else -X[j][u]])
        cl.append(lits)
    for i, (A, B, o, sm) in enumerate(meta):
        F = X[i]; ds = []
        zs = []
        for St in W:
            for a, b in itertools.combinations(St, 2):
                z = new(); zs.append(z); cl.append([-z, F[a]]); cl.append([-z, F[b]])
        cl.append(zs)
        for G in [A, B] + X[:i]:
            ds = []
            for w in range(n):
                d = new(); ds.append(d); cl.append([-d, F[w], G[w]]); cl.append([-d, -F[w], -G[w]])
            cl.append(ds)
    return cl, X, meta, new

def indep_count(prog, n, W, rm):
    """independent cleanup count: evaluate on universe minus rm; keep a line iff its value is not point-like, differs
    from both input values and all earlier line values, and (by value) it is a surviving target or read (by value) by a kept line."""
    rm = set(rm); full = lambda St: frozenset(set(St) - rm)
    val = []
    for op, ka, kb in prog:
        g = lambda k: full(k[1]) if k[0] == 'L' else val[k[1]]
        A, B = g(ka), g(kb)
        val.append(frozenset([A | B, A & B, A - B, B - A][op]))
    ptlike = lambda v: all(len(v & set(St)) <= 1 for St in W)
    ins = [(( full(ka[1]) if ka[0] == 'L' else val[ka[1]]), (full(kb[1]) if kb[0] == 'L' else val[kb[1]])) for _, ka, kb in prog]
    keep = [i for i, v in enumerate(val) if not ptlike(v) and v != ins[i][0] and v != ins[i][1] and all(v != val[j] for j in range(i))]
    tg = [full(St) for St in W if not ptlike(full(St))]
    alive = set(); ch = True
    while ch:
        ch = False
        for i in keep:
            if i in alive: continue
            if val[i] in tg or any(m in alive and val[i] in ins[m] for m in keep if m > i):
                alive.add(i); ch = True
    return len(alive)

def r2_violation(prog, n, W, priv):
    S = set(W[0]); T = set(W[1]); K = len(prog)
    if indep_count(prog, n, W, []) != K: return 'original not reduced'
    for u in priv:
        if indep_count(prog, n, W, [u]) <= K - 1: return None
    for a in priv:
        for e in priv:
            if a in S and e in T and indep_count(prog, n, W, [a, e]) <= K - 2: return None
    return 'VIOLATION'

if __name__ == '__main__':
    mode, p, q, sh = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == 's'
    S = tuple(range(p)); T = ((0,) if sh else ()) + tuple(range(p, p + q - (1 if sh else 0)))
    n = max(S + T) + 1; W = [S, T]; priv = [u for u in range(n) if (u in S) != (u in T)]
    tag = '%d %d %s' % (p, q, 'shared' if sh else 'disjoint')
    t0 = time.time()
    if mode in ('lemma', 'xor'):
        K = p + q - 3; cl = build(n, W, K, xor=(mode == 'xor'))[0]
        with Solver(name='cd15', bootstrap_with=cl) as sv: r = sv.solve()
        print(mode, tag, 'lines', K, 'SAT' if r else 'UNSAT', '%.1fs' % (time.time() - t0))
    elif mode == 'ruleR':
        K = int(sys.argv[5]); cl, X, meta, new = ruleR_cnf(n, W, K, priv)
        with Solver(name='cd15', bootstrap_with=cl) as sv:
            r = sv.solve(); print('ruleR', tag, 'K', K, 'SAT (rule R fails)' if r else 'UNSAT (rule R holds)', '%.1fs' % (time.time() - t0))
            if r:
                prog = decode(sv.get_model(), X, meta, n)
                for i, (op, ka, kb) in enumerate(prog):
                    f = lambda k: sorted(k[1]) if k[0] == 'L' else 'X%d' % k[1]
                    print('  X%d = %s %s %s' % (i, f(ka), ['|', '&', '-', 'rev-'][op], f(kb)))
    elif mode == 'r2sat':
        K = int(sys.argv[5]); cl, X, meta, new = r2sat_cnf(n, W, K, priv)
        with Solver(name='cd15', bootstrap_with=cl) as sv:
            r = sv.solve(); print('r2sat', tag, 'K', K, 'vars', new(), 'clauses', len(cl), 'SAT (R2 FAILS)' if r else 'UNSAT (R2 holds)', '%.1fs' % (time.time() - t0), flush=True)
            if r:
                prog = decode(sv.get_model(), X, meta, n)
                for i, (op, ka, kb) in enumerate(prog):
                    f = lambda k: sorted(k[1]) if k[0] == 'L' else 'X%d' % k[1]
                    print('  X%d = %s %s %s' % (i, f(ka), ['|', '&', '-', 'rev-'][op], f(kb)))
                print('  independent check:', r2_violation(prog, n, W, priv), '| B9 needed():', needed(prog, W, [], W),
                      [needed(prog, W, [u], W) for u in priv])
    elif mode == 'r2':
        K, trials = int(sys.argv[5]), int(sys.argv[6]); cl, X, meta, new = ruleR_cnf(n, W, K, priv); nv = new()
        bad = tot = 0
        for t in range(trials):
            random.seed(t)
            with Solver(name='g3', bootstrap_with=cl) as sv:
                sv.set_phases([random.choice([v, -v]) for v in range(1, nv)])
                if not sv.solve(): print('no rule-R witness'); break
                prog = decode(sv.get_model(), X, meta, n)
            tot += 1
            if needed(prog, W, [], W) < K: continue
            ok = any(needed(prog, W, [u], W) <= K - 1 for u in priv) or \
                 any(needed(prog, W, [a, e], W) <= K - 2 for a in priv for e in priv if a in S and e in T)
            if not ok: bad += 1; print('R2 FAILS', prog)
        print('r2', tag, 'K', K, 'samples', tot, 'R2 failures', bad, '%.1fs' % (time.time() - t0))
