"""U1: the payment Hall condition (PHC), one checker for both programs (U1_unify.md).

PHC instance: payers E; sets w with classes (a partition of S_w's points); for each payer g and set w a list of flip
sets (subsets of S_w's points).  M_w = matroid on E: I independent iff each g in I can pick two classes that both
meet one flip set of (g, w), the picked pairs forming a forest on w's classes.  PHC: disjoint E_w, each a basis of
M_w (|E_w| = #classes_w - 1).  By Edmonds / Nash-Williams matroid partition, PHC <=> for all A subset E:
sum_w (r_w(E) - r_w(A)) <= |E \\ A|.

Modes (repo root):
  circ  FILE.json ...           several-NOT forest form of S3(b): payers = wire classes, flip sets = D_{S_w}(g, Z)
                                over every zero point Z of S_w (multi-point).  Classes of w = singletons.
  circ0 FILE.json ...           same, only the all-zero point Z = 0 (single common point, the root form of BOTTOM PAY).
  prog  p q s|d K trials        point programs (B9 encoding, K lines, random phases) computing S, T: payers = lines,
                                flip set = line value (the sens set at 0).  Tests PHC at the common point 0.
Prints per instance: per-set rank (must equal need), PHC yes/no, and on failure the program.
"""
import json, sys, itertools, random
sys.path.insert(0, __file__.rsplit('/', 1)[0])

def partition(payers, sets):
    """payers: list of ids; sets: list of (classes: dict point->class, flips: dict payer->list of frozensets of points).
    Returns (ranks, ok).  Exact backtracking."""
    prep = []
    for cl, fl in sets:
        F = {}
        for g in payers:
            cs = [frozenset(cl[u] for u in f if u in cl) for f in fl.get(g, [])]
            cs = [c for c in cs if len(c) >= 2]
            cs = [c for c in cs if not any(c < d for d in cs)]
            if cs: F[g] = list(set(cs))
        prep.append((sorted(set(cl.values())), F))
    def rank(cls, F, allowed):
        lab = {c: c for c in cls}
        def find(c):
            while lab[c] != c: c = lab[c]
            return c
        # greedy is exact for a matroid only with a fixed representative; use exhaustive small search instead
        best = [0]
        gs = [g for g in allowed if g in F]
        def go(j, lab, r):
            best[0] = max(best[0], r)
            if best[0] == len(cls) - 1: return
            for k in range(j, len(gs)):
                def fd(c):
                    while lab[c] != c: c = lab[c]
                    return c
                for c in F[gs[k]]:
                    roots = sorted({fd(x) for x in c})
                    for x, y in itertools.combinations(roots, 2):
                        l2 = dict(lab); l2[y] = x; go(k + 1, l2, r + 1)
                        if best[0] == len(cls) - 1: return
        go(0, lab, 0)
        return best[0]
    ranks = [rank(cls, F, payers) for cls, F in prep]
    order = sorted(range(len(prep)), key=lambda i: -ranks[i])
    idx = {g: k for k, g in enumerate(payers)}
    def go(oi, used, lab, got, start):
        if oi == len(order): return True
        i = order[oi]; cls, F = prep[i]
        if got == ranks[i]: return go(oi + 1, used, None, 0, 0)
        if lab is None: lab = {c: c for c in cls}
        def fd(c):
            while lab[c] != c: c = lab[c]
            return c
        for k in range(start, len(payers)):
            g = payers[k]
            if used >> k & 1 or g not in F: continue
            pairs = set()
            for c in F[g]:
                roots = sorted({fd(x) for x in c})
                pairs.update(itertools.combinations(roots, 2))
            for x, y in sorted(pairs):
                l2 = dict(lab); l2[y] = x
                if go(oi, used | 1 << k, l2, got + 1, k + 1): return True
        return False
    return ranks, go(0, 0, None, 0, 0)

def circ(f, single):
    from B5_flip_hall import tables, zeros, correct
    c = json.load(open(f)); n = c['n']; S = [list(R) for R in c['sets']]
    w, M = tables(n, c['gates']); assert correct(c, w)
    bit = lambda t, x: t >> x & 1
    cls = {}
    for t in w: cls.setdefault(min(t, M ^ t), t)
    payers = sorted(cls); sets = []
    for R in S:
        fl = {}
        for g in payers:
            t = cls[g]; Zs = [0] if single else zeros(n, R); out = []
            for Z in Zs:
                D = frozenset(u for u in R if bit(t, Z | 1 << u) != bit(t, Z))
                if len(D) >= 2: out.append(D)
            if out: fl[g] = out
        sets.append(({u: u for u in R}, fl))
    ranks, ok = partition(payers, sets)
    need = [len(R) - 1 for R in S]
    return dict(n=n, nots=sum(g[0] == 'not' for g in c['gates']), need=need, ranks=ranks, PHC=ok)

def prog(p, q, sh, K, trials):
    from B9_two_sets import build, decode
    from pysat.solvers import Solver
    if sh: Sset = list(range(p)); Tset = [0] + list(range(p, p + q - 1)); n = p + q - 1
    else: Sset = list(range(p)); Tset = list(range(p, p + q)); n = p + q
    W = [Sset, Tset]; cl, X, meta, new = build(n, W, K); nv = new()
    fails = 0; seen = 0
    for tr in range(trials):
        s = Solver(name='g3', bootstrap_with=cl)
        rnd = random.Random(tr); s.set_phases([v if rnd.random() < .5 else -v for v in range(1, nv)])
        if not s.solve(): print('UNSAT'); return
        m = set(v for v in s.get_model() if v > 0); s.delete()
        vals = [frozenset(u for u in range(n) if X[i][u] in m) for i in range(K)]
        payers = list(range(K))
        sets = [({u: u for u in R}, {i: [vals[i]] for i in payers}) for R in W]
        ranks, ok = partition(payers, sets); seen += 1
        if not ok:
            fails += 1
            if fails <= 2:
                print('PHC@0 FAILS, ranks', ranks, 'lines:')
                for i, (op, a, b) in enumerate(decode(m, X, meta, n)):
                    print('  X%d = %s %s %s = %s' % (i, fmt(a), '|&-~'[op], fmt(b), sorted(vals[i])))
    print('p q shared K =', p, q, sh, K, 'programs', seen, 'PHC@0 failures', fails)

def enum(p, q, sh, K, cap):
    """all distinct tuples of line values (up to cap) of K-line point programs computing S, T: PHC@0 on each"""
    from B9_two_sets import build
    from pysat.solvers import Solver
    if sh: W = [list(range(p)), [0] + list(range(p, p + q - 1))]; n = p + q - 1
    else: W = [list(range(p)), list(range(p, p + q))]; n = p + q
    cl, X, meta, new = build(n, W, K); fails = cnt = 0
    with Solver(name='g3', bootstrap_with=cl) as s:
        while cnt < cap and s.solve():
            m = set(v for v in s.get_model() if v > 0); cnt += 1
            vals = [frozenset(u for u in range(n) if X[i][u] in m) for i in range(K)]
            ops = [[k for k in range(4) if meta[i][2][k] in m][0] for i in range(K)]
            pay = [i for i in range(K) if not UNION_ONLY or ops[i] == 0]
            sets = [({u: u for u in R}, {i: [vals[i]] for i in pay}) for R in W]
            ranks, ok = partition(pay, sets)
            if UNION_ONLY and ranks != [len(R) - 1 for R in W]: print('union-run rank short', ranks, ops, [sorted(v) for v in vals])
            if not ok:
                fails += 1
                if fails <= 2:
                    from B9_two_sets import decode
                    print('PHC@0 FAILS', ranks, 'payers', pay)
                    for i, (op, a, b) in enumerate(decode(m, X, meta, n)):
                        print('  X%d = %s %s %s = %s' % (i, fmt(a), ['|', '&', '-', 'rev-'][op], fmt(b), sorted(vals[i])))
            s.add_clause([-X[i][u] if X[i][u] in m else X[i][u] for i in range(K) for u in range(n)])
    print('enum p q shared K =', p, q, sh, K, 'value tuples', cnt, '(cap %d)' % cap, 'PHC@0 failures', fails)

def fmt(k): return ('X%d' % k[1]) if k[0] == 'X' else str(sorted(k[1]))

UNION_ONLY = '--union' in sys.argv
if __name__ == '__main__':
    sys.argv = [a for a in sys.argv if a != '--union']
    mode = sys.argv[1]
    if mode in ('circ', 'circ0'):
        for f in sys.argv[2:]:
            try: print(f.rsplit('/', 1)[-1], circ(f, mode == 'circ0'))
            except AssertionError: print(f, 'not correct')
    elif mode == 'enum':
        enum(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == 's', int(sys.argv[5]), int(sys.argv[6]))
    elif mode == 'prog':
        prog(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == 's', int(sys.argv[5]), int(sys.argv[6]))
