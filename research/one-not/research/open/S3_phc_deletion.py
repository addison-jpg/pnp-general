"""S3: PHC@0 under point deletion (U1_unify.md s4).  Run from this directory:
  nice python3 -I S3_phc_deletion.py p q s|d K cap [side]      side = S (default) or T: the set that loses a private point

For every distinct tuple of line values of a K-line point program computing S, T (B9 encoding, exhaustive if below cap),
and the private point u (the last private point of the chosen side): CLEANED program for (S-u, T) = lines with value
minus u, keep a line iff |value - u| >= 2 and it is the first line with that cleaned value.  Bases of a set w among
lines = line sets I, |I| = |w|-1, with |U_J (value & w)| >= |J|+1 for every nonempty J subset I (Lorea form of the U1 s1
matroid).  PHC partition = disjoint bases (E_A, E_B).
Per (program, u): short    = no PHC@0 partition of the cleaned program (S-u, T);
                  some_ext = some cleaned partition (E'_A, E_B) extends: exists base E_A of A (with u) with E_A >= E'_A,
                             E_A disjoint from E_B (E_B kept; only lines added on A's side);
                  all_ext  = every cleaned partition extends.
"""
import sys, itertools
sys.path.insert(0, __file__.rsplit("/", 1)[0] if "/" in __file__ else ".")
from B9_two_sets import build, decode
from pysat.solvers import Solver

def bases(lines, vals, pts, need):
    ok = [i for i in lines if len(vals[i] & pts) >= 2]
    res = []
    for I in itertools.combinations(ok, need):
        good = True
        for r in range(1, need + 1):
            for J in itertools.combinations(I, r):
                if len(frozenset().union(*[vals[i] & pts for i in J])) < r + 1: good = False; break
            if not good: break
        if good: res.append(frozenset(I))
    return res

def analyse(vals, S, T, u, side):
    K = len(vals)
    A, B = (S, T) if side == 'S' else (T, S)
    A2 = A - {u}
    bA = bases(range(K), vals, A, len(A) - 1); bB = bases(range(K), vals, B, len(B) - 1)
    cv = {}; kept = []
    for i in range(K):
        c = vals[i] - {u}
        if len(c) >= 2 and c not in cv.values(): cv[i] = c; kept.append(i)
    bA2 = [frozenset()] if len(A2) == 1 else bases(kept, cv, A2, len(A2) - 1)
    bB2 = bases(kept, cv, B, len(B) - 1)
    parts = [(x, y) for x in bA2 for y in bB2 if not (x & y)]
    if not parts: return 'short', None, None, bA, bB
    exts = [any(x <= E and not (E & y) for E in bA) for x, y in parts]
    return 'ok', any(exts), all(exts), bA, bB

def main():
    p, q, sh, K, cap = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3] == 's', int(sys.argv[4]), int(sys.argv[5])
    side = sys.argv[6] if len(sys.argv) > 6 else 'S'
    if sh: S = frozenset(range(p)); T = frozenset([0] + list(range(p, p + q - 1))); n = p + q - 1
    else: S = frozenset(range(p)); T = frozenset(range(p, p + q)); n = p + q
    A = S if side == 'S' else T; Bset = T if side == 'S' else S
    priv = sorted(A - Bset)
    if not priv: print('no private point'); return
    u = priv[-1]
    cl, X, meta, new = build(n, [sorted(S), sorted(T)], K)
    cnt = short = noext = notall = 0; worst = first = nall = None
    with Solver(name='g3', bootstrap_with=cl) as s:
        while cnt < cap and s.solve():
            m = set(v for v in s.get_model() if v > 0); cnt += 1
            vals = [frozenset(x for x in range(n) if X[i][x] in m) for i in range(K)]
            st, some, allx, bA, bB = analyse(vals, S, T, u, side)
            if not bA or not bB: print('ORIGINAL has no basis', [sorted(v) for v in vals])
            if st == 'short':
                short += 1
                if first is None: first = ('cleaned program has no partition', vals, m)
            else:
                if not some:
                    noext += 1
                    if worst is None: worst = ('no extendable partition', vals, m)
                if not allx:
                    notall += 1
                    if nall is None: nall = ('some partition of the cleaned program does not extend (another does)', vals, m)
            s.add_clause([-X[i][x] if X[i][x] in m else X[i][x] for i in range(K) for x in range(n)])
    print('S3 p q shared K side u =', p, q, sh, K, side, u, 'tuples', cnt, '(cap %d)' % cap,
          '| cleaned_short', short, '| no_extendable', noext, '| not_all_extendable', notall, flush=True)
    for tag, rec in (('first cleaned_short', first), ('first non-extendable', worst), ('first not-all-extendable', nall)):
        if rec:
            print(tag + ':', rec[0])
            for i, (op, a, b) in enumerate(decode(rec[2], X, meta, n)):
                print('  X%d = %s %s %s = %s' % (i, fmt(a), ['|', '&', '-', 'rev-'][op], fmt(b), sorted(rec[1][i])))

def fmt(k): return ('X%d' % k[1]) if k[0] == 'X' else str(sorted(k[1]))
if __name__ == '__main__': main()
