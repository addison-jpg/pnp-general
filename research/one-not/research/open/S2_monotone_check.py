"""S2: tests for S2_oronly_monotone.md.  Monotone point programs (ops union/intersection only), K lines computing every S_w.
Modes (cd research/one-not/research/open; run under nice, one core):
  phc   p q s|d K cap          OR-only PHC@0 (U1 partition()) on every distinct value tuple, <= cap tuples
  hall  p q s|d K cap          also the contracted counting form: for all partitions P of S, Q of T, #union lines
                               crossing P or Q >= |P|+|Q|-2 (the Edmonds/Rado form of PHC, S2 sec 2)
  fam   NAME K cap             PHC test on a named family (tri3, star3, pasch)
"""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from U1_payment_hall import partition
from B9_two_sets import build
from pysat.solvers import Solver

def setpartitions(items):
    items = list(items)
    if not items: yield []; return
    f, rest = items[0], items[1:]
    for p in setpartitions(rest):
        yield [[f]] + p
        for i in range(len(p)): yield p[:i] + [[f] + p[i]] + p[i + 1:]

FAM = {'tri3': [[0, 1, 2], [2, 3, 4], [4, 5, 0]], 'star3': [[0, 1, 2], [0, 3, 4], [0, 5, 6]],
       'pasch': [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]}

def programs(W, n, K, cap):
    cl, X, meta, new = build(n, W, K)
    for i in range(K): cl += [[-meta[i][2][2]], [-meta[i][2][3]]]       # monotone: no difference
    cnt = 0
    with Solver(name='g3', bootstrap_with=cl) as s:
        while cnt < cap and s.solve():
            m = set(v for v in s.get_model() if v > 0); cnt += 1
            vals = [frozenset(u for u in range(n) if X[i][u] in m) for i in range(K)]
            ops = [[k for k in range(2) if meta[i][2][k] in m][0] for i in range(K)]
            yield vals, ops
            s.add_clause([-X[i][u] if X[i][u] in m else X[i][u] for i in range(K) for u in range(n)])

def fam_of(p, q, sh):
    if sh: return [list(range(p)), [0] + list(range(p, p + q - 1))], p + q - 1
    return [list(range(p)), list(range(p, p + q))], p + q

def run_phc(W, n, K, cap, hall):
    cnt = fails = hfails = 0
    for vals, ops in programs(W, n, K, cap):
        cnt += 1
        U = [i for i in range(K) if ops[i] == 0]
        sets = [({u: u for u in R}, {i: [vals[i]] for i in U}) for R in W]
        ranks, ok = partition(U, sets)
        if ranks != [len(R) - 1 for R in W]: print('RANK SHORT', ranks, ops, [sorted(v) for v in vals])
        if not ok:
            fails += 1
            if fails <= 2: print('PHC FAIL', ops, [sorted(v) for v in vals])
        if hall and len(W) == 2:
            S, T = W; bad = False
            for P in setpartitions(S):
                bl = [set(b) for b in P]
                cP = {i for i in U if sum(1 for b in bl if b & vals[i]) >= 2}
                for Q in setpartitions(T):
                    bq = [set(b) for b in Q]
                    cQ = {i for i in U if sum(1 for b in bq if b & vals[i]) >= 2}
                    if len(cP | cQ) < len(P) + len(Q) - 2: bad = True
            if bad: hfails += 1
    print('W', W, 'K', K, 'tuples', cnt, '(cap %d)' % cap, 'PHC fails', fails, 'contracted-form fails', hfails if hall else 'n/a')

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode in ('phc', 'hall'):
        W, n = fam_of(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == 's')
        run_phc(W, n, int(sys.argv[5]), int(sys.argv[6]), mode == 'hall')
    elif mode == 'fam':
        W = FAM[sys.argv[2]]; run_phc(W, max(max(R) for R in W) + 1, int(sys.argv[3]), int(sys.argv[4]), False)
