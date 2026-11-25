"""B5: S3(b) (Hall form) on systems of triples, for EVERY circuit (any size, any number of NOT gates), by SAT on functions.

Reduction (proved in B5_flip_hall.md, section 3): for a triple S_w with output o_w, let g_w be the first wire whose function is
+-OR(S_w); g_w = A op B (op AND/OR), and E(w) = the classes of A, B that lie in C(w). Then E(w) is non-empty, its classes are not
output classes, and if E(w) = {[A]} then B is S_w-thin (|D| <= 1 at every zero point of S_w). A Hall violation on a family W of
triples (pairs never matter: their only needed class is their own output, which is private) gives at most |W| - 1 classes Y_i with,
for every w in W: OR(S_w) = A_w op_w B_w, A_w = +-Y_a, and B_w = +-Y_b or S_w-thin; and no Y_i equal to +-OR(S_v), v in W.
This script asks a SAT solver for such functions. UNSAT for W means: no correct circuit violates Hall on W.
Usage: python3 -I B5_triple_sat.py SYSTEM   (SYSTEM in SYSTEMS below) ; prints one line per subfamily up to relabelling-free brute force."""
import sys, itertools, time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

SYSTEMS = {
    'two3':  (5, [(0, 1, 2), (0, 3, 4)]),
    'dis3':  (6, [(0, 1, 2), (3, 4, 5)]),
    'tri3':  (6, [(0, 1, 3), (1, 2, 4), (0, 2, 5)]),
    'star3': (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6)]),
    'pasch': (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]),
    'fano':  (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]),
    'k4tri': (7, [(0, 1, 4), (0, 2, 5), (0, 3, 6), (1, 2, 6), (1, 3, 5), (2, 3, 4)]),
    'ag23':  (9, [(0, 1, 2), (3, 4, 5), (6, 7, 8), (0, 3, 6), (1, 4, 7), (2, 5, 8),
                  (0, 4, 8), (1, 5, 6), (2, 3, 7), (0, 5, 7), (1, 3, 8), (2, 4, 6)]),
}

def solve(n, W):
    N = 1 << n; k = len(W) - 1
    cnt = [0]
    def new():
        cnt[0] += 1; return cnt[0]
    Y = [[new() for _ in range(N)] for _ in range(k)]
    cl = []
    outs = [[int(any(x >> u & 1 for u in S)) for x in range(N)] for S in W]
    # Y_i != +-out_v
    for i in range(k):
        for o in outs:
            cl.append([Y[i][x] if o[x] == 0 else -Y[i][x] for x in range(N)])   # some x with Y != o
            cl.append([Y[i][x] if o[x] == 1 else -Y[i][x] for x in range(N)])   # some x with Y == o
    for w, S in enumerate(W):
        o = outs[w]
        A = [new() for _ in range(N)]; B = [new() for _ in range(N)]
        orop = new()  # true: OR, false: AND
        for x in range(N):
            if o[x]:
                cl.append([-orop, A[x], B[x]]); cl.append([orop, A[x]]); cl.append([orop, B[x]])
            else:
                cl.append([-orop, -A[x]]); cl.append([-orop, -B[x]]); cl.append([orop, -A[x], -B[x]])
        # A = +-Y_a
        selA = []
        for a in range(k):
            for s in (0, 1):
                p = new(); selA.append(p)
                for x in range(N):  # p -> A[x] == Y[a][x] xor s
                    if s == 0: cl.append([-p, -A[x], Y[a][x]]); cl.append([-p, A[x], -Y[a][x]])
                    else: cl.append([-p, -A[x], -Y[a][x]]); cl.append([-p, A[x], Y[a][x]])
        cl.append(selA)
        # B = +-Y_b or thin
        thin = new(); selB = [thin]
        for b in range(k):
            for s in (0, 1):
                p = new(); selB.append(p)
                for x in range(N):
                    if s == 0: cl.append([-p, -B[x], Y[b][x]]); cl.append([-p, B[x], -Y[b][x]])
                    else: cl.append([-p, -B[x], -Y[b][x]]); cl.append([-p, B[x], Y[b][x]])
        cl.append(selB)
        for Z in range(N):
            if any(Z >> u & 1 for u in S): continue
            for u, v in itertools.combinations(S, 2):
                zu, zv = Z | 1 << u, Z | 1 << v
                cl.append([-thin, B[Z], -B[zu], -B[zv]]); cl.append([-thin, -B[Z], B[zu], B[zv]])
    with Solver(name='cd15', bootstrap_with=cl) as s:
        r = s.solve()
        model = s.get_model() if r else None
    return r, model, Y

if __name__ == '__main__':
    name = sys.argv[1]; n, sets = SYSTEMS[name]
    maxw = int(sys.argv[2]) if len(sys.argv) > 2 else len(sets)
    tot = 0; sat = 0
    for r in range(2, min(maxw, len(sets)) + 1):
        for W in itertools.combinations(sets, r):
            t0 = time.time(); res, model, Y = solve(n, list(W)); tot += 1
            if res:
                sat += 1
                print(name, 'SAT (candidate)', W, [hex(sum(1 << x for x in range(1 << n) if model[Y[i][x] - 1] > 0)) for i in range(len(Y))], flush=True)
    print(name, 'subfamilies tested', tot, 'SAT', sat, flush=True)
