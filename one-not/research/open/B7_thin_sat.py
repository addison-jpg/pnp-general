"""B7: thin-basis SAT problem (B5_flip_hall.md s5) on the first unsettled systems, with timeouts, a control, witness check.

Problem for a family W: K = base(W)-1 lines F_i = L_i op R_i (op AND/OR); each of L_i, R_i is an arbitrary W-thin function
(|D_S| <= 1 at every zero point of S, every S in W), or +-F_j with j<i; every OR(S_w) equals some +-F_i.  UNSAT = lemma holds
for W.  --control uses base(W) lines (expected SAT).  Encoding as B5_thin_slp.py (truth tables as variables), plus:
  no symmetry breaking beyond B5's encoding (none was found that is both cheap and sound with free thin sides).
Usage: python3 -I B7_thin_sat.py NAME [--control] [--timeout=SEC] [--save=FILE]
       python3 -I B7_thin_sat.py --list
Result line: NAME n base lines RESULT seconds.  A SAT result is decoded and re-evaluated independently (verify()), and
the witness (line structure + truth tables) is written to --save."""
import sys, itertools, time, json, threading
from pysat.solvers import Solver

def S(*a): return [tuple(x) for x in a]
SYSTEMS = {
 'fano':  (7, S((0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5))),
 'two5_1': (9, S((0,1,2,3,4),(0,5,6,7,8))),            # intersection size 1
 'two5_0': (10, S((0,1,2,3,4),(5,6,7,8,9))),           # intersection size 0
 'k4tri': (7, S((0,1,4),(0,2,5),(0,3,6),(1,2,6),(1,3,5),(2,3,4))),   # K4: one set per edge-pair... 6 triples on 7 points
 'tri5':  (5, S((0,1,2),(0,3,4),(1,3))),
 'tri5b': (5, S((0,1,2),(0,3,4),(1,3),(2,4))),
 'tri6a': (6, S((0,1,2),(2,3,4),(4,5,0))),
 'tri6b': (6, S((0,1,2),(2,3,4),(4,5,0),(1,3))),
 'tri6c': (6, S((0,1,2),(2,3,4),(4,5,0),(1,3),(3,5),(5,1))),
 'q4':    (6, S((0,1,2,3),(0,4,5),(1,4),(2,5))),
 'tri4':  (6, S((0,1,3,4),(1,2,5),(0,2))),
 'pasch': (6, S((0,1,2),(0,3,4),(1,3,5),(2,4,5))),   # = K4 (points = edges, sets = vertex stars)
 'q5':    (6, S((0,1,2,3),(0,4,5),(1,4),(2,5),(3,5))),
}

def build(n, W, extra=0):
    N = 1 << n; K = sum(len(s) - 1 for s in W) - 1 + extra
    cnt = [0]
    def new():
        cnt[0] += 1; return cnt[0]
    cl = []
    zeros = [[Z for Z in range(N) if not any(Z >> u & 1 for u in s)] for s in W]
    def thin(T, guard):
        for s, zs in zip(W, zeros):
            for Z in zs:
                for u, v in itertools.combinations(s, 2):
                    zu, zv = Z | 1 << u, Z | 1 << v
                    cl.append([-guard, T[Z], -T[zu], -T[zv]]); cl.append([-guard, -T[Z], T[zu], T[zv]])
    def eqsel(p, X, Y, sg):
        for x in range(N):
            if sg == 0: cl.append([-p, -X[x], Y[x]]); cl.append([-p, X[x], -Y[x]])
            else: cl.append([-p, -X[x], -Y[x]]); cl.append([-p, X[x], Y[x]])
    F = []; info = []
    for i in range(K):
        Fi = [new() for _ in range(N)]; op = new(); sides = []; sel_info = []
        for _ in range(2):
            X = [new() for _ in range(N)]; g = new(); sel = [g]; thin(X, g); sj = [(g, 'thin', None)]
            for j in range(i):
                for sg in (0, 1):
                    p = new(); sel.append(p); eqsel(p, X, F[j], sg); sj.append((p, j, sg))
            cl.append(sel); sides.append(X); sel_info.append((X, sj))
        L, R = sides
        for x in range(N):
            cl.append([-op, -Fi[x], L[x], R[x]]); cl.append([-op, Fi[x], -L[x]]); cl.append([-op, Fi[x], -R[x]])
            cl.append([op, Fi[x], -L[x], -R[x]]); cl.append([op, -Fi[x], L[x]]); cl.append([op, -Fi[x], R[x]])
        F.append(Fi); info.append((op, Fi, sel_info))
    for s in W:
        o = [int(any(x >> u & 1 for u in s)) for x in range(N)]
        sel = []
        for i in range(K):
            for sg in (0, 1):
                p = new(); sel.append(p)
                for x in range(N):
                    cl.append([-p, F[i][x] if (o[x] ^ sg) else -F[i][x]])
        cl.append(sel)
    return cl, info, K

def verify(n, W, info, model):
    """Independent re-evaluation of a decoded program: rebuild each line from the model's structure, recompute with Python
    bit-ints, check thinness by the definition and that every OR(S_w) equals some +-line."""
    N = 1 << n; m = set(l for l in model if l > 0); full = (1 << N) - 1
    def tt(vars_): return sum(1 << x for x in range(N) if vars_[x] in m)
    lines = []
    for op, Fi, sel_info in info:
        sides = []
        for X, sj in sel_info:
            j, sg = next(((j, sg) for p, j, sg in sj if p in m and j != 'thin'), (None, None))
            if j is None:
                T = tt(X)
                for s in W:
                    for Z in range(N):
                        if any(Z >> u & 1 for u in s): continue
                        d = sum(((T >> (Z | 1 << u)) & 1) != ((T >> Z) & 1) for u in s)
                        assert d <= 1, 'not thin'
                sides.append(T)
            else:
                sides.append(lines[j] ^ (full if sg else 0))
        L, R = sides
        lines.append((L | R) if op in m else (L & R))
    for s in W:
        o = sum(1 << x for x in range(N) if any(x >> u & 1 for u in s))
        assert any(o == l or o == l ^ full for l in lines), 'output missing'
    return lines

def run(name, control=False, timeout=None, save=None):
    n, W = SYSTEMS[name]; base = sum(len(s) - 1 for s in W)
    t0 = time.time(); cl, info, K = build(n, W, 1 if control else 0)
    sv = Solver(name='cd15', bootstrap_with=cl)
    tm = threading.Timer(timeout, lambda: sv.interrupt()) if timeout else None
    if tm: tm.start()
    r = sv.solve_limited(expect_interrupt=True)
    if tm: tm.cancel()
    res = 'TIMEOUT' if r is None else ('SAT' if r else 'UNSAT')
    if r:
        model = sv.get_model(); verify(n, W, info, model)
        res = 'SAT(verified)'
        if save: json.dump({'system': name, 'W': W, 'lines': K, 'model_true_vars': [l for l in model if l > 0]}, open(save, 'w'))
    sv.delete()
    print(name, 'n=%d' % n, 'sets=%d' % len(W), 'base=%d' % base, 'lines=%d' % K, 'control' if control else 'violation',
          res, '%.1fs' % (time.time() - t0), flush=True)
    return res

if __name__ == '__main__':
    if '--list' in sys.argv:
        for k, (n, W) in SYSTEMS.items(): print(k, n, W, 'base', sum(len(s) - 1 for s in W))
        sys.exit()
    kw = {}
    for a in sys.argv[2:]:
        if a.startswith('--timeout='): kw['timeout'] = float(a[10:])
        if a.startswith('--save='): kw['save'] = a[7:]
    run(sys.argv[1], '--control' in sys.argv, **kw)
