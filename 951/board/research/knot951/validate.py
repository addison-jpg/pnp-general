"""Validation of knot.py: k=0 must give exactly base; sym on/off, cegar/full must agree; k=1 vs w951.sat."""
import sys, time, json
sys.path.insert(0, '/home/user/ku951'); sys.path.insert(0, '/home/user/coord951/tools')
import knot
from w951 import sat as wsat
from pysat.solvers import Solver

SYS = {
    'pair': [[0, 1]],
    'triple': [[0, 1, 2]],
    'path2': [[0, 1], [1, 2]],
    'triangle': [[0, 1], [1, 2], [0, 2]],
    'star2x3': [[0, 1, 2], [0, 3, 4]],
    'path3x3': [[0, 1, 2], [2, 3, 4]],
    'tri3': [[0, 1, 2], [2, 3, 4], [4, 5, 0]],
    'pasch': [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]],
    'quad4': [[0, 1, 2, 3]],
}


def w951_one_not(n, sets, s):
    """SAT with <= s gates and exactly one NOT (any position), w951 channel encoding."""
    for p in range(s):
        cl, SEL, O = wsat.build_channel(n, sets, s, p)
        with Solver(name='cadical195', bootstrap_with=cl) as sol:
            if sol.solve():
                return True
    return False


out = []
for name, sets in SYS.items():
    n, b = knot.nmax(sets), knot.base(sets)
    t0 = time.time()
    # k = 0: SAT at base, UNSAT at base-1, all four encoder variants
    for sym in (True, False):
        for full in (True, False):
            assert knot.solve(n, sets, b, 0, sym=sym, full=full) is not None, (name, 'k0 base')
            assert knot.solve(n, sets, b - 1, 0, sym=sym, full=full) is None, (name, 'k0 base-1')
    # k = 1, 2, all: variants must agree at base-1 and base-2
    line = {'name': name, 'n': n, 'base': b}
    for k in (1, 2, 3, b):
        for s in (b - 1, b - 2):
            if s < 1:
                continue
            rs = [knot.solve(n, sets, s, k, sym=sym, full=full) is not None
                  for sym in (True, False) for full in (True, False)]
            assert len(set(rs)) == 1, (name, k, s, rs)
            line['k%d_s%d' % (k, s)] = rs[0]
    # exactly-one-NOT cross check against w951.sat at base-1 (w951 forces the NOT to be read)
    mine = knot.solve(n, sets, b - 1, 1, sym=False, exact_k=True) is not None
    theirs = w951_one_not(n, sets, b - 1) if b - 1 >= 2 else None
    line['k1exact_mine'], line['k1_w951'] = mine, theirs
    if theirs is not None:
        assert mine == theirs, (name, mine, theirs)
    line['secs'] = round(time.time() - t0, 1)
    print(json.dumps(line), flush=True)
    out.append(line)
json.dump(out, open('/home/user/ku951/validate_out.json', 'w'), indent=1)
print('VALIDATION OK')
