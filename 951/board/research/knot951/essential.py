"""essential.py: min size with EXACTLY k NOTs, each one essential (replacing that single NOT by const 0 or by
const 1 makes some output wrong).  sym=False (the nodd normal form is not sound here).  k=1 must reproduce E4."""
import sys, json, time
sys.path.insert(0, '/home/user/ku951'); sys.path.insert(0, '/home/user/coord951/tools')
import knot
from w951 import Circuit
def check_ess(n, sets, gates, outs):
    tt = [knot.or_table(n, S) for S in sets]; full = (1 << (1 << n)) - 1
    for f, g in enumerate(gates):
        if g[0] != 'not': continue
        for c in (0, full):
            t = knot.tables(n, [])
            for j, h in enumerate(gates):
                t.append(c if j == f else (full ^ t[h[1]] if h[0] == 'not' else t[h[1]] & t[h[2]] if h[0] == 'and' else t[h[1]] | t[h[2]]))
            if all(t[o] == T for o, T in zip(outs, tt)): return False
    return True
SYS = {'pair': [[0, 1]], 'triple': [[0, 1, 2]], 'path2': [[0, 1], [1, 2]], 'triangle': [[0, 1], [1, 2], [0, 2]],
       'quad4': [[0, 1, 2, 3]], 'star2x3': [[0, 1, 2], [0, 3, 4]], 'path3x3': [[0, 1, 2], [2, 3, 4]]}
names = sys.argv[2:] or list(SYS)
ks = [int(c) for c in sys.argv[1]]
for name in names:
    sets = SYS[name]; n, b = knot.nmax(sets), knot.base(sets)
    for k in ks:
        t0 = time.time(); s = b
        while True:
            r = knot.solve(n, sets, s, k, sym=False, exact_k=True, essential=True, full=True)
            if r: break
            s += 1
        assert check_ess(n, sets, *r) and knot.verify(n, sets, *r, k)
        if k == 1: assert Circuit(n, [tuple(g) for g in r[0]], sets, r[1]).is_essential()
        rec = dict(name=name, n=n, sets=sets, base=b, k=k, min_essential=s, excess=s - b, gates=r[0], outs=r[1], secs=round(time.time() - t0, 1))
        print(json.dumps(rec), flush=True)
        open('/home/user/ku951/essential.jsonl', 'a').write(json.dumps(rec) + '\n')
