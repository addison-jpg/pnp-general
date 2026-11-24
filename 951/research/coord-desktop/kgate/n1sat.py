# Abstract "N1" search: k OR-gates G=s∨t given as real functions (monotone on D={h=0} and on D^c separately),
# such that every zero point z of every set w has some G with G(z)=0 and B_z(s),B_z(t) nonempty & disjoint in S_w.
import sys, itertools
from pysat.solvers import Solver
def solve(n, sets, hfun, k, extra=None, verbose=True):
    P = range(1<<n)
    heavy = [hfun(A) for A in P]
    vid = {}
    def v(*key):
        if key not in vid: vid[key] = len(vid)+1
        return vid[key]
    S = Solver(name='cadical153')
    for G in range(k):
        for side in 'st':
            for A in P:
                for u in range(n):
                    if not A>>u&1:
                        B = A|1<<u
                        if heavy[A]==heavy[B]:
                            S.add_clause([-v(G,side,A), v(G,side,B)])
    masks = [sum(1<<u for u in s) for s in sets]
    for i,s in enumerate(sets):
        for z in P:
            if z & masks[i]: continue
            sel = [v('c',i,z,G) for G in range(k)]
            S.add_clause(sel)
            for G in range(k):
                c = v('c',i,z,G)
                S.add_clause([-c, -v(G,'s',z)]); S.add_clause([-c, -v(G,'t',z)])
                S.add_clause([-c]+[v(G,'s',z|1<<u) for u in s])
                S.add_clause([-c]+[v(G,'t',z|1<<u) for u in s])
                for u in s:
                    S.add_clause([-c, -v(G,'s',z|1<<u), -v(G,'t',z|1<<u)])
    if extra: extra(S, v)
    ok = S.solve()
    if not ok: return None
    m = set(x for x in S.get_model() if x>0)
    fun = {(G,side):[A for A in P if v(G,side,A) in m] for G in range(k) for side in 'st'}
    sel = {(i,z):[G for G in range(k) if v('c',i,z,G) in m] for i in range(len(sets)) for z in P if not z&masks[i]}
    return fun, sel
if __name__=='__main__':
    tests = {
     'tri_n3_mono': (3, [(0,1),(1,2),(0,2)], lambda A:0),
     'tri_n3_h012': (3, [(0,1),(1,2),(0,2)], lambda A: int(A&7!=0)),
     'tri_n4_h012': (4, [(0,1,3),(1,2),(0,2)], lambda A: int(A&7!=0)),
     'tri_n6_mono': (6, [(0,1,3),(1,2,4),(0,2,5)], lambda A:0),
     'tri_n6_h012': (6, [(0,1,3),(1,2,4),(0,2,5)], lambda A: int(A&7!=0)),
     'tri_n9_h012': (9, [(0,1,3,4),(1,2,5,6),(0,2,7,8)], lambda A: int(A&7!=0)),
     'disj_n6_mono': (6, [(0,1),(2,3),(4,5)], lambda A:0),
    }
    for name,(n,sets,h) in tests.items():
        r = solve(n,sets,h,2)
        print(name, 'k=2:', 'SAT' if r else 'UNSAT')
