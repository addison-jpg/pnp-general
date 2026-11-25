# Front's request (helper tooling, not a proof): live-NOT circuits whose NOT reads a gate h = OR(x_a, x_b) (a != b
# inputs). C1 = circuit with NOT := 1. For each set S: T_S = S ∪ {a,b}, zero point z = 0 on T_S, 1 elsewhere
# (h(z)=0, so C1 = C at z), test points e_u (u in S). Cone-restricted union-find over the gates in the cone of o_S,
# evaluated in C1: an OR gate g with g(z)=0 whose two inputs have nonempty S-sets in different classes is a charge
# of S. Reports per circuit: #gates charged twice or more, #AND gates, #OR gates charged by no set; and the key
# question: is any gate charged by a set through a (a in S, b not in S) AND a set through b (b in S, a not in S)?
#   python3 research/tools/l951_charging/abcharge_scaffold.py SYS [cap_per_cell] [seconds] [--sizes 2,3]
#   SYS = pasch | k4e | fano | p6   (p6 = 6-cycle)
import sys, time, collections
sys.path.insert(0, 'research/tools/l951_charging'); import live951
from pysat.solvers import Cadical153
argv = sys.argv[1:]; sizes = (2, 3)
if '--sizes' in argv:
    i = argv.index('--sizes'); sizes = tuple(int(v) for v in argv[i + 1].split(',')); del argv[i:i + 2]
SYS = {'pasch': (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]),
       'k4e': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]),
       'fano': (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]),
       'p6': (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)])}
name = argv[0]; n, sets = SYS[name]; CAP = int(argv[1]) if len(argv) > 1 else 500; SECS = float(argv[2]) if len(argv) > 2 else 1200
def cone(gates, o):
    C = set(); st = [o]
    while st:
        w = st.pop()
        if w < n or w in C: continue
        C.add(w); st += [gates[w - n][1], gates[w - n][2]]
    return C
def w1(gates, x, p):
    w = [(x >> i) & 1 for i in range(n)]
    for k, (op, a, b) in enumerate(gates):
        w.append(1 if k == p else (w[a] & w[b] if op == 'and' else w[a] | w[b]))
    return w
def analyse(gates, outs, p):
    hw = gates[p][1]; _, a, b = gates[hw - n]; full = (1 << n) - 1; charges = collections.defaultdict(list)
    for i, (S, o) in enumerate(zip(sets, outs)):
        T = set(S) | {a, b}; z = full & ~sum(1 << v for v in T)
        wz = w1(gates, z, p); wp = {u: w1(gates, 1 << u, p) for u in S}; C = cone(gates, o)
        assert wz[o] == 0
        par = {u: u for u in S}
        def f(x):
            while par[x] != x: x = par[x]
            return x
        Aset = lambda w: [u for u in S if wp[u][w]] if wz[w] == 0 else None
        cnt = 0
        for k, (op, x, y) in enumerate(gates):
            if op != 'or' or n + k not in C or wz[n + k] != 0: continue
            Ax, Ay = Aset(x), Aset(y)
            if Ax and Ay and f(Ax[0]) != f(Ay[0]): par[f(Ax[0])] = f(Ay[0]); charges[k].append(i); cnt += 1
        assert cnt >= len(S) - 1, (S, cnt, gates, outs)
    side = lambda i: 'a' if a in sets[i] and b not in sets[i] else 'b' if b in sets[i] and a not in sets[i] else 'ab' if a in sets[i] else '-'
    dbl = [k for k, L in charges.items() if len(L) >= 2]
    ab = [k for k in dbl if {'a', 'b'} <= {side(i) for i in charges[k]}]
    kinds = sorted(tuple(sorted(side(i) for i in charges[k])) for k in dbl)
    nand = sum(op == 'and' for op, _, _ in gates)
    unch = sum(1 for k, (op, _, _) in enumerate(gates) if op == 'or' and k not in charges and k != hw - n)
    return len(dbl), ab, nand, unch, tuple(kinds), (a, b)
print(f'{name} n={n} sets={sets}', flush=True)
base = sum(len(S) - 1 for S in sets); t0 = time.time()
for d in sizes:
    s = base + d; tot = 0; H = collections.Counter(); abhit = 0; shown = 0; ex = 0
    for p in range(1, s - 1):
        cl, SEL, O = live951.build_live(n, sets, s, p, [])
        A, B, op = SEL[p]
        cl += [[-A[i]] for i in range(n)]
        for j in range(n, n + p):
            k = j - n; Ak, Bk, opk = SEL[k]
            cl += [[-A[j], -opk], [-A[j]] + [Ak[i] for i in range(n)], [-A[j]] + [Bk[i] for i in range(n)]]
            cl += [[-A[j], -Ak[i], -Bk[i]] for i in range(n)]        # a != b
        sol = Cadical153(bootstrap_with=cl); found = 0
        while found < CAP and time.time() - t0 < SECS:
            if not sol.solve(): ex += 1; break
            M = sol.get_model(); gates, outs = live951.decode(M, n, s, p, SEL, O); found += 1; tot += 1
            pos = set(l for l in M if l > 0)
            sol.add_clause([-SEL[k][0][gates[k][1]] for k in range(s)] + [-SEL[k][1][gates[k][2]] for k in range(s) if k != p]
                           + [(-SEL[k][2] if SEL[k][2] in pos else SEL[k][2]) for k in range(s) if k != p])
            nd, ab, nand, unch, kinds, hab = analyse(gates, outs, p)
            H[(nd, nand, unch)] += 1; H[('dbl_kinds', kinds)] += 1
            if ab:
                abhit += 1
                if shown < 3: shown += 1; print(f'  AB-DOUBLE size={s} h=x{hab[0]}|x{hab[1]} p={p} gates={gates} outs={outs} at={ab}', flush=True)
        sol.delete()
    print(f'{name} size={s} (base+{d}) circuits={tot} exhausted_cells={ex}/{s-2} a-b_double_circuits={abhit} ({time.time()-t0:.0f}s)', flush=True)
    print('   (#double-charged, #AND, #uncharged OR) ->', dict(sorted((k, v) for k, v in H.items() if k[0] != 'dbl_kinds')), flush=True)
    print('   double-charge side kinds ->', dict((k[1], v) for k, v in H.items() if k[0] == 'dbl_kinds'), flush=True)
