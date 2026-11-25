# Generate CLEAN live-NOT circuits (scaffold's build_clean) and test the Lean inequality
#   sum_w min_{Q ⊇ S_w, Good(Q)} |D(Q, S_w)| <= s
# with Lean's Good: NOT true at z_Q, OR NOT false at e_u for EVERY input u.
import sys, json, time, random, itertools
sys.path.insert(0, 'research/tools/l951_charging'); import clean951_scaffold as C
from pysat.solvers import Cadical153
SYS = {'K4e': (4, [(0,1),(0,2),(0,3),(1,2),(1,3)]), 'C5': (5, [(0,1),(1,2),(2,3),(3,4),(4,0)]),
       'gad': (5, [(0,1),(0,2),(3,4)]), 'P2': (6, [(0,1,2),(0,3,4),(1,3),(2,4),(5,0)]),
       'tri': (6, [(0,1,2),(2,3,4),(4,5,0)])}
def ev(n, gates, x):
    w = list(x)
    for op, a, b in gates:
        w.append(1 - w[a] if op == 'not' else (w[a] & w[b] if op == 'and' else w[a] | w[b]))
    return w
def slack(n, sets, gates):
    s = len(gates); nw = n + [k for k, g in enumerate(gates) if g[0] == 'not'][0]
    unit = [ev(n, gates, [int(v == u) for v in range(n)]) for u in range(n)]
    du = all(unit[u][nw] == 0 for u in range(n)); tot = 0
    for S in sets:
        R = set(S); best = None; rest = [v for v in range(n) if v not in R]
        for r in range(len(rest) + 1):
            for ex in itertools.combinations(rest, r):
                Q = R | set(ex); z = ev(n, gates, [0 if v in Q else 1 for v in range(n)])
                if not (z[nw] == 1 or du): continue
                d = sum(1 for i in range(n, n + s) if z[i] == 0 and sum(unit[u][i] for u in R) >= 2)
                best = d if best is None else min(best, d)
        tot += best
    return s - tot
name, extra, cap, secs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
n, sets = SYS[name]; base = sum(len(S) - 1 for S in sets); s = base + extra
t0 = time.time(); k = 0; minsl = 99; viol = []; ESS = [0]; NONESS = [0]
for p in range(1, s - 1):
    if time.time() - t0 > secs: break
    cl, SEL, O = C.build_clean(n, sets, s, p, [])
    cl = cl + [[SEL[p][0][w] for w in range(n, n + p)]]
    sol = Cadical153(bootstrap_with=cl); rng = random.Random(p)
    sol.set_phases([v if rng.random() < .5 else -v for v in range(1, sol.nof_vars() + 1)])
    f = 0
    while f < cap and time.time() - t0 < secs and sol.solve():
        M = sol.get_model(); gates, outs = C.decode(M, n, s, p, SEL, O)
        sl = slack(n, sets, gates); k += 1; f += 1
        def okN(val):
            for xi in itertools.product([0, 1], repeat=n):
                w = list(xi)
                for op, a, b in gates: w.append(val if op == 'not' else (w[a] & w[b] if op == 'and' else w[a] | w[b]))
                if any(w[o] != int(any(xi[v] for v in S)) for o, S in zip(outs, sets)): return False
            return True
        ess = not okN(0) and not okN(1)
        if ess:
            ESS[0] += 1; minsl = min(minsl, sl)
            if sl < 0: viol.append((gates, outs))
        elif sl < 0: NONESS[0] += 1
        pos = set(l for l in M if l > 0)
        block = [-SEL[q][0][gates[q][1]] for q in range(s)] + [-SEL[q][1][gates[q][2]] for q in range(s) if q != p]
        block += [(-SEL[q][2] if SEL[q][2] in pos else SEL[q][2]) for q in range(s) if q != p]
        block += [-O[i][outs[i]] for i in range(len(sets))]
        sol.add_clause(block)
    sol.delete()
print(name, 'base+%d' % extra, 'clean', k, 'essential', ESS[0], 'min slack(ess)', minsl, 'ESSENTIAL VIOLATIONS', len(viol), 'removable-NOT violations', NONESS[0], 'sec', round(time.time() - t0), flush=True)
for g, o in viol[:2]: print('  VIOL', g, o, flush=True)
