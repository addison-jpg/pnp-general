# Front's request (helper tooling, not a proof): the Lean ChargeOK target. For each set S:
#   min over Q ⊇ S that are Good  [NOT true at z_Q, or NOT false at every e_u, u in [n] (all inputs)]  of |D(Q,S)|,
#   D(Q,S) = gate wires w with w(z_Q) = 0 and w(e_u) = 1 for >= 2 u in S   (original circuit, not C1).
# Violation: Σ_S min |D| > s (circuit size). Reports violations among CLEAN circuits: no two gates compute the same
# function, no gate equals (as a function) one of its inputs, no constant gate. NOT live (build_live).
#   python3 research/tools/l951_charging/dmin_scaffold.py SYS|rand:SEED:K [cap_per_cell] [seconds] [--sizes 2,3,4,5,6]
import sys, time, random, itertools, collections
sys.path.insert(0, 'research/tools/l951_charging'); import live951, clean951_scaffold as clean951
from pysat.solvers import Cadical153
CLEAN = '--clean' in sys.argv; ESS = '--essential' in sys.argv; sys.argv = [a for a in sys.argv if a != '--essential']; argv = [a for a in sys.argv[1:] if a != '--clean']; sizes = (2, 3, 4, 5)
if '--sizes' in argv:
    i = argv.index('--sizes'); sizes = tuple(int(v) for v in argv[i + 1].split(',')); del argv[i:i + 2]
SYS = {'p6': (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]), 'k4': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]), 'c5': (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]), 'gadget': (5, [(0, 1), (0, 2), (3, 4)]), 'pasch': (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]), 'p2': (6, [(0, 1, 2), (0, 3, 4), (1, 3), (2, 4), (5, 0)]),
       'k4e': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]), 'c5': (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
       'k4': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])}
SYS['fano'] = (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)])
SYS['mk'] = (8, [tuple(sorted({i, (i + 1) % 8, (i + 3) % 8})) for i in range(8)])
SYS['pappus'] = (9, [(0, 1, 2), (3, 4, 5), (6, 7, 8), (0, 4, 8), (0, 5, 7), (1, 3, 8), (1, 5, 6), (2, 3, 7), (2, 4, 6)])
_pairs = [p for p in itertools.combinations(range(5), 2)]
SYS['desargues'] = (10, [tuple(_pairs.index(p) for p in itertools.combinations(t, 2)) for t in itertools.combinations(range(5), 3)])
for _k in ('fano', 'mk', 'pappus', 'desargues'):
    _n, _ss = SYS[_k]
    assert all(len(set(a) & set(b)) <= 1 for a, b in itertools.combinations(_ss, 2)) and set().union(*map(set, _ss)) == set(range(_n)), _k
spec = argv[0]; CAP = int(argv[1]) if len(argv) > 1 else 500; SECS = float(argv[2]) if len(argv) > 2 else 900
if spec.startswith('rand'):
    _, seed, K = spec.split(':'); rng = random.Random(int(seed)); todo = []
    while len(todo) < int(K):
        n = rng.randint(4, 6); m = rng.randint(3, 6); sets = []
        for _ in range(300):
            S = tuple(sorted(rng.sample(range(n), rng.choice((2, 2, 3)))))
            if S not in sets and all(len(set(S) & set(T)) <= 1 for T in sets): sets.append(S)
            if len(sets) == m: break
        if len(sets) == m and set().union(*map(set, sets)) == set(range(n)): todo.append((n, sets))
else: todo = [SYS[spec]]
def run(n, sets):
    full = (1 << n) - 1; base = sum(len(S) - 1 for S in sets); t0 = time.time()
    for d in sizes:
        s = base + d; tot = clean = viol = cviol = ndviol = nd = tight = 0; ex = 0; slack = collections.Counter()
        for p in range(s - 1):
            cl, SEL, O = (clean951.build_clean if CLEAN else live951.build_live)(n, sets, s, p, [])
            for k in range(s):
                if k != p: cl += [[-SEL[k][0][i], -SEL[k][1][i]] for i in range(n + k)]   # no op(w, w)
            sol = Cadical153(bootstrap_with=cl); found = 0
            while found < CAP and time.time() - t0 < SECS:
                if not sol.solve(): ex += 1; break
                M = sol.get_model(); gates, outs = live951.decode(M, n, s, p, SEL, O); found += 1; tot += 1
                pos = set(l for l in M if l > 0)
                sol.add_clause([-SEL[k][0][gates[k][1]] for k in range(s)] + [-SEL[k][1][gates[k][2]] for k in range(s) if k != p]
                               + [(-SEL[k][2] if SEL[k][2] in pos else SEL[k][2]) for k in range(s) if k != p])
                vals = [live951.wires(n, gates, x) for x in range(1 << n)]
                if ESS:
                    def wrong(c):
                        for x in range(1 << n):
                            w = [(x >> i) & 1 for i in range(n)]
                            for op, a, b in gates: w.append(c if op == 'not' else (w[a] & w[b] if op == 'and' else w[a] | w[b]))
                            if any(w[o] != int(any(x >> v & 1 for v in S)) for S, o in zip(sets, outs)): return True
                        return False
                    if not (wrong(0) and wrong(1)): tot -= 1; continue
                col = [tuple(v[w] for v in vals) for w in range(n + s)]
                isclean = (len(set(col[n:])) == s and all(len(set(c)) == 2 for c in col[n:])
                           and all(col[n + k] != col[a] and col[n + k] != col[b] for k, (op, a, b) in enumerate(gates)))
                # live gates: every gate in the cone of some output
                cone = set(); st = list(outs)
                while st:
                    w = st.pop()
                    if w < n or w in cone: continue
                    cone.add(w); st += [gates[w - n][1], gates[w - n][2]]
                nodead = len(cone) == s
                Nw = n + p; tot_min = 0
                for S in sets:
                    sm = sum(1 << v for v in S); rest = [v for v in range(n) if v not in S]; best = None
                    notfalse_units = all(vals[1 << u][Nw] == 0 for u in range(n))   # Lean Good: NOT false at e_u for EVERY u in [n]
                    for r in range(len(rest) + 1):
                        for R in itertools.combinations(rest, r):
                            z = full & ~(sm | sum(1 << v for v in R))
                            if not (vals[z][Nw] == 1 or notfalse_units): continue
                            D = sum(1 for w in range(n, n + s) if vals[z][w] == 0 and sum(vals[1 << u][w] for u in S) >= 2)
                            best = D if best is None else min(best, D)
                    tot_min += best
                sl = s - tot_min; slack[min(sl, 5)] += 1
                if sl == 0 and isclean:
                    tight += 1
                    if tight <= 3: print(f'  TIGHT nodead={nodead} n={n} sets={sets} size={s} p={p} Σmin|D|={tot_min} gates={gates} outs={outs}', flush=True)
                if sl < 0:
                    viol += 1
                    if isclean and nodead: ndviol += 1
                    if isclean:
                        cviol += 1
                        if cviol <= 3: print(f'  CLEAN-VIOLATION nodead={nodead} n={n} sets={sets} size={s} p={p} Σmin|D|={tot_min} gates={gates} outs={outs}', flush=True)
                clean += isclean; nd += isclean and nodead
            sol.delete()
        print(f'n={n} {sets} size={s} (base+{d}) circuits={tot} clean={clean} violations={viol} clean_violations={cviol} clean_nodead={nd} clean_nodead_violations={ndviol} tight={tight} '
              f'slack_hist(s-Σmin|D|, capped 5)={dict(sorted(slack.items()))} exhausted={ex}/{s-1} ({time.time()-t0:.0f}s)', flush=True)
for n, sets in todo: run(n, sets)
