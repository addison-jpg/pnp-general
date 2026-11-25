# C1 lemma support (helper tooling, not a proof): on correct live-NOT circuits where C1 (NOT := 1) is WRONG,
# measure which gates pay. B = outputs C1 gets wrong ("bad"), G = good outputs. cone(G) = gates in the cones of
# good outputs. Since C1 is correct on G, cone(G) minus {NOT} with NOT:=1 is a monotone circuit for G, so
# |cone(G) \ {N}| >= Σ_G(|S|-1). Reports  extra = s - |cone(G) \ {N}| - Σ_B(|S|-1)  (gates the bad sets pay beyond
# their own merges), whether N and its readers lie in cone(G), and #readers of N.
#   python3 research/tools/l951_charging/c1pay_scaffold.py SYSIDX|rand:SEED:K [cap_per_cell] [seconds] [--sizes 3,4]
import sys, time, random, collections
sys.path.insert(0, 'research/tools/l951_charging'); import live951
from pysat.solvers import Cadical153
argv = sys.argv[1:]; sizes = (3,)
if '--sizes' in argv:
    i = argv.index('--sizes'); sizes = tuple(int(v) for v in argv[i + 1].split(',')); del argv[i:i + 2]
SYSTEMS = [(5, [(0, 1, 2), (0, 3, 4)]), (5, [(0, 1, 2), (2, 3), (3, 4, 0)]), (6, [(0, 1), (2, 3), (4, 5), (0, 2, 4)]),
           (6, [(0, 1, 2), (3, 4, 5), (0, 3)]), (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]),
           (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]), (6, [(0, 1, 2), (0, 3, 4), (1, 3), (2, 4), (5, 0)]),
           (5, [(0, 3, 4), (1, 3), (0, 1, 2)]), (6, [(0, 1, 4), (2, 3, 4), (0, 2), (1, 2), (1, 3, 5)])]
def cone(n, gates, outs):
    C = set(); st = list(outs)
    while st:
        w = st.pop()
        if w < n or w in C: continue
        C.add(w); st += [gates[w - n][1], gates[w - n][2]]
    return C
def wires1(n, gates, x, p):  # C1: NOT := 1
    w = [(x >> i) & 1 for i in range(n)]
    for k, (op, a, b) in enumerate(gates):
        w.append(1 if k == p else (w[a] & w[b] if op == 'and' else w[a] | w[b]))
    return w
spec = argv[0]; CAP = int(argv[1]) if len(argv) > 1 else 400; SECS = float(argv[2]) if len(argv) > 2 else 900
todo = [SYSTEMS[int(spec)]]
for n, sets in todo:
    base = sum(len(S) - 1 for S in sets); t0 = time.time()
    for d in sizes:
        s = base + d; tot = 0; bad_c = 0; H = collections.Counter(); ex = 0; shown = 0
        for p in range(s - 1):
            cl, SEL, O = live951.build_live(n, sets, s, p, [])
            cl += [[-SEL[p][0][i]] for i in range(n)]  # h a gate
            sol = Cadical153(bootstrap_with=cl); found = 0
            while found < CAP and time.time() - t0 < SECS:
                if not sol.solve(): ex += 1; break
                M = sol.get_model(); gates, outs = live951.decode(M, n, s, p, SEL, O); found += 1; tot += 1
                pos = set(l for l in M if l > 0)
                sol.add_clause([-SEL[k][0][gates[k][1]] for k in range(s)] + [-SEL[k][1][gates[k][2]] for k in range(s) if k != p]
                               + [(-SEL[k][2] if SEL[k][2] in pos else SEL[k][2]) for k in range(s) if k != p])
                bad = [i for i, (S, o) in enumerate(zip(sets, outs))
                       if any(wires1(n, gates, x, p)[o] != int(any(x >> v & 1 for v in S)) for x in range(1 << n))]
                if not bad: continue
                bad_c += 1; good = [i for i in range(len(sets)) if i not in bad]
                CG = cone(n, gates, [outs[i] for i in good]) - {n + p}
                readers = [k for k, (op, a, b) in enumerate(gates) if k != p and n + p in (a, b)]
                extra = s - len(CG) - sum(len(sets[i]) - 1 for i in bad)
                key = (extra, len(bad), len(readers), any(n + r in CG for r in readers))
                H[key] += 1
                if extra < 3 and shown < 3:
                    shown += 1; print(f'  LOW extra={extra} size={s} p={p} bad={bad} gates={gates} outs={outs}', flush=True)
            sol.delete()
        print(f'n={n} {sets} size={s} (base+{d}) live-hgate circuits={tot} C1-wrong={bad_c} exhausted={ex}/{s-1}', flush=True)
        print('   (extra, #bad outputs, #readers of N, a reader in cone(good)) -> count:', dict(sorted(H.items())), flush=True)
