# Exhaustive near-optimum check for the L-meta-951 charging inequality (helper tooling, not a proof).
# For each set system and each size s in (base+1, base+2), base = sum(|S|-1), and each NOT position p:
# enumerate EVERY circuit from ov951.build (NOT at p, read later), blocking each one found (inputs and op of
# every gate) until UNSAT, and run merge951b.analyse2 on it. Reports whether each cell was exhausted or
# hit the cap, plus the max excess seen. merge951b.py's sampling took 5 circuits per cell; this takes all.
#   python3 tools/l951_charging/exh951.py [cap_per_cell] [seconds_per_system]
import sys, time, collections
src = open('tools/l951_charging/merge951b.py').read().split('t0=time.time()')[0]
exec(src)  # brings build, decode, analyse2 (and ov951's helpers) into scope
from pysat.solvers import Glucose4

CAP = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
SECS = float(sys.argv[2]) if len(sys.argv) > 2 else 300
systems = [(5, [(0, 1, 2), (0, 3, 4)]), (5, [(0, 1, 2), (2, 3), (3, 4, 0)]),
           (6, [(0, 1), (2, 3), (4, 5), (0, 2, 4)]), (6, [(0, 1, 2), (3, 4, 5), (0, 3)]),
           (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)])]
for n, sets in systems:
    base = sum(len(S) - 1 for S in sets)
    t0 = time.time()
    for s in (base + 1, base + 2):
        total = 0; hist = collections.Counter(); cells_done = 0; cells = 0; hh = 0
        for p in range(s - 1):
            cells += 1
            cl, SEL, O = build(n, sets, s, p, [])
            solver = Glucose4(bootstrap_with=cl)
            found = 0; exhausted = False
            while found < CAP and time.time() - t0 < SECS:
                if not solver.solve():
                    exhausted = True; break
                M = solver.get_model()
                gates, outs = decode(M, n, s, p, SEL, O)
                kinds, dbl = analyse2(n, sets, gates, p)
                hist[dbl] += 1; hh += kinds.count('H') >= 2; found += 1
                pos = set(l for l in M if l > 0)
                block = [-SEL[k][0][gates[k][1]] for k in range(s)]
                block += [-SEL[k][1][gates[k][2]] for k in range(s) if k != p]
                block += [(-SEL[k][2] if SEL[k][2] in pos else SEL[k][2]) for k in range(s) if k != p]
                solver.add_clause(block)
            solver.delete()
            total += found; cells_done += exhausted
        print(f'{sets} size={s} (base+{s - base}): circuits={total} exhausted_cells={cells_done}/{cells} '
              f'>=2hard={hh} excess_histogram={dict(hist)} ({time.time() - t0:.0f}s)', flush=True)
