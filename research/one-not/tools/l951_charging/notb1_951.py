# Request 3 (helper tooling, not a proof): test 'NOT read => size >= base+2' on bigger systems.
# Random set systems, n=7..9 inputs (every input in some set), 4-5 sets of size 2-3, pairwise |Si ∩ Sj| <= 1.
# For each NOT position p, ov951.build(n, sets, base+1, p) asks for a base+1 gate circuit whose NOT at p is read.
# Expected UNSAT in every cell; a SAT cell is printed with the circuit and re-checked on all rows.
#   python3 research/tools/l951_charging/notb1_951.py SEED NSYS [cell_timeout] [nmin] [nmax]
import sys, random, time, itertools, threading
src = open('research/tools/l951_charging/ov951.py').read().split('random.seed(')[0]
exec(src)
from pysat.solvers import Cadical153
seed, nsys = int(sys.argv[1]), int(sys.argv[2])
TMO = float(sys.argv[3]) if len(sys.argv) > 3 else 900
nmin = int(sys.argv[4]) if len(sys.argv) > 4 else 7
nmax = int(sys.argv[5]) if len(sys.argv) > 5 else 9
rng = random.Random(seed)
def gen():
    while True:
        n = rng.randint(nmin, nmax); m = rng.randint(4, 5); sets = []
        for _ in range(500):
            S = tuple(sorted(rng.sample(range(n), rng.choice((2, 3, 3)))))
            if S not in sets and all(len(set(S) & set(T)) <= 1 for T in sets): sets.append(S)
            if len(sets) == m: break
        if len(sets) == m and set().union(*map(set, sets)) == set(range(n)): return n, sets
def check(n, sets, gates, outs):
    for x in range(1 << n):
        w = wires(n, gates, x)
        for S, o in zip(sets, outs):
            if w[o] != int(any(x >> v & 1 for v in S)): return False
    return True
for _ in range(nsys):
    n, sets = gen(); base = sum(len(S) - 1 for S in sets); s = base + 1; t0 = time.time(); res = []
    for p in range(s - 1):
        cl, SEL, O = build(n, sets, s, p, [])
        sol = Cadical153(bootstrap_with=cl); tm = threading.Timer(TMO, sol.interrupt); tm.start()
        r = sol.solve_limited(expect_interrupt=True); tm.cancel()
        res.append('T' if r is None else ('S' if r else 'U'))
        if r:
            g, o = decode(sol.get_model(), n, s, p, SEL, O)
            print(f'  SAT n={n} sets={sets} p={p} gates={g} outs={o} recheck={check(n, sets, g, o)}', flush=True)
        sol.delete()
    print(f'n={n} sets={sets} base={base} size={s} cells(p=0..{s-2})={"".join(res)} '
          f'{"ALL-UNSAT" if set(res) == {"U"} else ""} ({time.time() - t0:.0f}s)', flush=True)
