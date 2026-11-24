# Stress test for front's substitution lemma (helper tooling, not a proof): in a correct circuit whose NOT
# (gate p) lies in an output cone, every read of the NOT wire can be replaced by a constant 0/1 or by an earlier
# wire that does not depend on the NOT, keeping all outputs correct. Tries ALL combinations over the reads.
# Enumerates live-NOT circuits (live951.build_live, h a gate wire with --hgate) and prints every failure.
#   python3 tools/l951_charging/subst951_scaffold.py SYSIDX|rand:SEED:K [cap_per_cell] [seconds] [--hgate] [--sizes 3,4,5]
import sys, time, random, itertools, collections
sys.path.insert(0, 'tools/l951_charging'); import live951
from pysat.solvers import Cadical153
HG = '--hgate' in sys.argv; argv = [a for a in sys.argv[1:] if a != '--hgate']
sizes = (2, 3, 4)
if '--sizes' in argv:
    i = argv.index('--sizes'); sizes = tuple(int(v) for v in argv[i + 1].split(',')); del argv[i:i + 2]
SYSTEMS = [(5, [(0, 1, 2), (0, 3, 4)]), (5, [(0, 1, 2), (2, 3), (3, 4, 0)]), (6, [(0, 1), (2, 3), (4, 5), (0, 2, 4)]),
           (6, [(0, 1, 2), (3, 4, 5), (0, 3)]), (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]),
           (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]), (7, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 6), (5, 6)]),
           (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (2, 4)]), (6, [(0, 1, 2), (0, 3, 4), (1, 3), (2, 4), (5, 0)]),
           (7, [(0, 1), (0, 2), (1, 3), (2, 3), (4, 5, 6), (3, 4)]), (7, [(0, 1, 2, 3), (0, 4), (1, 5), (2, 6), (4, 5, 6)])]
def randsys(rng):
    while True:
        n = rng.randint(5, 7); m = rng.randint(2, 5); sets = []
        for _ in range(500):
            S = tuple(sorted(rng.sample(range(n), rng.choice((2, 2, 3, 3, 4)))))
            if S not in sets and all(len(set(S) & set(T)) <= 1 for T in sets): sets.append(S)
            if len(sets) == m: break
        if len(sets) == m and set().union(*map(set, sets)) == set(range(n)): return n, sets
def evalc(n, gates, x, p, subs):
    # subs: dict (gate k, slot 1|2) -> 'C0' | 'C1' | wire index
    w = [(x >> i) & 1 for i in range(n)]
    for k, (op, a, b) in enumerate(gates):
        A = subs.get((k, 1), a); B = subs.get((k, 2), b)
        va = 0 if A == 'C0' else 1 if A == 'C1' else w[A]
        vb = 0 if B == 'C0' else 1 if B == 'C1' else w[B]
        w.append(1 - va if op == 'not' else (va & vb if op == 'and' else va | vb))
    return w
def subst_ok(n, sets, gates, outs, p):
    N = n + p
    dep = set([N])
    for k in range(p + 1, len(gates)):
        op, a, b = gates[k]
        if a in dep or b in dep: dep.add(n + k)
    reads = [(k, slot) for k, (op, a, b) in enumerate(gates) if k > p
             for slot, w in ((1, a), (2, b)) if w == N and not (slot == 2 and a == b)]
    rows = range(1 << n); want = [[int(any(x >> v & 1 for v in S)) for S in sets] for x in rows]
    def good(subs):
        for x in rows:
            w = evalc(n, gates, x, p, subs)
            if any(w[o] != t for o, t in zip(outs, want[x])): return False
        return True
    # constants first (cheap), then constants + earlier NOT-free wires
    for pool_kind in ('const', 'wire'):
        pools = []
        for (k, slot) in reads:
            pool = ['C1', 'C0']
            if pool_kind == 'wire': pool += [w for w in range(n + k) if w not in dep]
            pools.append(pool)
        for combo in itertools.product(*pools):
            subs = dict(zip(reads, combo))
            # a == b == N case: both slots read the NOT
            for (k, slot) in reads:
                if gates[k][1] == gates[k][2] == N: subs[(k, 2)] = subs[(k, 1)]
            if good(subs): return pool_kind, combo
    return None, None
spec = argv[0]; CAP = int(argv[1]) if len(argv) > 1 else 300; SECS = float(argv[2]) if len(argv) > 2 else 900
if spec.startswith('rand'):
    _, seed, K = spec.split(':'); rng = random.Random(int(seed)); todo = [randsys(rng) for _ in range(int(K))]
else: todo = [SYSTEMS[int(spec)]]
print('h restricted to gate wires' if HG else 'h unrestricted', flush=True)
for n, sets in todo:
    base = sum(len(S) - 1 for S in sets); t0 = time.time()
    for d in sizes:
        s = base + d; hist = collections.Counter(); fails = 0; ex = 0; cells = 0
        for p in range(s - 1):
            cells += 1; cl, SEL, O = live951.build_live(n, sets, s, p, [])
            if HG: cl += [[-SEL[p][0][i]] for i in range(n)]
            sol = Cadical153(bootstrap_with=cl); found = 0
            while found < CAP and time.time() - t0 < SECS:
                if not sol.solve(): ex += 1; break
                M = sol.get_model(); gates, outs = live951.decode(M, n, s, p, SEL, O); found += 1
                pos = set(l for l in M if l > 0)
                sol.add_clause([-SEL[k][0][gates[k][1]] for k in range(s)] + [-SEL[k][1][gates[k][2]] for k in range(s) if k != p]
                               + [(-SEL[k][2] if SEL[k][2] in pos else SEL[k][2]) for k in range(s) if k != p])
                kind, combo = subst_ok(n, sets, gates, outs, p)
                if kind is None:
                    fails += 1; hist['FAIL'] += 1
                    if fails <= 3: print(f'  SUBST-FAIL n={n} sets={sets} size={s} p={p} gates={gates} outs={outs}', flush=True)
                elif kind == 'const': hist['all1' if set(combo) == {'C1'} else 'all0' if set(combo) == {'C0'} else 'mixed-const'] += 1
                else: hist['needs-wire'] += 1
            sol.delete()
        print(f'n={n} {sets} size={s} (base+{d}) exhausted={ex}/{cells} {dict(hist)} ({time.time()-t0:.0f}s)', flush=True)
