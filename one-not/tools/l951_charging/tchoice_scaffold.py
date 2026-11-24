# Front's request (helper tooling, not a proof): does a double-free choice of zero sets always exist?
# Live-NOT circuits, NOT reads a gate h (so h(0)=0), no gate constant as a function. C1 = NOT := 1.
# Easy S (h(z_S)=0, z_T = 0 on T, 1 elsewhere): T_S = S. Hard S: T_S = S ∪ R_S, R_S a MINIMUM set (R ∩ S = ∅) with
# h(z_{S∪R}) = 0; every minimum R_S is tried. Per set: cone-restricted union-find in C1 at zero point z_T, test points
# e_u (u in S); an OR gate g with g(z_T)=0 whose inputs have nonempty S-sets in different classes is a charge.
# A choice (one R_S per hard set) is double-free if no gate is charged by two sets.
# Reports per size: #circuits, #open (>=2 hard sets and h(1_X)=1, X = union of hard sets), #all-choices-double,
# and prints every circuit where no double-free choice exists.
#   python3 tools/l951_charging/tchoice_scaffold.py SYS|rand:SEED:K [cap_per_cell] [seconds] [--sizes 2,3,4]
import sys, time, random, itertools, collections
sys.path.insert(0, 'tools/l951_charging'); import live951, clean951_scaffold as clean951
from pysat.solvers import Cadical153
CLEAN = '--clean' in sys.argv; ESS = '--essential' in sys.argv; sys.argv = [a for a in sys.argv if a != '--essential']; argv = [a for a in sys.argv[1:] if a != '--clean']; sizes = (2, 3, 4)
if '--sizes' in argv:
    i = argv.index('--sizes'); sizes = tuple(int(v) for v in argv[i + 1].split(',')); del argv[i:i + 2]
SYS = {'gadget': (5, [(0, 1), (0, 2), (3, 4)]), 'c5': (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]), 'pasch': (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]),
       'p2': (6, [(0, 1, 2), (0, 3, 4), (1, 3), (2, 4), (5, 0)]),
       'k4e': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)])}
def randsys(rng):
    while True:
        n = rng.randint(6, 7); m = rng.randint(3, 5); sets = []
        for _ in range(500):
            S = tuple(sorted(rng.sample(range(n), rng.choice((2, 2, 3, 3)))))
            if S not in sets and all(len(set(S) & set(T)) <= 1 for T in sets): sets.append(S)
            if len(sets) == m: break
        if len(sets) == m and set().union(*map(set, sets)) == set(range(n)): return n, sets
spec = argv[0]; CAP = int(argv[1]) if len(argv) > 1 else 400; SECS = float(argv[2]) if len(argv) > 2 else 900
if spec.startswith('rand'):
    _, seed, K = spec.split(':'); rng = random.Random(int(seed)); todo = [randsys(rng) for _ in range(int(K))]
else: todo = [SYS[spec]]
def run(n, sets):
    full = (1 << n) - 1; base = sum(len(S) - 1 for S in sets); t0 = time.time()
    def wires(gates, x, p, c1):
        w = [(x >> i) & 1 for i in range(n)]
        for k, (op, a, b) in enumerate(gates):
            if op == 'not': w.append(1 if c1 else 1 - w[a])
            else: w.append(w[a] & w[b] if op == 'and' else w[a] | w[b])
        return w
    def cone(gates, o):
        C = set(); st = [o]
        while st:
            w = st.pop()
            if w < n or w in C: continue
            C.add(w); st += [gates[w - n][1], gates[w - n][2]]
        return C
    def charges(gates, p, S, o, T):
        z = full & ~sum(1 << v for v in T); wz = wires(gates, z, p, True); wp = {u: wires(gates, 1 << u, p, True) for u in S}
        assert wz[o] == 0; C = cone(gates, o); par = {u: u for u in S}
        def f(x):
            while par[x] != x: x = par[x]
            return x
        A = lambda w: [u for u in S if wp[u][w]] if wz[w] == 0 else None
        out = set()
        for k, (op, a, b) in enumerate(gates):
            if op != 'or' or n + k not in C or wz[n + k] != 0: continue
            Aa, Ab = A(a), A(b)
            if Aa and Ab and f(Aa[0]) != f(Ab[0]): par[f(Aa[0])] = f(Ab[0]); out.add(k)
        assert len(out) >= len(S) - 1, (S, T, gates)
        return frozenset(out)
    for d in sizes:
        rules = collections.Counter(); anyfail = 0; s = base + d; tot = opened = alldbl = skipped_const = 0; ex = 0
        for p in range(1, s - 1):
            cl, SEL, O = (clean951.build_clean if CLEAN else live951.build_live)(n, sets, s, p, [])
            cl += [[-SEL[p][0][i]] for i in range(n)]
            sol = Cadical153(bootstrap_with=cl); found = 0
            while found < CAP and time.time() - t0 < SECS:
                if not sol.solve(): ex += 1; break
                M = sol.get_model(); gates, outs = live951.decode(M, n, s, p, SEL, O); found += 1
                pos = set(l for l in M if l > 0)
                sol.add_clause([-SEL[k][0][gates[k][1]] for k in range(s)] + [-SEL[k][1][gates[k][2]] for k in range(s) if k != p]
                               + [(-SEL[k][2] if SEL[k][2] in pos else SEL[k][2]) for k in range(s) if k != p])
                vals = [wires(gates, x, p, False) for x in range(1 << n)]
                if any(len({v[n + k] for v in vals}) == 1 for k in range(s)): skipped_const += 1; continue
                if ESS:
                    def wrong(c):
                        for x in range(1 << n):
                            w = [(x >> i) & 1 for i in range(n)]
                            for op, a, b in gates: w.append(c if op == 'not' else (w[a] & w[b] if op == 'and' else w[a] | w[b]))
                            if any(w[o] != int(any(x >> v & 1 for v in S)) for S, o in zip(sets, outs)): return True
                        return False
                    if not (wrong(0) and wrong(1)): skipped_const += 1; continue
                tot += 1; hw = gates[p][1]; h = lambda x: vals[x][hw]
                choices = []; hard = []
                for i, S in enumerate(sets):
                    sm = sum(1 << v for v in S)
                    if not h(full & ~sm): choices.append([frozenset(S)]); continue
                    hard.append(i); rest = [v for v in range(n) if v not in S]; opts = []
                    for r in range(1, len(rest) + 1):
                        opts = [frozenset(S) | frozenset(R) for R in itertools.combinations(rest, r)
                                if not h(full & ~(sm | sum(1 << v for v in R)))]
                        if opts: break
                    choices.append(opts)
                X = 0
                for i in hard:
                    for v in sets[i]: X |= 1 << v
                if len(hard) >= 2 and h(X): opened += 1
                ch = [[charges(gates, p, sets[i], outs[i], T) for T in choices[i]] for i in range(len(sets))]
                # canonical rules (one choice per set): lex = first minimum R in itertools order;
                # avoid = minimum R with fewest elements in other hard sets (ties: lex); glob = R_S = (T* minus S) for one
                # global minimum hitting set T* of all minterms of h (not minimum per S; used only if h(z) = 0 holds)
                def dfree(sel):
                    seen = set()
                    for cs in sel:
                        if seen & cs: return False
                        seen |= cs
                    return True
                otherhard = lambda i: set().union(*[set(sets[j]) for j in hard if j != i]) if len(hard) > 1 else set()
                lexsel = [c[0] for c in ch]
                avsel = [ch[i][min(range(len(choices[i])), key=lambda j: (len(choices[i][j] & otherhard(i)), j))] for i in range(len(sets))]
                mins = [x for x in range(1 << n) if h(x) and all(not h(x & ~(1 << v)) for v in range(n) if x >> v & 1)]
                Tg = None
                for r in range(n + 1):
                    for c in itertools.combinations(range(n), r):
                        cm = sum(1 << v for v in c)
                        if all(m & cm for m in mins): Tg = set(c); break
                    if Tg is not None: break
                glsel = [charges(gates, p, sets[i], outs[i], set(sets[i]) | (Tg if i in hard else set())) for i in range(len(sets))]
                rules['lex'] += not dfree(lexsel); rules['avoid'] += not dfree(avsel); rules['global'] += not dfree(glsel)
                # does SOME choice have a double charge? (pairwise: two sets with intersecting charge sets for some options)
                somedbl = [(i, j) for i in range(len(sets)) for j in range(i) if any(a & b for a in ch[i] for b in ch[j])]
                if somedbl:
                    anyfail += 1
                    if anyfail <= 3:
                        print(f'  SOME-CHOICE-DOUBLE n={n} sets={sets} size={s} p={p} hard={hard} pairs={somedbl} gates={gates} outs={outs} '
                              f'Rchoices={[sorted(map(sorted, c)) for c in choices]} charges={[[sorted(x) for x in c] for c in ch]}', flush=True)
                ok = False
                for combo in itertools.islice(itertools.product(*ch), 5000):
                    seen = set(); bad = False
                    for cs in combo:
                        if seen & cs: bad = True; break
                        seen |= cs
                    if not bad: ok = True; break
                if not ok:
                    alldbl += 1
                    if alldbl <= 3:
                        print(f'  NO-DOUBLE-FREE-CHOICE n={n} sets={sets} size={s} p={p} hard={hard} open={len(hard) >= 2 and bool(h(X))} '
                              f'gates={gates} outs={outs} Rchoices={[sorted(map(sorted, c)) for c in choices]}', flush=True)
            sol.delete()
        print(f'n={n} {sets} size={s} (base+{d}) circuits={tot} (skipped: constant gate{' or NOT inessential' if ESS else ''} {skipped_const}) open_case={opened} '
              f'no_double_free_choice={alldbl} some_choice_double={anyfail} rule_failures={dict(rules)} exhausted={ex}/{s-2} ({time.time()-t0:.0f}s)', flush=True)
print('tchoice', spec, flush=True)
for n, sets in todo: run(n, sets)
