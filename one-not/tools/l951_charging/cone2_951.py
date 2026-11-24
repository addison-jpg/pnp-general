# Request 2 (helper tooling, not a proof): search CORRECT circuits of size <= base+3 with the NOT read
# for a gate that is a cone-restricted merge for two sets (Lemma A version: each set's union-find runs only over
# gates in the cone of its output o_S). Enumerates circuits per (size, NOT position) with blocking, up to a cap.
#   python3 tools/l951_charging/cone2_951.py SYS_INDEX [cap_per_cell] [seconds]
import sys, time, collections, itertools
src = open('tools/l951_charging/ov951.py').read().split('random.seed(')[0]
exec(src)
sys.path.insert(0, 'tools/l951_charging'); import live951; build = live951.build_live  # NOT in an output cone
from pysat.solvers import Cadical153
SYSTEMS = [  # hard-set-friendly systems: several sets through shared hubs, crossing possible
    (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]),          # Pasch configuration
    (7, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 6), (5, 6)]),
    (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (2, 4)]),
    (6, [(0, 1, 2), (0, 3, 4), (1, 3), (2, 4), (5, 0)]),
    (7, [(0, 1), (0, 2), (1, 3), (2, 3), (4, 5, 6), (3, 4)]),
]
def cone(gates, n, o):
    seen = set(); st = [o]
    while st:
        w = st.pop()
        if w < n or w in seen: continue
        seen.add(w); op, a, b = gates[w - n]; st += [a, b]
    return seen
def analyse3(n, sets, gates, outs, p):
    hw = gates[p][1]; full = (1 << n) - 1
    W = lambda x: wires(n, gates, x); h = lambda x: W(x)[hw]
    mins = [x for x in range(1 << n) if h(x) and all(not h(x & ~(1 << i)) for i in range(n) if x >> i & 1)]
    per = []; kinds = []; Ts = []
    for S, o in zip(sets, outs):
        sm = sum(1 << v for v in S); Ms = [m for m in mins if not (m & sm)]
        hard = bool(Ms); kinds.append('H' if hard else 'E'); T = 0
        if hard:  # minimum hitting set of the minterms disjoint from S, avoiding S
            cand = [i for i in range(n) if not sm >> i & 1]
            for k in range(len(cand) + 1):
                hit = next((sum(1 << i for i in c) for c in itertools.combinations(cand, k) if all(m & sum(1 << i for i in c) for m in Ms)), None)
                if hit is not None: T = hit; break
        Ts.append(T); Z = full & ~(sm | T); assert not h(Z)
        wZ = W(Z); wp = {u: W(1 << u) for u in S}; C = cone(gates, n, o)
        par = {u: u for u in S}
        def f(x):
            while par[x] != x: x = par[x]
            return x
        A = lambda w: [u for u in S if wp[u][w]] if wZ[w] == 0 else None
        mg = []
        for k, (op, a, b) in enumerate(gates):
            if op != 'or' or n + k not in C or wZ[n + k] != 0: continue
            Aa, Ab = A(a), A(b)
            if Aa and Ab and f(Aa[0]) != f(Ab[0]): par[f(Aa[0])] = f(Ab[0]); mg.append(k)
        assert len(mg) >= len(S) - 1, (S, mg)
        per.append(mg)
    sms = [sum(1 << v for v in S) for S in sets]
    cross = any(sms[a] & Ts[b] and sms[b] & Ts[a] for a in range(len(sets)) for b in range(a))
    cnt = collections.Counter(k for mg in per for k in mg)
    return cross, kinds, sum(c - 1 for c in cnt.values() if c >= 2), [k for k, c in cnt.items() if c >= 2]
HGATE = '--hgate' in sys.argv; sys.argv = [a for a in sys.argv if a != '--hgate']
idx = int(sys.argv[1]); CAP = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
SECS = float(sys.argv[3]) if len(sys.argv) > 3 else 3600
print('h restricted to gate wires' if HGATE else 'h unrestricted', flush=True)
n, sets = SYSTEMS[idx]; base = sum(len(S) - 1 for S in sets); t0 = time.time()
for s in (base + 1, base + 2, base + 3):
    tot = 0; hh = 0; ncr = 0; hist = collections.Counter(); ex = 0; cells = 0
    for p in range(s - 1):
        cells += 1; cl, SEL, O = build(n, sets, s, p, [])
        if HGATE: cl += [[-SEL[p][0][i]] for i in range(n)]  # h is a gate, not an input
        sol = Cadical153(bootstrap_with=cl); found = 0
        while found < CAP and time.time() - t0 < SECS:
            if not sol.solve(): ex += 1; break
            M = sol.get_model(); gates, outs = decode(M, n, s, p, SEL, O)
            cr, kinds, dbl, where = analyse3(n, sets, gates, outs, p)
            found += 1; hist[dbl] += 1; hh += kinds.count('H') >= 2; ncr += cr
            if dbl and hist[dbl] <= 3:
                print(f'  DOUBLE size={s} p={p} kinds={kinds} gates={gates} outs={outs} double_at={where}', flush=True)
            pos = set(l for l in M if l > 0)
            sol.add_clause([-SEL[k][0][gates[k][1]] for k in range(s)] + [-SEL[k][1][gates[k][2]] for k in range(s) if k != p]
                           + [(-SEL[k][2] if SEL[k][2] in pos else SEL[k][2]) for k in range(s) if k != p])
        sol.delete(); tot += found
    print(f'{sets} size={s} (base+{s-base}): circuits={tot} exhausted_cells={ex}/{cells} >=2hard={hh} with_crossing_pair={ncr} '
          f'cone_double_histogram={dict(hist)} ({time.time()-t0:.0f}s)', flush=True)
