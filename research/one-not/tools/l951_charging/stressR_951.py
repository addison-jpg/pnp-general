# Stress test for LEMMA R (agents/MATH_FINDINGS.md, commit 819072e) — helper tooling, not a proof.
# For a correct circuit with the NOT (gate p, reading h) read later, and a minterm M of h:
#   set x_v=1 for v in M, NOT -> const 0, constant-propagate, keep only outputs of sets with S ∩ M = ∅ (unhit).
#   live = gates still reachable; removed = size - live.  R: removed >= Σ_{hit}(|S|-1) + 2.
# Circuits whose NOT lies in no output cone are skipped (counted as deadNOT_skipped).
# Reports, per (system, size), min over circuits of  min_M slack  and  max_M slack  (slack = removed - Σhit - 2;
# R for every M needs min_M slack >= 0, the 951 consequence only needs max_M slack >= 0), and prints violators.
# live uses agents/restr951.py's restrict_count (const-prop + dead code, no structural hashing), so a violation
# is only a candidate: overcounted live gates (duplicates) can fake one, so violators are printed for a hand check.
#   python3 research/tools/l951_charging/stressR_951.py SYSIDX|rand:SEED:K [cap_per_cell] [seconds]
import sys, time, random, collections
args = sys.argv[1:]; sys.argv = ['x']
src = open('research/tools/l951_charging/agents/restr951.py').read().split('\nt0=time.time()')[0]
exec(src)  # build, decode, wires, restrict_count
sys.path.insert(0, 'research/tools/l951_charging'); import live951; build = live951.build_live  # NOT in an output cone
from pysat.solvers import Cadical153
SYSTEMS = [(5, [(0, 1, 2), (0, 3, 4)]), (5, [(0, 1, 2), (2, 3), (3, 4, 0)]), (6, [(0, 1), (2, 3), (4, 5), (0, 2, 4)]),
           (6, [(0, 1, 2), (3, 4, 5), (0, 3)]), (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]),
           (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]), (7, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 6), (5, 6)]),
           (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (2, 4)]), (6, [(0, 1, 2), (0, 3, 4), (1, 3), (2, 4), (5, 0)]),
           (7, [(0, 1), (0, 2), (1, 3), (2, 3), (4, 5, 6), (3, 4)]), (7, [(0, 1, 2, 3), (0, 4), (1, 5), (2, 6), (4, 5, 6)])]
def randsys(rng):
    while True:
        n = rng.randint(6, 7); m = rng.randint(3, 5); sets = []
        for _ in range(500):
            S = tuple(sorted(rng.sample(range(n), rng.choice((2, 3, 3, 4)))))
            if S not in sets and all(len(set(S) & set(T)) <= 1 for T in sets): sets.append(S)
            if len(sets) == m: break
        if len(sets) == m and set().union(*map(set, sets)) == set(range(n)): return n, sets
def r2(n, sets, gates, outs, p, m):
    # R2 (repair of R): with x_M=1 fixed, run for each UNHIT set S (S ∩ M = ∅) the union-find over the cone of o_S:
    # zero point Z = all ones except S; S-set of wire w = {u in S : w(1_M + e_u) = 1}, tracked only if w(Z) = 0;
    # a merge is an OR gate in the cone, tracked, whose two inputs have nonempty S-sets in different classes.
    # Returns (unhit_excess, slack2): unhit_excess = Σ_unhit #merges - #distinct merge gates (double merges),
    # slack2 = #gates that are a merge for no unhit set - Σ_hit(|S|-1).   R2: slack2 >= 0.
    # R2 with unhit_excess = 0 and >= |S|-1 merges per unhit set (asserted) gives size >= Σ_all(|S|-1).
    full = (1 << n) - 1; U = set(); tot = 0; hit = 0
    for S, o in zip(sets, outs):
        sm = sum(1 << v for v in S)
        if sm & m: hit += len(S) - 1; continue
        wZ = wires(n, gates, full & ~sm); wp = {u: wires(n, gates, m | 1 << u) for u in S}
        C = set(); st = [o]
        while st:
            w = st.pop()
            if w < n or w in C: continue
            C.add(w); st += [gates[w - n][1], gates[w - n][2]]
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
        assert len(mg) >= len(S) - 1, (S, mg, gates)
        tot += len(mg); U |= set(mg)
    return tot - len(U), (len(gates) - len(U)) - hit
spec = args[0]; CAP = int(args[1]) if len(args) > 1 else 200; SECS = float(args[2]) if len(args) > 2 else 1800
if spec.startswith('rand'):
    _, seed, K = spec.split(':'); rng = random.Random(int(seed)); todo = [randsys(rng) for _ in range(int(K))]
else: todo = [SYSTEMS[int(spec)]]
for n, sets in todo:
    base = sum(len(S) - 1 for S in sets); t0 = time.time()
    for s in (base + 1, base + 2, base + 3):
        nc = 0; mins = []; maxs = []; r2min = []; r2ex = 0; v2 = 0; ex = 0; cells = 0; viol = 0; dead = 0
        for p in range(s - 1):
            cells += 1; cl, SEL, O = build(n, sets, s, p, []); sol = Cadical153(bootstrap_with=cl); found = 0
            while found < CAP and time.time() - t0 < SECS:
                if not sol.solve(): ex += 1; break
                M_ = sol.get_model(); gates, outs = decode(M_, n, s, p, SEL, O); found += 1
                pos = set(l for l in M_ if l > 0)
                sol.add_clause([-SEL[k][0][gates[k][1]] for k in range(s)] + [-SEL[k][1][gates[k][2]] for k in range(s) if k != p]
                               + [(-SEL[k][2] if SEL[k][2] in pos else SEL[k][2]) for k in range(s) if k != p])
                cone = set(); st = list(outs)
                while st:
                    w = st.pop()
                    if w < n or w in cone: continue
                    cone.add(w); st += [gates[w - n][1], gates[w - n][2]]
                if n + p not in cone: dead += 1; continue  # NOT outside every output cone: monotone circuit + junk
                hw = gates[p][1]; h = lambda x: wires(n, gates, x)[hw]
                mt = [x for x in range(1 << n) if h(x) and all(not h(x & ~(1 << i)) for i in range(n) if x >> i & 1)]
                sl = []; q = [r2(n, sets, gates, outs, p, m) for m in mt]
                r2min.append(min(b for a, b in q)); r2ex += any(a for a, b in q)
                if min(b for a, b in q) < 0 or any(a for a, b in q):
                    v2 += 1
                    if v2 <= 3: print(f'  R2-VIOL size={s} p={p} (unhit_excess, slack2) per M={q} minterms={mt} gates={gates} outs={outs}', flush=True)
                for m in mt:
                    Ms = [v for v in range(n) if m >> v & 1]
                    keep = [i for i, S in enumerate(sets) if not set(S) & set(Ms)]
                    lv = restrict_count(n, gates, outs, p, Ms, keep)
                    sl.append((s - lv) - sum(len(S) - 1 for i, S in enumerate(sets) if i not in keep) - 2)
                mins.append(min(sl)); maxs.append(max(sl))
                if min(sl) < 0:
                    viol += 1
                    if viol <= 3: print(f'  R-VIOL size={s} p={p} slacks={sl} minterms={mt} gates={gates} outs={outs}', flush=True)
            sol.delete(); nc += found
        h1 = dict(collections.Counter(mins)); h2 = dict(collections.Counter(maxs))
        print(f'n={n} {sets} size={s} (base+{s-base}) circuits={nc} deadNOT_skipped={dead} exhausted={ex}/{cells} '
              f'minM_slack_hist={h1} maxM_slack_hist={h2} R_violations(forall M)={viol} | R2: minM_slack2_hist={dict(collections.Counter(r2min))} circuits_with_unhit_double_merge={r2ex} R2_violations={v2} ({time.time()-t0:.0f}s)', flush=True)
