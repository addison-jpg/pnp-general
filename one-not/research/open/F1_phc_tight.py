"""Seat F1: the payment Hall condition in DELETION FORM (F1_phc.md, Lemma D) and its tight families.  Repo root:
  nice python3 -I one-not/research/open/F1_phc_tight.py dd [--maxn 9] [--states -1] [--gen K]     BottomPay instances (A14 setup)
  nice python3 -I one-not/research/open/F1_phc_tight.py prog p q s|d K cap [--union]             point programs, PHC@0 (U1 setup)
  nice python3 -I one-not/research/open/F1_phc_tight.py lemmaD                                   Lemma D on random instances
An instance: payers E, sets w with classes, one hyperedge V_w(g) (set of classes) per payer and set.
  c_w(J)   = number of components of the hypergraph {V_w(g) : g in J} on the classes of w
  slack(J) = |E - J| - sum_w (c_w(J) - 1)                          Lemma D:  PHC  <=>  slack(J) >= 0 for every J
  PEELING  = for every J != E some g outside J has sum_w (c_w(J) - c_w(J + g)) <= 1 (implies slack >= 0 by induction;
             strictly stronger than PHC).  peel_fail counts the J where it fails, by slack(J).
  union    = max size of a disjoint union of independent sets (A14 `partition`, Edmonds)
Checked on every instance: min_J slack(J) = union - sum_w need_w  (the matroid union formula with r_w replaced by
classes - c_w; brute force over J, only payers useful for some set matter).  A deletion set R = E - J is TIGHT when
slack = 0.  Printed: histogram of min slack, the inclusion-minimal nonempty tight R (size, sets split, gates
shared), and whether a tight R is 'single-set' (splits one set only).
"""
import sys, collections, itertools, random
sys.path.insert(0, 'one-not/research/open')

def comps(classes, edges):
    lab = {c: c for c in classes}
    def fd(c):
        while lab[c] != c: lab[c] = lab[lab[c]]; c = lab[c]
        return c
    k = len(classes)
    for e in edges:
        e = list(e); r = fd(e[0])
        for x in e[1:]:
            s = fd(x)
            if s != r: lab[s] = r; k -= 1
    return k

CAP = 14

def study(E, cls, hyp, out, tag, EX, info=None):
    """E: payers; cls[w]: list of classes; hyp[w][g]: frozenset of classes."""
    K = len(cls)
    useful = [g for g in E if any(len(hyp[w][g]) >= 2 for w in range(K))]
    need = [len(cls[w]) - 1 for w in range(K)]
    if len(useful) > CAP: out[tag + 'skipped_big'] += 1; return
    m = len(useful); best = None; tight = []; cc = {}
    for mask in range(1 << m):          # mask = R, the deleted payers
        J = [useful[i] for i in range(m) if not mask >> i & 1]
        c = [comps(cls[w], [hyp[w][g] for g in J if len(hyp[w][g]) >= 2]) for w in range(K)]
        s = bin(mask).count('1') - sum(x - 1 for x in c)
        if best is None or s < best: best = s
        cc[mask] = (sum(c), s)
        if s == 0 and mask: tight.append((mask, tuple(c)))
    out[tag + 'min_slack_%d' % best] += 1
    # PEELING: from every J != E some payer g outside J can be put back with sum_w c_w dropping by at most 1
    pf = 0; ef = lf = 0
    for mask in range(1, 1 << m):
        d = [cc[mask][0] - cc[mask ^ (1 << i)][0] for i in range(m) if mask >> i & 1]
        if min(d) > 1:
            pf += 1; out[tag + 'peel_fail_J_with_slack_%d' % min(cc[mask][1], 5)] += 1
            if len(EX) < 300 and cc[mask][1] <= 1: EX.append((-1, 'PEEL FAIL', info, [useful[i] for i in range(m) if mask >> i & 1], cc[mask]))
        ef += d[0] > 1; lf += d[-1] > 1
    out[tag + 'peel_fail_instances'] += bool(pf); out[tag + 'earliest_rule_fail_instances'] += bool(ef); out[tag + 'latest_rule_fail_instances'] += bool(lf)
    if comps_all := [comps(cls[w], [hyp[w][g] for g in useful if len(hyp[w][g]) >= 2]) for w in range(K)]:
        if any(x != 1 for x in comps_all): out[tag + 'per_set_rank_short'] += 1
    # compare with Edmonds
    import A14_bottom_hall as A14
    assign, I, reach = A14.partition(useful, hyp, K)
    un = sum(len(I[w]) for w in range(K))
    if un - sum(need) != min(best, 0) and not (best >= 0 and un == sum(need)): out[tag + 'LEMMA_D_MISMATCH'] += 1
    if best < 0 and un - sum(need) != best: out[tag + 'LEMMA_D_MISMATCH'] += 1
    out[tag + 'instances'] += 1
    # blocks of the lattice of tight deletion sets (closed under union and intersection): for a join-irreducible
    # tight R (one maximal tight proper subset R'), the block is R - R'; it is ENTANGLED when it splits >= 2 sets.
    tm = dict(tight); tm[0] = tuple(1 for _ in range(K))
    if len(tm) <= 4096:
        for R, c in tight:
            lower = [o for o in tm if o != R and o & R == o]
            mx = [o for o in lower if not any(o2 != o and o & o2 == o for o2 in lower)]
            if len(mx) != 1: continue
            d = [c[w] - tm[mx[0]][w] for w in range(K)]; nb = bin(R ^ mx[0]).count('1')
            ent = sum(1 for x in d if x > 0)
            out[tag + 'block_splits_%d_sets' % ent] += 1
            if ent >= 2:
                out[tag + 'entangled_block_size_%d' % nb] += 1
                B = [useful[i] for i in range(m) if (R ^ mx[0]) >> i & 1]
                allsh = all(sum(len(hyp[w][g]) >= 2 for w in range(K)) >= 2 for g in B)
                out[tag + 'entangled_block_all_gates_shared_%s' % allsh] += 1
                if len(EX) < 300: EX.append((nb, info, B, d, [[sorted(map(str, hyp[w][g])) for g in B] for w in range(K)]))
    masks = [t[0] for t in tight]
    mins = [t for t in tight if not any(o != t[0] and o & t[0] == o for o in masks)]
    out[tag + 'has_tight'] += bool(tight)
    for mask, c in mins:
        split = sum(1 for x in c if x > 1)
        out[tag + 'mintight_split_%d_sets' % split] += 1
        R = [useful[i] for i in range(m) if mask >> i & 1]
        sh = sum(1 for g in R if sum(len(hyp[w][g]) >= 2 for w in range(K)) >= 2)
        out[tag + 'mintight_shared_gates_%s' % ('0' if sh == 0 else '>0')] += 1

def dd(A):
    import A7_dd_absorb_attack as A7, A10_light_attack as A10
    maxn = int(A[A.index('--maxn') + 1]) if '--maxn' in A else 9
    k = int(A[A.index('--states') + 1]) if '--states' in A else -1
    rng = random.Random(1)
    cs = [] if '--nostored' in A else A7.collect(maxn)
    if '--gen' in A: cs += [A7.gen_switch(rng) for _ in range(int(A[A.index('--gen') + 1]))]
    out = collections.Counter(); EX = []
    for c in cs:
        W, X, FULL = A7.tables(c['n'], c['gates'])
        if not A7.correct(c, W, X): continue
        n, G, S = c['n'], c['gates'], c['sets']
        p = [i for i, g in enumerate(G) if g[0] == 'not'][0]; a = W[G[p][1]]; ALL = (1 << n) - 1
        for Q, D in A7.states(n, rng, k):
            qpt = sum(1 << v for v in Q); top = set(); dds = []
            for w, R in enumerate(S):
                if set(R) & Q: continue
                R2 = [u for u in R if u not in D]
                if len(R2) < 2: continue
                zw = ALL
                for u in R2 + list(D): zw &= ~(1 << u)
                P = {u: qpt | 1 << u for u in R2}
                if not (a >> zw & 1 and any(not (a >> P[u] & 1) for u in R2)):
                    top |= set(A10.uf_run(G, W, n, zw, P)); continue
                U = [u for u in R2 if a >> P[u] & 1]
                if len(U) >= 2: top |= set(A10.uf_run(G, W, n, zw, {u: P[u] for u in U}))
                dds.append((w, R2, P, {u: ('H' if u in U else u) for u in R2}))
            if not dds: continue
            out['dd_states'] += 1
            ORs = [i for i in range(len(G)) if G[i][0] == 'or' and not W[n + i] >> qpt & 1]
            E = [i for i in ORs if i not in top]
            cls = [sorted(set(d[3].values()), key=str) for d in dds]
            hyp = [{i: frozenset(d[3][u] for u in d[1] if W[n + i] >> d[2][u] & 1) for i in ORs} for d in dds]
            # the gap in the per-set rank: is some gate that the bottom hypergraph of w needs in top?
            if any(comps(cls[w], [hyp[w][g] for g in E if len(hyp[w][g]) >= 2]) != 1 for w in range(len(dds))): out['rank_short_without_top'] += 1
            if any(len(hyp[w][g]) >= 2 for w in range(len(dds)) for g in ORs if g in top): out['states_with_useful_gate_in_top'] += 1
            if len(dds) < 2: out['one_dd_set'] += 1; continue
            study(E, cls, hyp, out, '', EX, (c.get('name', '')[-40:], sorted(Q), sorted(D)))
    return out, EX

def prog(A):
    from B9_two_sets import build
    from pysat.solvers import Solver
    union = '--union' in A; A = [x for x in A if x != '--union']
    p, q, sh, K, cap = int(A[0]), int(A[1]), A[2] == 's', int(A[3]), int(A[4])
    if sh: Wt = [list(range(p)), [0] + list(range(p, p + q - 1))]; n = p + q - 1
    else: Wt = [list(range(p)), list(range(p, p + q))]; n = p + q
    cl, X, meta, new = build(n, Wt, K); out = collections.Counter(); EX = []; cnt = 0
    with Solver(name='g3', bootstrap_with=cl) as s:
        while cnt < cap and s.solve():
            m = set(v for v in s.get_model() if v > 0); cnt += 1
            vals = [frozenset(u for u in range(n) if X[i][u] in m) for i in range(K)]
            ops = [[k for k in range(4) if meta[i][2][k] in m][0] for i in range(K)]
            E = [i for i in range(K) if not union or ops[i] == 0]
            hyp = [{i: vals[i] & frozenset(R) for i in E} for R in Wt]
            study(E, [list(R) for R in Wt], hyp, out, '', EX, ([sorted(v) for v in vals], ops))
            s.add_clause([-X[i][u] if X[i][u] in m else X[i][u] for i in range(K) for u in range(n)])
    return out, EX

def lemma_d_random(trials=3000, seed=7):
    """Lemma D on random instances (PHC true or false): Edmonds' union size (A14 `partition`) against
    min_J (|E - J| + sum_w (classes_w - c_w(J)))."""
    import A14_bottom_hall as A14
    rng = random.Random(seed); bad = short = 0
    for _ in range(trials):
        K = rng.randint(1, 3); m = rng.randint(2, 7)
        cls = [list(range(rng.randint(2, 5))) for _ in range(K)]
        hyp = [{g: frozenset(x for x in cls[w] if rng.random() < rng.choice([.2, .4, .6])) for g in range(m)} for w in range(K)]
        E = list(range(m)); useful = [g for g in E if any(len(hyp[w][g]) >= 2 for w in range(K))]
        assign, I, reach = A14.partition(useful, hyp, K); un = sum(len(I[w]) for w in range(K))
        best = min(bin(mask).count('1') + sum(len(cls[w]) - comps(cls[w], [hyp[w][g] for i, g in enumerate(useful) if not mask >> i & 1 and len(hyp[w][g]) >= 2]) for w in range(K))
                   for mask in range(1 << len(useful)))
        bad += un != best; short += un < sum(len(c) - 1 for c in cls)
    print('random instances', trials, 'PHC false in', short, 'Lemma D mismatches', bad)

if __name__ == '__main__':
    if sys.argv[1] == 'lemmaD': lemma_d_random(); sys.exit()
    out, EX = dd(sys.argv[2:]) if sys.argv[1] == 'dd' else prog(sys.argv[2:])
    for key in sorted(out): print(key, out[key])
    for e in sorted(EX, key=lambda e: e[0])[:4]: print(e)
