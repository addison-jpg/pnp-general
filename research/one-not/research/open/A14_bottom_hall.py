"""Seat A14: BOTTOM PAY (board open-one-not, A10 section 3) in Hall / matroid-union form.  From the repo root:
   python3 -I research/one-not/research/open/A14_bottom_hall.py [--maxn 9] [--states -1] [--gen K] [--seed 1] [--nostored] [--ex 6]
At every DD state (Q, D) (A7/A10 notation): E = OR gates not in top, 0 at 1_Q.  For a DD set w the w-classes are the heavy
atoms U_w (one class) and the light atoms T_w (singletons); gate g has the hyperedge V_w(g) = classes holding an atom P_u
with g(P_u) = 1; g is USEFUL for w when |V_w(g)| >= 2.  M_w = hypergraphic matroid on E (I independent iff every nonempty
J in I spans >= |J| + 1 classes; Lorea / Frank-Kiraly-Kriesell), r_w(E) = need_w (A10 item 1).
Computed per state:
  naive   = min over nonempty subfamilies F of DD sets of |N(F)| - sum_{F} need_w   (N(F) = gates useful for some w in F)
  naive2  = the same over |F| >= 2
  union   = matroid partition (Edmonds, shortest augmenting paths): max |I_1 u ... u I_k|, I_w independent in M_w, disjoint;
            BOTTOM PAY <=> union = sum need_w.  fail = states where union < sum need.
  rigid   = B* = E_useful minus the gates reachable from a free gate in the exchange graph (the largest B with
            |B| = sum_w (r_w(E) - r_w(E - B)), i.e. the largest tight deletion set).
  structure of shared gates (useful for two DD sets a, b): where their 1-atoms lie (the point S_a cap S_b, heavy atoms,
            light atoms), and whether each shared gate is 1 at the common point of S_a and S_b.
"""
import sys, collections, random, itertools
sys.path.insert(0, 'research/one-not/research/open')
import A7_dd_absorb_attack as A7
import A10_light_attack as A10


def indep(edges):
    """edges: list of frozensets (classes).  Hypergraphic independence: every nonempty subfamily J spans >= |J| + 1."""
    k = len(edges)
    for mask in range(1, 1 << k):
        span = set(); c = 0
        for i in range(k):
            if mask >> i & 1: span |= edges[i]; c += 1
        if len(span) < c + 1: return False
    return True


def rank(edges):
    I = []
    for e in edges:
        if len(e) >= 2 and indep(I + [e]): I.append(e)
    return len(I)


def partition(gates, hyp, K):
    """gates: list of gate ids; hyp[w][g] = frozenset of w-classes.  Returns (assign dict g -> w, reach set)."""
    assign = {}
    I = {w: [] for w in range(K)}
    def edges(w, gs): return [hyp[w][g] for g in gs]
    for x in gates:
        # BFS from x over the exchange graph
        prev = {x: None}; queue = [x]; found = None
        while queue and found is None:
            nq = []
            for y in queue:
                for w in range(K):
                    if len(hyp[w][y]) < 2 or assign.get(y) == w: continue
                    cur = [g for g in I[w]]
                    if indep(edges(w, cur + [y])):
                        found = (y, w); break
                    for z in cur:
                        if z in prev: continue
                        rest = [g for g in cur if g != z] + [y]
                        if indep(edges(w, rest)):
                            prev[z] = (y, w); nq.append(z)
                if found: break
            queue = nq
        if found is None: continue
        y, w = found
        # augment: y goes into w; walk back
        while True:
            old = assign.get(y)
            if old is not None: I[old].remove(y)
            assign[y] = w; I[w].append(y)
            if prev[y] is None: break
            y, w = prev[y][0], prev[y][1]
            # prev[z] = (y', w'): z was displaced from w' by y'; z itself is now re-placed (handled in previous step)
        for w2 in range(K): assert indep(edges(w2, I[w2])), 'augment broke independence'
    # reach from free gates
    free = [g for g in gates if g not in assign]
    reach = set(free); queue = list(free)
    while queue:
        y = queue.pop()
        for w in range(K):
            if len(hyp[w][y]) < 2 or assign.get(y) == w: continue
            for z in I[w]:
                if z in reach: continue
                rest = [g for g in I[w] if g != z] + [y]
                if indep(edges(w, rest)): reach.add(z); queue.append(z)
    return assign, I, reach


def analyse(c, W, X, FULL, Q, D, out, EX):
    n, G, S = c['n'], c['gates'], c['sets']
    p = [k for k, g in enumerate(G) if g[0] == 'not'][0]; a = W[G[p][1]]
    qpt = sum(1 << v for v in Q); ALL = (1 << n) - 1
    alive = []
    for w, R in enumerate(S):
        if set(R) & Q: continue
        R2 = [u for u in R if u not in D]
        if len(R2) < 2: continue
        zw = ALL
        for u in R2 + list(D): zw &= ~(1 << u)
        P = {u: qpt | 1 << u for u in R2}
        dd = bool(a >> zw & 1) and any(not (a >> P[u] & 1) for u in R2)
        alive.append((w, R2, zw, P, dd))
    if not any(x[4] for x in alive): return
    out['dd_states'] += 1
    top = set(); dds = []
    for (w, R2, zw, P, dd) in alive:
        if not dd:
            top |= set(A10.uf_run(G, W, n, zw, P)); continue
        U = [u for u in R2 if a >> P[u] & 1]; T = [u for u in R2 if not a >> P[u] & 1]
        if len(U) >= 2: top |= set(A10.uf_run(G, W, n, zw, {u: P[u] for u in U}))
        cl = {u: ('H' if u in U else u) for u in R2}
        dds.append((w, R2, P, U, T, cl, len(T) - (0 if U else 1)))
    E = [k for k in range(len(G)) if G[k][0] == 'or' and k not in top and not W[n + k] >> qpt & 1]
    K = len(dds)
    hyp = [{k: frozenset(cl[u] for u in R2 if W[n + k] >> P[u] & 1) for k in E} for (w, R2, P, U, T, cl, nd) in dds]
    need = [d[6] for d in dds]
    useful = [k for k in E if any(len(hyp[i][k]) >= 2 for i in range(K))]
    users = {k: [i for i in range(K) if len(hyp[i][k]) >= 2] for k in useful}
    shared = [k for k in useful if len(users[k]) >= 2]
    if not shared:
        out['no_shared'] += 1; return
    out['shared_states'] += 1
    out['ndd_hist_%d' % K] += 1
    # naive Hall
    best = None; best2 = None
    for r in range(1, K + 1):
        for F in itertools.combinations(range(K), r):
            NF = sum(1 for k in useful if any(i in F for i in users[k]))
            s = NF - sum(need[i] for i in F)
            if best is None or s < best[0]: best = (s, F)
            if r >= 2 and (best2 is None or s < best2[0]): best2 = (s, F)
    out['naive_min_%d' % best[0]] += 1
    if best2: out['naive2_min_%d' % min(best2[0], 9)] += 1
    if best[0] < 0: out['naive_fail'] += 1
    # private rank: do the private gates alone pay every set?
    priv_ok = all(rank([hyp[i][k] for k in useful if users[k] == [i]]) >= need[i] for i in range(K))
    out['private_pays'] += priv_ok
    # matroid union
    assign, I, reach = partition(useful, hyp, K)
    tot = sum(len(I[i]) for i in range(K))
    for i in range(K): assert len(I[i]) <= need[i]
    fail = tot < sum(need)
    out['union_fail'] += fail
    rigid = [k for k in useful if k not in reach]
    out['rigid_eq_all'] += len(rigid) == len(useful)
    sh_rigid = [k for k in shared if k not in reach]
    out['shared_rigid_states'] += bool(sh_rigid)
    # structure of shared gates
    for k in shared:
        us = users[k]
        for i, j in itertools.combinations(us, 2):
            Si, Sj = set(dds[i][1]), set(dds[j][1])
            com = Si & Sj
            on = lambda u, d: W[n + k] >> d[2][u] & 1
            onI = {u for u in dds[i][1] if on(u, dds[i])}; onJ = {u for u in dds[j][1] if on(u, dds[j])}
            out['pair_total'] += 1
            out['pair_has_common_point'] += bool(com)
            out['pair_gate_on_common'] += bool(com & onI)
            hi = onI & set(dds[i][3]); hj = onJ & set(dds[j][3])
            out['pair_heavy_on_some_side'] += bool(hi or hj)
            # light-only sharing: on both sides the gate is 1 only at light atoms
            if not hi and not hj: out['pair_light_only'] += 1
    if (best2 and best2[0] == 0 or fail or sh_rigid) and len(EX) < 400:
        EX.append(dict(name=c.get('name'), n=n, Q=sorted(Q), D=sorted(D), h_on_atoms=None,
                       dd=[(d[0], d[1], d[3], d[4], d[6]) for d in dds],
                       F=[dds[i][0] for i in best2[1]] if best2 else None, naive2=best2[0] if best2 else None,
                       shared=[(k, G[k], [dds[i][0] for i in users[k]],
                                sorted(u for u in range(n) if W[n + k] >> (qpt | 1 << u) & 1 and u not in Q)) for k in shared],
                       useful=len(useful), sumneed=sum(need), rigid=len(rigid), sh_rigid=len(sh_rigid), fail=fail))


if __name__ == '__main__':
    A = sys.argv
    maxn = int(A[A.index('--maxn') + 1]) if '--maxn' in A else 9
    k = int(A[A.index('--states') + 1]) if '--states' in A else -1
    nex = int(A[A.index('--ex') + 1]) if '--ex' in A else 6
    rng = random.Random(int(A[A.index('--seed') + 1]) if '--seed' in A else 1)
    cs = [] if '--nostored' in A else A7.collect(maxn)
    if '--gen' in A: cs += [A7.gen_switch(rng) for _ in range(int(A[A.index('--gen') + 1]))]
    out = collections.Counter(); EX = []
    for c in cs:
        W, X, FULL = A7.tables(c['n'], c['gates'])
        if not A7.correct(c, W, X): continue
        out['circuits'] += 1
        for Q, D in A7.states(c['n'], rng, k): analyse(c, W, X, FULL, Q, D, out, EX)
    for key in sorted(out): print(key, out[key])
    tight = [e for e in EX if e['naive2'] == 0]
    print('examples with naive2 = 0:', len(tight), ' with rigid shared gates:', sum(1 for e in EX if e['sh_rigid']))
    for e in sorted(EX, key=lambda e: (e['n'], len(e['shared'])))[:nex]: print(e)
