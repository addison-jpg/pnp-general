# analysis of a one-NOT circuit for the payment lemma (h = x_a v x_b family)
# circuit: n inputs, gates list of (op,i,j) with op in and/or/not, outs[w] = wire index of o_w
import itertools

def table(n, gates):
    T = []
    for x in range(1 << n):
        w = [(x >> i) & 1 for i in range(n)]
        for op, i, j in gates:
            w.append(1 - w[i] if op == 'not' else (w[i] & w[j] if op == 'and' else w[i] | w[j]))
        T.append(w)
    return T

def cone(n, gates, o):
    C = set(); st = [o]
    while st:
        w = st.pop()
        if w < n or w in C: continue
        C.add(w); op, i, j = gates[w - n]; st += [i, j]
    return C

def check(n, sets, gates, outs, a, b):
    """returns dict or None if not in the regime"""
    T = table(n, gates); W = n + len(gates)
    full = (1 << n) - 1
    for S, o in zip(sets, outs):
        for x in range(1 << n):
            if T[x][o] != int(any(x >> v & 1 for v in S)): return {'bad': 'incorrect'}
    p = [k for k, g in enumerate(gates) if g[0] == 'not']
    assert len(p) == 1; p = p[0]; Nw = n + p; hw = gates[p][1]
    info = {}
    info['h_is_ab'] = all(T[x][hw] == int(x >> a & 1 or x >> b & 1) for x in range(1 << n))
    # clean: no gate equals an earlier wire
    cols = [tuple(T[x][w] for x in range(1 << n)) for w in range(W)]
    info['clean'] = all(cols[w] not in cols[:w] for w in range(n, W))
    reads = set()
    for op, i, j in gates: reads.add(i); reads.add(j)
    info['allread'] = all(w in reads or w in outs for w in range(n, W))
    cones = [cone(n, gates, o) for o in outs]
    info['live'] = any(Nw in C for C in cones)
    # C0 / C1
    def ev(x, nv):
        w = [(x >> i) & 1 for i in range(n)]
        for op, i, j in gates:
            w.append(nv if op == 'not' else (w[i] & w[j] if op == 'and' else w[i] | w[j]))
        return w
    def wrong(nv):
        for x in range(1 << n):
            w = ev(x, nv)
            for S, o in zip(sets, outs):
                if w[o] != int(any(x >> v & 1 for v in S)): return True
        return False
    info['C0wrong'] = wrong(0); info['C1wrong'] = wrong(1)
    info['h0'] = T[0][hw]
    # frames
    charged = {}
    for si, (S, o) in enumerate(zip(sets, outs)):
        zS = full & ~sum(1 << v for v in S)
        hard = T[zS][hw] == 1
        Nin = Nw in cones[si]
        Q = set(S) | ({a, b} if (hard and Nin) else set())
        z = full & ~sum(1 << v for v in Q)
        assert not (Nin and T[z][hw] == 1)
        par = {u: u for u in S}
        def f(u):
            while par[u] != u: u = par[u]
            return u
        cnt = 0
        for w in sorted(cones[si]):
            op, i, j = gates[w - n]
            if op != 'or' or T[z][w]: continue
            Bi = [u for u in S if T[1 << u][i]]; Bj = [u for u in S if T[1 << u][j]]
            if Bi and Bj and f(Bi[0]) != f(Bj[0]):
                # invariant check
                assert len(set(f(u) for u in Bi)) == 1 and len(set(f(u) for u in Bj)) == 1
                par[f(Bi[0])] = f(Bj[0]); cnt += 1
                charged.setdefault(w, []).append(si)
        assert cnt == len(S) - 1, (S, cnt)
    info['charged'] = charged
    info['excess'] = sum(len(v) - 1 for v in charged.values())
    nand = sum(1 for g in gates if g[0] == 'and')
    unch = sum(1 for k, g in enumerate(gates) if g[0] == 'or' and n + k not in charged)
    info['nand'] = nand; info['unch'] = unch; info['s'] = len(gates)
    info['base'] = sum(len(S) - 1 for S in sets)
    # killers
    readers = {w: [] for w in range(W)}
    for k, (op, i, j) in enumerate(gates):
        readers[i].append(n + k)
        if j != i: readers[j].append(n + k)
    def killers(g, o, pt):
        # first gates on paths g -> o whose value at pt is 0 (path gates before them all 1 at pt)
        reach = cones[outs.index(o)] if False else None
        Co = cone(n, gates, o)
        K = set(); seen = set(); st = [g]
        while st:
            w = st.pop()
            if w in seen: continue
            seen.add(w)
            for r in readers[w]:
                if r not in Co: continue
                if T[pt][r] == 0: K.add(r)
                else: st.append(r)
        return K
    col = []
    for g, L in charged.items():
        if len(L) < 2: continue
        tr = [u for u in range(n) if T[1 << u][g]]
        ent = {'g': g, 'sets': [sets[i] for i in L], 'trace': tr}
        Ks = {}
        for i in L:
            S = sets[i]
            for (side, other) in ((a, b), (b, a)):
                if side in S and other not in S:
                    Ks[(i, 'kill_e%d' % other)] = sorted(killers(g, outs[i], 1 << other))
        ent['K'] = Ks
        col.append(ent)
    info['col'] = col
    return info

def matching(left, cand):
    # left: list of keys; cand[key] = set of payers
    match = {}
    def aug(l, seen):
        for r in cand[l]:
            if r in seen: continue
            seen.add(r)
            if r not in match or aug(match[r], seen):
                match[r] = l; return True
        return False
    return sum(1 for l in left if aug(l, set()))
