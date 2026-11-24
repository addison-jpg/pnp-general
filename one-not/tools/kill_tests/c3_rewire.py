# Conjecture C3_k against MinCE.no_rewire (old: R6).  Serves README items L2, C3.
# Greedy reduction: while some gate input can be moved to another existing wire (no cycle) so that every output stays correct
# and a gate goes unread, do it and delete the unread gates.  After each reduction prints the depth at the empty cube
# (least |D| with slack(D) <= slack(empty), base smaller; c3_tab definitions, truth tables as big integers).
# The last circuit admits no gate-saving rewiring (it satisfies MinCE.no_rewire as a property of the circuit).
# Run: python3 -I one-not/tools/kill_tests/c3_rewire.py FILE.json [cap] [out.json|-] [notonly]
# 'notonly': only rewirings of the input of the NOT gate are tried (fast at n = 24; shows that MinCE.no_rewire fails).
import sys, json, itertools
d = json.load(open(sys.argv[1])); cap = int(sys.argv[2]) if len(sys.argv) > 2 else 3
n = d['n']; S = d['sets']; P = 1 << n; FULL = (1 << P) - 1
X = []
for v in range(n):
    t = ((1 << (1 << v)) - 1) << (1 << v); w = 1 << (v + 1)
    while w < P: t |= t << w; w *= 2
    X.append(t)
want = []
for R in S:
    t = 0
    for u in R: t |= X[u]
    want.append(t)
def topo(G, outs):
    # gates as dict wire -> gate; returns evaluation order of the live gates or None on a cycle
    order = []; state = {}
    def visit(i):
        if i < n or state.get(i) == 2: return True
        if state.get(i) == 1: return False
        state[i] = 1
        for j in G[i][1:]:
            if not visit(j): return False
        state[i] = 2; order.append(i); return True
    for o in outs:
        if not visit(o): return None
    return order
def evalc(G, order):
    W = {v: X[v] for v in range(n)}
    for i in order:
        g = G[i]; W[i] = FULL ^ W[g[1]] if g[0] == 'not' else (W[g[1]] & W[g[2]] if g[0] == 'and' else W[g[1]] | W[g[2]])
    return W
def depth0(G, outs, order, W):
    wm = []
    for i in order:
        if G[i][0] != 'or': continue
        t = W[i]; nt = FULL ^ t
        for wi, R in enumerate(S):
            av = nt
            for u in R: av &= FULL ^ X[u]
            if not av: continue
            one = two = 0
            for u in R:
                a = av & (t >> (1 << u)); two |= one & a; one |= a
            if two: wm.append((i, wi, two))
    def slack(Q):
        cb = FULL
        for v in Q: cb &= X[v]
        al = {wi for wi, R in enumerate(S) if not set(R) & set(Q)}
        return len({i for i, wi, M in wm if wi in al and M & cb}) - sum(len(S[wi]) - 1 for wi in al), sum(len(S[wi]) - 1 for wi in al)
    s0, b0 = slack([]); best = {}
    for k in range(1, cap + 1):
        for D in itertools.combinations(range(n), k):
            s, b = slack(list(D))
            if b < b0 and (k not in best or s - s0 < best[k]): best[k] = s - s0
        if best.get(k, 1) <= 0: return s0, k, best
    return s0, None, best
NOTONLY = len(sys.argv) > 4 and sys.argv[4] == 'notonly'
G = {n + k: list(g) for k, g in enumerate(d['gates'])}; outs = list(d['outs'])
order = topo(G, outs); G = {i: G[i] for i in order}
while True:
    W = evalc(G, order); assert all(W[o] == t for o, t in zip(outs, want)), 'incorrect'
    nots = [i for i in order if G[i][0] == 'not']; hdep = None
    if nots:
        h = W[G[nots[0]][1]]; hdep = sum(1 for v in range(n) if (h ^ (h >> (1 << v))) & (FULL ^ X[v]))
    s0, dp, best = depth0(G, outs, order, W)
    print('gates', len(G), 'NOT gate', 'read, its input depends on %d inputs' % hdep if nots else 'unread', '| slack(empty)', s0, 'depth at empty', dp if dp else '> %d' % cap, best, flush=True)
    found = None; wires = list(range(n)) + order
    for r in (nots if NOTONLY else order):
        for pos in range(1, len(G[r])):
            for f in wires:
                if f == G[r][pos] or f == r: continue
                G2 = dict(G); G2[r] = list(G[r]); G2[r][pos] = f
                o2 = topo(G2, outs)
                if o2 is None or len(o2) >= len(G): continue          # cycle, or no gate saved
                W2 = evalc(G2, o2)
                if all(W2[o] == t for o, t in zip(outs, want)): found = (r, pos, f, G2, o2); break
            if found: break
        if found: break
    if not found: break
    r, pos, f, G2, o2 = found
    print('   rewire: input %d of gate %d %s -> wire %d; gates saved: %d' % (pos, r, G[r], f, len(G) - len(o2)))
    G = {i: G2[i] for i in o2}; order = o2
print('no gate-saving rewiring of the NOT gate left:' if NOTONLY else 'no gate-saving rewiring left:', len(G), 'gates; base', sum(len(R) - 1 for R in S))
if len(sys.argv) > 3 and sys.argv[3] != '-':
    ren = {v: v for v in range(n)}
    for j, i in enumerate(order): ren[i] = n + j
    json.dump(dict(name=d.get('name', '') + ' rewire-reduced', n=n, sets=S, gates=[[G[i][0]] + [ren[x] for x in G[i][1:]] for i in order], outs=[ren[o] for o in outs]), open(sys.argv[3], 'w'))
