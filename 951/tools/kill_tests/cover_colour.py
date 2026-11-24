"""Sanity check of Lemma P1 / Theorem P2 (opus-global-price.md): for every point b, every gate g in a real merge
set M_b(l): g is an OR gate a | c with a(b) = c(b) = 0, every trace point p in S_l (g(b + e_p) = 1) has EXACTLY one
of a(b + e_p), c(b + e_p), and both occur.  Hence chi_g(p) := a(b + e_p) properly 2-colours every trace S_l & T_g(b)
of the family F_g(b) = {l : g in M_b(l)} with ONE colouring.  Also counts families F_g(b) of size >= 3 whose pair traces
contain an odd cycle (must be 0).
Usage: python3 -I cover_colour.py ROOT_OR_FILES... [--nmax 9]"""
import sys, os, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import global_price as GP

def real_run(L, R, b):
    n = L.n; pt = lambda x: x | (L.nu[x] << n)
    zb = pt(b); A = {u: pt(b | 1 << u) for u in R}
    lab = {u: u for u in R}; M = []
    for k, g in enumerate(L.G):
        i = n + k
        if k == L.p or L.val(i, zb): continue
        tr = {lab[u] for u in R if L.val(i, A[u])}
        if len(tr) >= 2:
            M.append(i); r = min(tr)
            for u in R:
                if lab[u] in tr: lab[u] = r
    return M

def odd_cycle(edges):
    adj = collections.defaultdict(set)
    for a, c in edges: adj[a].add(c); adj[c].add(a)
    col = {}
    for s in adj:
        if s in col: continue
        col[s] = 0; st = [s]
        while st:
            v = st.pop()
            for w in adj[v]:
                if w not in col: col[w] = 1 - col[v]; st.append(w)
                elif col[w] == col[v]: return True
    return False

args = sys.argv[1:]; NMAX = 9
if '--nmax' in args: i = args.index('--nmax'); NMAX = int(args[i + 1]); del args[i:i + 2]
st = collections.Counter()
for name, n, S, G, outs in GP.load(args):
    if n > NMAX or sum(1 for g in G if g[0] == 'not') != 1 or any(len(R) < 2 for R in S): continue
    if any(len(set(a) & set(c)) > 1 for a, c in itertools.combinations(S, 2)): continue
    try: L = GP.Lift(n, G, outs)
    except Exception: continue
    if not L.real_ok(S): continue
    st['circuits'] += 1
    pt = lambda x: x | (L.nu[x] << n)
    for b in range(1 << n):
        fam = collections.defaultdict(list)
        for l, R in enumerate(S):
            if any((b >> u) & 1 for u in R): continue
            for i in real_run(L, R, b): fam[i].append(l)
        for i, F in fam.items():
            g = G[i - n]; st['merge (g, b, l)'] += len(F)
            if g[0] != 'or': st['NOT OR'] += 1; continue
            a, c = g[1], g[2]
            ok = not L.val(a, pt(b)) and not L.val(c, pt(b))
            pairs = []
            for l in F:
                T = [p for p in S[l] if L.val(i, pt(b | 1 << p))]
                ca = [L.val(a, pt(b | 1 << p)) for p in T]; cc = [L.val(c, pt(b | 1 << p)) for p in T]
                ok &= all(x + y == 1 for x, y in zip(ca, cc)) and 0 < sum(ca) < len(T)
                if len(T) == 2: pairs.append(tuple(T))
            st['P1 ok'] += ok; st['P1 FAIL'] += not ok
            if len(F) >= 3: st['families |F_g(b)| >= 3'] += 1
            if odd_cycle(pairs): st['ODD CYCLE (must be 0)'] += 1
print(dict(st))
