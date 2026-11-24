# liftmenu.py (scaffold 951, 2026-11-24): EXACT liftMenu (Lean W951/PureGP.lean semantics) for circuits with k >= 1 NOT gates,
# MUL margin |U liftMenu| - base, LiftSDR; generators for the m-selector path and m-hub plane circuits.
# Lifted circuit: each NOT output := a free input y_i (coordinate n+i). Test system t = (P, A_c for c in S_w), points of
# {0,1}^(n+k): o_w(P) = 0; o_w(A_c) = 1 (A_c alone); separation: the sets A_c \ P are pairwise disjoint (all coordinates).
# Class = runMT: union-find over S_w on wires g with g(P) = 0, B(g) = {c : g(A_c) = 1}; merge at an OR gate whose inputs have
# nonempty B in different blocks. Atoms are interchangeable and every valid atom has A \ P nonempty (the lifted circuit is
# monotone), so a test system = k distinct atom profiles with pairwise disjoint exclusive parts; the enumeration is complete.
#   python3 liftmenu.py FILE.json [NAME ...]     (FILE: {name: circuit} or one circuit)
# Landed by coord (scaffold cannot push).
import sys, json, itertools

def lifted_vectors(c):
    n = c['n']; nots = [k for k, g in enumerate(c['gates']) if g[0] == 'not']; R = 1 << (n + len(nots))
    T = [sum(((r >> i) & 1) << r for r in range(R)) for i in range(n)]
    ycol = {k: sum(((r >> (n + j)) & 1) << r for r in range(R)) for j, k in enumerate(nots)}
    for k, g in enumerate(c['gates']):
        if g[0] == 'not': T.append(ycol[k])
        elif g[0] == 'and': T.append(T[g[1]] & T[g[2]])
        else: T.append(T[g[1]] | T[g[2]])
    vec = [0] * R
    for w in range(len(T)):
        t = T[w]
        for r in range(R):
            if t >> r & 1: vec[r] |= 1 << w
    return T, vec, R

def menu(c, w, T, vec, R):
    n = c['n']; k = len(c['sets'][w]); o = c['outs'][w]; allw = (1 << len(T)) - 1
    ors = [(n + i, g[1], g[2]) for i, g in enumerate(c['gates']) if g[0] == 'or']
    zeros = [r for r in range(R) if not (T[o] >> r & 1)]; ones = [r for r in range(R) if T[o] >> r & 1]
    classes = set()
    for P in zeros:
        Z = allw & ~vec[P]; zors = [(g, a, b) for (g, a, b) in ors if Z >> g & 1]; prof = {}
        for A in ones:
            pr = vec[A] & Z
            if pr not in prof: prof[pr] = A & ~P
        items = list(prof.items())
        def rec(start, used, chosen):
            if len(chosen) == k:
                par = list(range(k))
                def find(x):
                    while par[x] != x: par[x] = par[par[x]]; x = par[x]
                    return x
                M = []
                for (g, a, b) in zors:
                    ba = [i for i in range(k) if chosen[i] >> a & 1]; bb = [i for i in range(k) if chosen[i] >> b & 1]
                    if ba and bb:
                        ra, rb = find(ba[0]), find(bb[0])
                        if ra != rb: par[ra] = rb; M.append(g)
                classes.add(frozenset(M)); return
            for j in range(start, len(items)):
                pr, ex = items[j]
                if not (ex & used): rec(j + 1, used | ex, chosen + [pr])
        rec(0, 0, [])
    return classes

def evaluate(c):
    T, vec, R = lifted_vectors(c); base = sum(len(S) - 1 for S in c['sets'])
    menus = [menu(c, w, T, vec, R) for w in range(len(c['sets']))]
    U = frozenset().union(*[M for cl in menus for M in cl])
    lists = [list(m) for m in menus]; order = sorted(range(len(lists)), key=lambda i: len(lists[i]))
    def rec(i, used, ch):
        if i == len(order): return dict(ch)
        for M in lists[order[i]]:
            if not (M & used):
                ch[order[i]] = sorted(M); r = rec(i + 1, used | M, ch)
                if r: return r
                del ch[order[i]]
        return None
    return {'s': len(c['gates']), 'base': base, 'MUL_margin': len(U) - base, 'menu_sizes': [len(m) for m in menus],
            'LiftSDR': rec(0, frozenset(), {})}

def selector_path(sets2, nsel, shifts=None):
    # 2-sets e_0..e_{L-1} (cyclic); selectors = new inputs in no set; world w (sign pattern) has shift t_w;
    # g_j = OR_w (lit_w AND OR(e_{j+t_w})) (OR split as (lit AND x_u) OR (lit AND x_v)); o_j = OR_w (lit_w AND g_{j-t_w}).
    n0 = 1 + max(max(e) for e in sets2); n = n0 + nsel; L = len(sets2); G = []
    def add(op, a, b=None):
        G.append([op, a] if b is None else [op, a, b]); return n + len(G) - 1
    sel = [n0 + i for i in range(nsel)]; neg = [add('not', s) for s in sel]
    worlds = list(itertools.product([1, 0], repeat=nsel)); shifts = shifts or list(range(len(worlds))); lit = {}
    for w in worlds:
        ls = [sel[i] if w[i] else neg[i] for i in range(nsel)]; x = ls[0]
        for l in ls[1:]: x = add('and', x, l)
        lit[w] = x
    g = []
    for j in range(L):
        terms = []
        for wi, w in enumerate(worlds):
            u, v = sets2[(j + shifts[wi]) % L]; terms.append(add('or', add('and', lit[w], u), add('and', lit[w], v)))
        x = terms[0]
        for t in terms[1:]: x = add('or', x, t)
        g.append(x)
    outs = []
    for j in range(L):
        terms = [add('and', lit[w], g[(j - shifts[wi]) % L]) for wi, w in enumerate(worlds)]; x = terms[0]
        for t in terms[1:]: x = add('or', x, t)
        outs.append(x)
    return {'n': n, 'sets': [list(e) for e in sets2], 'gates': G, 'outs': outs}

def hub_circuit(n, lines, hubs, perms):
    # hubs = points of the space used as selectors; per world a permutation of the lines.
    G = []
    def add(op, a, b=None):
        G.append([op, a] if b is None else [op, a, b]); return n + len(G) - 1
    neg = [add('not', a) for a in hubs]; worlds = list(itertools.product([1, 0], repeat=len(hubs))); lit = {}
    for w in worlds:
        ls = [hubs[i] if w[i] else neg[i] for i in range(len(hubs))]; x = ls[0]
        for l in ls[1:]: x = add('and', x, l)
        lit[w] = x
    L = len(lines); g = []
    for j in range(L):
        terms = []
        for wi, w in enumerate(worlds):
            parts = [add('and', lit[w], u) for u in lines[perms[wi][j]]]; x = parts[0]
            for p in parts[1:]: x = add('or', x, p)
            terms.append(x)
        x = terms[0]
        for t in terms[1:]: x = add('or', x, t)
        g.append(x)
    outs = []
    for j in range(L):
        terms = [add('and', lit[w], g[perms[wi].index(j)]) for wi, w in enumerate(worlds)]; x = terms[0]
        for t in terms[1:]: x = add('or', x, t)
        outs.append(x)
    return {'n': n, 'sets': [list(S) for S in lines], 'gates': G, 'outs': outs}

if __name__ == '__main__':
    B = json.load(open(sys.argv[1])); B = B if 'gates' not in B else {sys.argv[1]: B}
    for nm in (sys.argv[2:] or list(B)):
        print(nm, json.dumps(evaluate(B[nm])), flush=True)
