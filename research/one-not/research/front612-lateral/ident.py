"""Lateral move test: induction by VARIABLE IDENTIFICATION (x_v := x_u) instead of constant restriction.
IDENT(c): there are u != v in a common set S_w such that
  (adm) identifying u, v keeps the system (1,1)-disjoint with no set collapsing to < 2 points except possibly
        S_w itself (S_w loses one point; base drops by exactly 1), and
  (kill) the identified circuit needs >= 1 gate fewer: after x_v := x_u, some gate is constant, equals an input,
        equals an earlier gate, or is no longer in any output cone (semantic, on the face x_u = x_v).
If IDENT holds for a MinCE (s < base), the identified circuit has s' <= s - 1 < base - 1 = base': a smaller
counterexample (needs: the identified system is in the 951 class; checked by (adm)). Data only.
Usage: python3 ident.py OUT.jsonl"""
import itertools, json, os, sys
from multiprocessing import Pool
sys.path.insert(0, '/home/user/pequalnp-proofs/research/front/no_minCE/supportB'); sys.path.insert(0, '/home/user/c951/tools')

def tables_face(n, G, u, v):
    P = 1 << n; FULL = (1 << P) - 1
    face = sum(1 << x for x in range(P) if (x >> u & 1) == (x >> v & 1))
    W = [sum(1 << x for x in range(P) if x >> i & 1) & face for i in range(n)]
    for g in G:
        if g[0] == 'not': W.append((FULL ^ W[g[1]]) & face)
        elif g[0] == 'and': W.append(W[g[1]] & W[g[2]])
        else: W.append(W[g[1]] | W[g[2]])
    return W, face

def removed(n, G, outs, u, v):
    W, face = tables_face(n, G, u, v)
    seen = {0: -1, face: -1}
    for i in range(n): seen.setdefault(W[i], i)
    rep = {}
    for k in range(len(G)):
        w = n + k
        if W[w] in seen: rep[w] = seen[W[w]]
        else: seen[W[w]] = w
    # live gates after replacing redundant ones by their representatives
    live, stack = set(), [o for o in outs]
    while stack:
        w = stack.pop()
        w = rep.get(w, w)
        if w < n or w < 0 or w in live: continue
        live.add(w); g = G[w - n]
        stack.extend(g[1:2] if g[0] == 'not' else g[1:3])
    return len(G) - len(live)

def admissible(sets, u, v):
    # the one set containing both u and v may collapse to a single point (it becomes a trivial output, base - 1)
    new = [frozenset(u if x == v else x for x in S) for S in sets]
    new = [S for S in new if len(S) >= 2]
    for i in range(len(new)):
        for j in range(i + 1, len(new)):
            if len(new[i] & new[j]) > 1 or new[i] == new[j]: return False
    return True

def job(item):
    tag, d = item
    n, G, sets, outs = d['n'], [list(g) for g in d['gates']], [list(S) for S in d['sets']], d['outs']
    if n > 14: return None
    pairs = {(min(a, b), max(a, b)) for S in sets for a, b in itertools.combinations(S, 2)}
    adm = [p for p in pairs if admissible(sets, *p)]
    best = max((removed(n, G, outs, u, v) for u, v in adm), default=None)
    base = sum(len(S) - 1 for S in sets)
    return dict(tag=tag, n=n, s=len(G), base=base, pairs=len(pairs), adm=len(adm), best_kill=best)

if __name__ == '__main__':
    import harness as H
    seen, items = set(), []
    for t, c in H.corpora():
        if len(c.nots) != 1: continue
        k = json.dumps(c.to_dict(), sort_keys=True)
        if k in seen: continue
        seen.add(k); items.append((t, c.to_dict()))
    out = open(sys.argv[1], 'w'); st = dict(circuits=0, no_adm=0, adm_but_no_kill=0, ident=0); noadm = open(sys.argv[1].replace('.jsonl', '_noadm.jsonl'), 'w')
    with Pool(4) as P:
        for r in P.imap_unordered(job, items, chunksize=32):
            if r is None: continue
            st['circuits'] += 1
            if r['adm'] == 0: st['no_adm'] += 1; noadm.write(json.dumps(r) + '\n')
            elif r['best_kill'] == 0: st['adm_but_no_kill'] += 1; out.write(json.dumps(r) + '\n')
            else: st['ident'] += 1
    print('FINAL', st, flush=True)
