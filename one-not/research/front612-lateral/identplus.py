"""IDENT+ : identify u, v (u, v in a common set S_w) and delete the outputs of a set D of other sets so that the remaining
system is (1,1)-disjoint with distinct sets (S_w may collapse to a point). Then base drops by db = 1 + sum_{t in D} d_t
and the gate count by ds = s - (live gates of the identified circuit for the kept outputs, semantic on the face).
IDENT+(c): some (u, v, D) has ds >= db. For a MinCE (s < base) that gives s' < base': a smaller counterexample.
Usage: python3 identplus.py OUT.jsonl   (only circuits where plain IDENT had no admissible pair)"""
import itertools, json, sys
from multiprocessing import Pool
from ident import tables_face

def reps(n, G, u, v):
    W, face = tables_face(n, G, u, v)
    seen = {0: -1, face: -1}
    for i in range(n): seen.setdefault(W[i], i)
    rep = {}
    for k in range(len(G)):
        w = n + k
        if W[w] in seen: rep[w] = seen[W[w]]
        else: seen[W[w]] = w
    return rep

def live_count(n, G, outs, rep):
    live, stack = set(), list(outs)
    while stack:
        w = stack.pop(); w = rep.get(w, w)
        if w < n or w in live: continue
        live.add(w); g = G[w - n]; stack.extend(g[1:2] if g[0] == 'not' else g[1:3])
    return len(live)

def ok_system(sets):
    S2 = [s for s in sets if len(s) >= 2]
    return all(len(a & b) <= 1 and a != b for a, b in itertools.combinations(S2, 2))

def job(d):
    n, G, sets, outs = d['n'], [list(g) for g in d['gates']], [frozenset(S) for S in d['sets']], d['outs']
    m = len(sets); s = len(G); best = None; arg = None
    for w, S in enumerate(sets):
        for u, v in itertools.combinations(sorted(S), 2):
            new = [frozenset(u if x == v else x for x in T) for T in sets]
            rep = reps(n, G, u, v)
            others = [t for t in range(m) if t != w]
            for r in range(0, m):
                found = False
                for D in itertools.combinations(others, r):
                    keep = [t for t in range(m) if t not in D]
                    if not ok_system([new[t] for t in keep]): continue
                    found = True
                    db = 1 + sum(len(sets[t]) - 1 for t in D)
                    ds = s - live_count(n, G, [outs[t] for t in keep], rep)
                    ds0 = s - live_count(n, G, [outs[t] for t in keep], {}) if D else 0   # deletion alone, no identification
                    val = ds - db
                    if best is None or val > best: best, arg = val, dict(w=w, u=u, v=v, D=list(D), ds=ds, db=db, ds_delete_only=ds0, db_delete_only=db - 1)
                if found: break   # minimal deletion sets only
    return best, arg

if __name__ == '__main__':
    src = {}
    sys.path.insert(0, '/home/user/pequalnp-proofs/research/front/no_minCE/supportB'); sys.path.insert(0, '/home/user/c951/tools')
    import harness as H
    want = {json.loads(l)['tag'] for l in open('ident_fail_noadm.jsonl')}
    items = [(t, c.to_dict()) for t, c in H.corpora() if t in want]
    import random; random.Random(0).shuffle(items); items = items[:int(sys.argv[2]) if len(sys.argv) > 2 else len(items)]
    out = open(sys.argv[1], 'w'); st = dict(circuits=0, identplus=0, fail=0)
    with Pool(4) as P:
        for (t, d), (best, arg) in zip(items, P.imap(job, [d for t, d in items], chunksize=32)):
            st['circuits'] += 1
            if best is not None and best >= 0:
                st['identplus'] += 1; st.setdefault('D_empty', 0); st.setdefault('delete_alone_enough', 0)
                if not arg['D']: st['D_empty'] += 1
                elif arg['ds_delete_only'] >= arg['db_delete_only'] and arg['db_delete_only'] > 0: st['delete_alone_enough'] += 1
            else: st['fail'] += 1; out.write(json.dumps(dict(tag=t, best=best, arg=arg, n=d['n'], s=len(d['gates']))) + '\n'); out.flush()
            if st['circuits'] % 500 == 0: print(st, flush=True)
    print('FINAL', st, flush=True)
