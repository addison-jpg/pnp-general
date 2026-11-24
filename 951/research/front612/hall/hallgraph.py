"""Data for the heredity lane (BOARD 11 UTC: Hall for a MinCE graph system). Graph system = every set has 2 points;
then each pure class (sdrcert/pure_export.menus: I1 at any Z avoiding S_w with h(Z) = 0, I0 at top_w with minterms)
is one gate and PureSDR <=> Hall on the pure menus (Lean pureSDR_iff_hall).
Per circuit: U_w = gates offered to set w. Hall surplus of a family F = |∪_{w∈F} U_w| - |F|; report the minimum over
all nonempty F and every tight family (surplus 0). For each tight F: restrict the circuit to F (delete the other
outputs, then x_v := 0 for every v outside ∪F; w951 delete_outputs + restrict, semantic) and report
s' - base(F) (base(F) = |F|) and |∪U_w|, to see what a Hall-tight family leaves in the restricted circuit.
Usage: python3 hallgraph.py OUT.jsonl"""
import itertools, json, os, sys
from multiprocessing import Pool
sys.path.insert(0, '/home/user/c951/tools'); sys.path.insert(0, '/home/user/pnp-general/951/tools/sdrcert')
sys.path.insert(0, '/home/user/pequalnp-proofs/research/front/no_minCE/supportB')
from w951 import Circuit
import pure_export as PE

def gates_of(opts):
    U = set()
    for M in opts:
        assert len(M) == 1, ('graph system class with != 1 gate', M)
        U |= set(M)
    return U

def restrict_to(c, F):
    drop = [w for w in range(len(c.sets)) if w not in F]
    c2 = c.delete_outputs(drop).circuit if drop else c
    keep = set(v for w in F for v in c.sets[w])
    for v in range(c.n):
        if v not in keep: c2 = c2.restrict(v, 0).circuit
    return c2

def job(item):
    tag, d = item
    try:
        c = Circuit.from_dict(d)
        if len(c.nots) != 1 or any(len(S) != 2 for S in c.sets) or len(c.sets) < 2 or not c.is_correct(): return None
        n, S, G, p, opts = PE.menus(d)
        U = [gates_of(o) for o in opts]; m = len(U)
        best = None; tight = []
        for r in range(1, m + 1):
            for F in itertools.combinations(range(m), r):
                sur = len(set().union(*(U[w] for w in F))) - r
                best = sur if best is None else min(best, sur)
                if sur == 0: tight.append(F)
        rows = []
        for F in tight[:20]:
            c2 = restrict_to(c, F)
            rows.append(dict(F=F, union=len(set().union(*(U[w] for w in F))), s_restr=c2.s, slack=c2.s - len(F)))
        return dict(tag=tag, n=c.n, s=c.s, base=c.base, m=m, ess=c.is_essential(), menu_sizes=[len(u) for u in U],
                    min_surplus=best, n_tight=len(tight), tight=rows)
    except Exception as e:
        return dict(tag=tag, err=f'{type(e).__name__}: {e}')

if __name__ == '__main__':
    import harness as H
    seen, items = set(), []
    for t, c in H.corpora():
        if any(len(S) != 2 for S in c.sets): continue
        k = json.dumps(c.to_dict(), sort_keys=True)
        if k in seen: continue
        seen.add(k); items.append((t, c.to_dict()))
    print(f'{len(items)} distinct graph-system circuits', flush=True)
    out = open(sys.argv[1], 'w'); st = dict(done=0, err=0, hall_fail=0, tight_circuits=0, min_slack_tight=None)
    with Pool(4) as P:
        for r in P.imap_unordered(job, items, chunksize=16):
            if r is None: continue
            out.write(json.dumps(r) + '\n')
            if 'err' in r: st['err'] += 1; continue
            st['done'] += 1; st['hall_fail'] += r['min_surplus'] < 0; st['tight_circuits'] += r['n_tight'] > 0
            for t in r['tight']:
                st['min_slack_tight'] = t['slack'] if st['min_slack_tight'] is None else min(st['min_slack_tight'], t['slack'])
            if st['done'] % 2000 == 0: print(st, flush=True)
    print('FINAL', st, flush=True)
