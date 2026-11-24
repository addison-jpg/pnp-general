"""M1 on circuits that are ALREADY irreducible (every gate read, no gate-saving rewiring; c3_norewire_corpus.irreducible)
with the NOT gate read, taken from the full corpus (data-corpora + w9 + instances, n <= NMAX). Then plain IDENT and
genuine IDENT+ as in ident_minimal.py. Usage: python3 ident_irred.py NMAX"""
import json, os, sys
from multiprocessing import Pool
sys.path.insert(0, '/home/user/pnp-general/one-not/tools/kill_tests'); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, '/home/user/pequalnp-proofs/research/front/no_minCE/supportB'); sys.path.insert(0, '/home/user/c951/tools')
import f2lib as L, c3_norewire_corpus as R
from ident_minimal import todict
import ident as I, identplus as IP

def work(item):
    t, d = item
    try:
        c = L.mk(t, d['n'], d['sets'], d['gates'], d['outs'], need_not=False)
        if c is None or not any(g[0] == 'not' for g in c['G']) or not R.irreducible(c): return None
    except Exception as e:
        return dict(tag=t, err=str(e))
    j = I.job(('x', d)); best, arg = IP.job(d)
    genuine = arg is not None and best is not None and best >= 0 and (not arg['D'] or arg['ds_delete_only'] < arg['db_delete_only'])
    return dict(tag=t, n=d['n'], s=len(d['gates']), base=sum(len(S) - 1 for S in d['sets']), adm=j['adm'],
                ident=bool(j['adm'] and j['best_kill'] and j['best_kill'] >= 1), identplus_genuine=genuine, arg=arg, circuit=d)

if __name__ == '__main__':
    import harness as H
    NMAX = int(sys.argv[1]); seen, items = set(), []
    for t, c in H.corpora():
        if c.n > NMAX or len(c.nots) != 1: continue
        k = json.dumps(c.to_dict(), sort_keys=True)
        if k in seen: continue
        seen.add(k); items.append((t, c.to_dict()))
    print('candidates', len(items), flush=True)
    st = dict(checked=0, irreducible_not_read=0, err=0, ident=0, identplus_genuine_only=0, neither=0)
    out = open('ident_irred.jsonl', 'w')
    with Pool(4) as P:
        for r in P.imap_unordered(work, items, chunksize=16):
            st['checked'] += 1
            if r is None: continue
            if 'err' in r: st['err'] += 1; continue
            st['irreducible_not_read'] += 1; st['ident'] += r['ident']
            st['identplus_genuine_only'] += r['identplus_genuine'] and not r['ident']
            if not r['ident'] and not r['identplus_genuine']: st['neither'] += 1
            out.write(json.dumps(r) + '\n'); out.flush()
            if st['checked'] % 3000 == 0: print(st, flush=True)
    print('FINAL', st, flush=True)
