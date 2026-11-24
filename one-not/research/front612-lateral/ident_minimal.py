"""M1 on minimal-like circuits. Corpus: kill_tests f2lib corpus (n <= NMAX) + randgen + one-not/data/fano_sat66.json,
each reduced greedily by gate-saving rewirings (c3_norewire_corpus.reduce: every gate read, no gate-saving rewiring =
MinCE.no_rewire as a circuit property). Kept: the NOT gate still read (a MinCE's NOT is used). For each kept circuit:
plain IDENT (adm + kill) and IDENT+ where identification is genuinely needed (output deletion alone does not pay).
Also reports output-deletion savings (a MinCE has none: MinCE.outDel). Data only.
Usage: python3 ident_minimal.py NMAX RANDCOUNT"""
import json, os, sys
from multiprocessing import Pool
KT = '/home/user/pnp-general/one-not/tools/kill_tests'
sys.path.insert(0, KT); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import f2lib as L, c3_norewire_corpus as R
import ident as I, identplus as IP

def todict(c): return dict(n=c['n'], sets=[list(s) for s in c['S']], gates=[list(g) for g in c['G']], outs=list(c['outs']))

def work(c):
    try:
        r = R.reduce(c)
    except Exception as e:
        return dict(err=str(e))
    if not any(g[0] == 'not' for g in r['G']): return dict(skip='NOT unread')
    d = todict(r)
    j = I.job(('x', d))
    best, arg = IP.job(d)
    genuine = arg is not None and best is not None and best >= 0 and (not arg['D'] or arg['ds_delete_only'] < arg['db_delete_only'])
    return dict(name=c['name'], n=d['n'], s=len(d['gates']), base=sum(len(S) - 1 for S in d['sets']), adm=j['adm'] if j else None,
                ident=bool(j and j['adm'] and j['best_kill'] and j['best_kill'] >= 1), identplus=best is not None and best >= 0,
                identplus_genuine=genuine, arg=arg, circuit=d)

if __name__ == '__main__':
    NMAX, CNT = int(sys.argv[1]), int(sys.argv[2])
    CS = L.corpus(NMAX) + (L.randgen(1, CNT) if CNT else [])
    for i, d in enumerate(json.load(open('/home/user/pnp-general/one-not/data/fano_sat66.json'))):
        c = L.mk(f'fano_sat66:{i}', d['n'], d['sets'], d['gates'], d['outs'], need_not=False)
        if c is not None: CS.append(c)
    print('circuits', len(CS), flush=True)
    st = dict(reduced=0, not_unread=0, err=0, kept=0, ident=0, identplus_genuine=0, neither=0); seen = set()
    out = open('ident_minimal.jsonl', 'w')
    with Pool(4) as P:
        for r in P.imap_unordered(work, CS, chunksize=4):
            st['reduced'] += 1
            if 'err' in r: st['err'] += 1; continue
            if 'skip' in r: st['not_unread'] += 1; continue
            k = json.dumps(r['circuit'], sort_keys=True)
            if k in seen: continue
            seen.add(k); st['kept'] += 1; st['ident'] += r['ident']; st['identplus_genuine'] += r['identplus_genuine'] and not r['ident']
            if not r['ident'] and not r['identplus_genuine']: st['neither'] += 1
            out.write(json.dumps(r) + '\n'); out.flush()
            if st['reduced'] % 500 == 0: print(st, flush=True)
    print('FINAL', st, flush=True)
