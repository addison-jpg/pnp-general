# Condition (ii) of CrossWorldAt.ndep on merge sets: for every set a, every world-0 zero point z of S_a
# (h(z) = 1) and every gate g in M_z(a): C0(g)(Zof S_a) = 0, where Zof S_a = the point that is 1 exactly off S_a
# and C0 = the circuit with the NOT gate := 0. Corpus = gAdyD's nomixed.corpus() (NOMIX_ROOT, NOMIX_DC).
import sys, os, json, collections
from multiprocessing import Pool
from nomixed import corpus, bt, mg


def flags(T, c):
    W = T.w['real']
    c0 = any(T.w[0][o] != t for o, t in zip(c['outs'], T.o)); c1 = any(T.w[1][o] != t for o, t in zip(c['outs'], T.o))
    clean = len(set(W)) == len(W) and all(0 < t < T.FULL for t in W)
    return c0 and c1, clean


def run(item):
    name, c = item
    T = bt.TT(c)
    if T.Ni is None or not T.correct():
        return None
    Ms, anom = mg.merges(c, T)
    n, h, W0 = T.n, T.h, T.w[0]
    viol, checked = [], 0
    for wi, S in enumerate(c['sets']):
        zof = sum(1 << v for v in range(n) if v not in S)
        for z, M in Ms[wi].items():
            if not (h >> z) & 1:
                continue
            for g in M:
                checked += 1
                if (W0[g] >> zof) & 1:
                    viol.append([wi, z, g])
    ess, clean = flags(T, c)
    base = sum(len(S) - 1 for S in c['sets'])
    return dict(name=name, n=n, s=len(c['gates']), base=base, ess=ess, clean=clean, anom=anom,
                checked=checked, viol=viol[:20], nviol=len(viol),
                circ=c if viol else None)


if __name__ == '__main__':
    out = sys.argv[1]
    cs = corpus()
    print('corpus', len(cs), flush=True)
    with Pool(int(os.environ.get('CW_PROCS', '4'))) as P, open(out, 'w') as f:
        for r in P.imap_unordered(run, cs, chunksize=8):
            if r is not None:
                f.write(json.dumps(r) + '\n')
    print('done', flush=True)
