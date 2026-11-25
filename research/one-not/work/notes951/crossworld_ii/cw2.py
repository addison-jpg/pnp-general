# Target claim (tractability's MinCE.crossWorld_ndep): every cross-world gate g -- g in M_z(a) at a world-0 zero point
# z of S_a (h(z) = 1) and g in M_z'(b) at a world-1 zero point z' of S_b (h(z'+e_u) = 0 for all u in S_b), a != b --
# whose z' also vanishes on S_a (hypothesis (i)) is N-dependent: C0(g) != C1(g) as functions.
# Also records whether (ii) C0(g)(Zof S_a) = 0 holds for that pair.
import sys, os, json
from multiprocessing import Pool
from nomixed import corpus, bt, mg


def flags(T, c):
    W = T.w['real']
    c0 = any(T.w[0][o] != t for o, t in zip(c['outs'], T.o)); c1 = any(T.w[1][o] != t for o, t in zip(c['outs'], T.o))
    clean = len(set(W)) == len(W) and all(0 < t < T.FULL for t in W)
    n = c['n']; read = set(c['outs'])
    for g in c['gates']: read.update(g[1:])
    live = all(n + k in read for k in range(len(c['gates'])))
    return c0 and c1, clean, live


def run(item):
    name, c = item
    T = bt.TT(c)
    if T.Ni is None or not T.correct():
        return None
    Ms, anom = mg.merges(c, T)
    n, h = T.n, T.h
    sets = c['sets']; masks = [sum(1 << v for v in S) for S in sets]
    w0 = {}  # gate -> list of (a, z) world-0 merges
    w1 = {}  # gate -> list of (b, z') world-1 merges
    for wi, S in enumerate(sets):
        for z, M in Ms[wi].items():
            if (h >> z) & 1:
                for g in M: w0.setdefault(g, []).append((wi, z))
            elif all(not (h >> (z | 1 << u)) & 1 for u in S):
                for g in M: w1.setdefault(g, []).append((wi, z))
    cross = 0; bad = []; ii_fail = 0
    for g in set(w0) & set(w1):
        ndep = T.w[0][g] != T.w[1][g]
        for a, z in w0[g]:
            zof = sum(1 << v for v in range(n) if v not in sets[a])
            for b, z2 in w1[g]:
                if a == b or z2 & masks[a]:
                    continue
                cross += 1
                ii = not (T.w[0][g] >> zof) & 1
                ii_fail += not ii
                if not ndep:
                    bad.append([g, a, z, b, z2, ii])
    ess, clean, live = flags(T, c)
    return dict(name=name, n=n, s=len(c['gates']), base=sum(len(S) - 1 for S in sets), ess=ess, clean=clean,
                live=live, cross=cross, ii_fail=ii_fail, nbad=len(bad), bad=bad[:10], circ=c if bad else None)


if __name__ == '__main__':
    out = sys.argv[1]
    cs = corpus()
    with Pool(int(os.environ.get('CW_PROCS', '4'))) as P, open(out, 'w') as f:
        for r in P.imap_unordered(run, cs, chunksize=8):
            if r is not None:
                f.write(json.dumps(r) + '\n')
    print('done', flush=True)
