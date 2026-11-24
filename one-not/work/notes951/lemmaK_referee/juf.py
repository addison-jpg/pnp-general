"""Kill test for a proof route of SEE+K3 (dwV8p): the JOINT union-find over the star of v.
P = union of the alive sets through v (pairwise meeting only in v), so |P| - 1 = cost(v). Run union-find over P at the zero
point Q in the REAL circuit (blocks {x in P : real g(Q + e_x) = 1}); the invariant holds for the real circuit at any Q (the
NOT gate is either 1 at Q or has an empty block), so there are >= cost(v) DISTINCT merge OR gates. Kinds of merge gate:
  same : its two merged units lie in one star set (then it is in F2(Q), witness at Z = Q);
  cross: they lie in two different star sets (it need not be in F2(Q)).
JUF-GAIN (the route): some v has >= cost(v) joint merges in gain(v) = F2(Q) minus F2(Q + v).
Run from one-not/:  python3 work/notes951/lemmaK_referee/juf.py N SEED
"""
import random
import sys

sys.path.insert(0, 'tools')
sys.path.insert(0, 'work/notes951/lemmaK_referee')
from kcheck import random_circuit  # noqa: E402
from f2synth import run  # noqa: E402  (reuse nothing but the import path check)


def f2set(c, T, Qm):
    n, full = c.n, (1 << c.n) - 1
    sets = [sum(1 << u for u in S) for S in c.sets]
    res = set()
    for k, g in enumerate(c.gates):
        if g[0] != 'or':
            continue
        w_ = n + k
        for i, m in enumerate(sets):
            if m & Qm or w_ in res:
                continue
            free = full & ~(Qm | m)
            sub = free
            while True:
                Z = Qm | sub
                if not (T[w_] >> Z & 1) and sum(1 for u in c.sets[i] if T[w_] >> (Z | 1 << u) & 1) >= 2:
                    res.add(w_)
                    break
                if sub == 0:
                    break
                sub = (sub - 1) & free
    return res


def main():
    N, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    st = {'instances': 0, 'juf_gain_ok': 0, 'step_ok': 0, 'merges_ge_cost': 0, 'pairs': 0, 'cross_merges': 0,
          'same_merges': 0, 'same_not_dying': 0}
    for _ in range(N):
        n = rng.choice((4, 5, 6))
        c = random_circuit(rng, n, rng.randrange(6, 18))
        if c is None or len(c.sets) < 2:
            continue
        Q = rng.randrange(1 << n) & rng.randrange(1 << n)
        T = c.tables()
        sets = [sum(1 << u for u in S) for S in c.sets]
        alive = [i for i, m in enumerate(sets) if m & Q == 0]
        if not alive:
            continue
        apts = sorted({u for i in alive for u in c.sets[i]})
        F2 = f2set(c, T, Q)
        st['instances'] += 1
        juf_ok = step_ok = False
        for v in apts:
            star = [i for i in alive if sets[i] >> v & 1]
            P = sorted({u for i in star for u in c.sets[i]})
            cost = len(P) - 1
            gain = F2 - f2set(c, T, Q | 1 << v)
            step_ok |= len(gain) >= cost
            comp = {x: x for x in P}

            def find(x):
                while comp[x] != x:
                    x = comp[x]
                return x
            merges = []
            for k, g in enumerate(c.gates):
                w_ = n + k
                if g[0] != 'or' or T[w_] >> Q & 1:
                    continue
                a, b = g[1:]
                ba = [x for x in P if not (T[a] >> Q & 1) and T[a] >> (Q | 1 << x) & 1]
                bb = [x for x in P if not (T[b] >> Q & 1) and T[b] >> (Q | 1 << x) & 1]
                if ba and bb and find(ba[0]) != find(bb[0]):
                    xa, xb = ba[0], bb[0]
                    comp[find(xa)] = find(xb)
                    same = any((sets[i] >> xa & 1) and (sets[i] >> xb & 1) for i in star)
                    merges.append((w_, same))
            st['pairs'] += 1
            st['merges_ge_cost'] += len(merges) >= cost
            st['cross_merges'] += sum(1 for _, s in merges if not s)
            st['same_merges'] += sum(1 for _, s in merges if s)
            st['same_not_dying'] += sum(1 for w_, s in merges if s and w_ not in gain)
            if sum(1 for w_, _ in merges if w_ in gain) >= cost:
                juf_ok = True
        st['juf_gain_ok'] += juf_ok
        st['step_ok'] += step_ok
    print(st)


if __name__ == '__main__':
    main()
