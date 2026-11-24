"""Referee tests for research's F2 LIGHT case (one-not/board/agents/research-F2-light.md).

F2(Q): OR gates g with a real witness: an alive w (S_w ∩ Q = ∅), a zero point Z ⊇ Q with Z ∩ S_w = ∅ and
u != u' in S_w with real g(Z) = 0, real g(Z + e_u) = real g(Z + e_u') = 1. LIGHT at Q: h is not constant and
h(Q + e_u) = 0 for every alive point u (a point of an alive set, outside Q). real = C_{~h}: C_1 on {h = 0}, C_0 on
{h = 1}. The script checks, on random correct one-NOT circuits and every light (circuit, Q):
  B   for every alive w, the union-find merge gates of the C_1 run at Q (atoms Q + e_u) lie in F2(Q) with a witness at Q;
  K0  C_0(g)(Q + e_v) = 1  =>  g not in F2(Q + v);
  K1  C_1(g)(Q + e_v) = 1  =>  every witness of g at Q + v has h(Z') = 1 (world 0), and its set is type A at Q + v;
  K3  witnesses at Q + v are witnesses at Q of sets not through v;
  GAP a bottom merge g of a set w through v whose block misses v, with g in F2(Q + v) through witnesses with h(Z') = 0
      only. Such a g has no world-0 witness at Q + v but SURVIVES the move, so "no world-0 witness" does not imply
      g in F2(Q) minus F2(Q + v) (LIGHT-STAR's wording);
  STAR LIGHT-STAR as written (gates with no world-0 witness at Q + v) and as repaired (gates with no witness at
      Q + v, i.e. gates of the gain), over the candidate pool (bottom merges of sets through v) ∪ (F2(Q) gates with K0).
Run from one-not/:  python3 work/notes951/lemmaK_referee/f2light.py N SEED
"""
import random
import sys

sys.path.insert(0, 'tools')
sys.path.insert(0, 'work/notes951/lemmaK_referee')
from kcheck import random_circuit  # noqa: E402


def analyse(c, Q, stats, out):
    n, s = c.n, len(c.gates)
    T, T0, T1 = c.tables(), c.tables(force=0), c.tables(force=1)
    h = T[c.h_wire]
    full_pts = (1 << n) - 1
    sets = [sum(1 << u for u in S) for S in c.sets]
    alive = [i for i, m in enumerate(sets) if m & Q == 0]
    if not alive:
        return
    apts = sorted({u for i in alive for u in c.sets[i]})
    hv = [h >> p & 1 for p in range(1 << n)]
    if len(set(hv)) == 1 or any(hv[Q | 1 << u] for u in apts):
        return                                          # not light
    stats['light'] += 1
    ors = [n + k for k, g in enumerate(c.gates) if g[0] == 'or']

    def real(g, p):
        return T[g] >> p & 1

    def witnesses(g, Qm):
        """Witnesses (w, Z, world0) of OR gate g at restriction Qm."""
        res = []
        for i, m in enumerate(sets):
            if m & Qm:
                continue
            free = full_pts & ~(Qm | m)
            sub = free
            while True:
                Z = Qm | sub
                if not real(g, Z):
                    us = [u for u in c.sets[i] if real(g, Z | 1 << u)]
                    if len(us) >= 2:
                        res.append((i, Z, hv[Z] == 1))
                if sub == 0:
                    break
                sub = (sub - 1) & free
        return res

    W = {g: witnesses(g, Q) for g in ors}
    F2 = {g for g in ors if W[g]}
    # B: bottom merges via union-find in C_1 at Q
    bottom = {}
    for i in alive:
        S = c.sets[i]
        comp = {u: u for u in S}

        def find(u):
            while comp[u] != u:
                u = comp[u]
            return u
        merges = []
        for g in range(n, n + s):
            if (T1[g] >> Q) & 1:
                continue
            op = c.gates[g - n]
            if op[0] != 'or':
                continue
            a, b = op[1:]
            ua = {u for u in S if (T1[a] >> (Q | 1 << u)) & 1 and not (T1[a] >> Q) & 1}
            ub = {u for u in S if (T1[b] >> (Q | 1 << u)) & 1 and not (T1[b] >> Q) & 1}
            if ua and ub:
                ra, rb = find(min(ua)), find(min(ub))
                if ra != rb:
                    comp[ra] = rb
                    merges.append(g)
        if len(merges) < len(S) - 1:
            out.append(('B-count', c.to_dict(), Q, i))
            return
        for g in merges:
            if not any(w == i and Z == Q for (w, Z, _) in W.get(g, [])):
                out.append(('B-witness', c.to_dict(), Q, i, g))
                return
        bottom[i] = merges
    stats['B_ok'] += 1
    for v in apts:
        Qv = Q | 1 << v
        Wv = {g: witnesses(g, Qv) for g in ors}
        F2v = {g for g in ors if Wv[g]}
        for g in ors:
            if (T0[g] >> Qv) & 1 and g in F2v:
                out.append(('K0', c.to_dict(), Q, v, g))
                return
            if (T1[g] >> Qv) & 1:
                for (w, Z, w0) in Wv[g]:
                    top = full_pts & ~sets[w]
                    if not w0 or not hv[top]:
                        out.append(('K1', c.to_dict(), Q, v, g))
                        return
            for (w, Z, w0) in Wv[g]:
                if (w, Z, w0) not in W[g] or (sets[w] >> v) & 1:
                    out.append(('K3', c.to_dict(), Q, v, g))
                    return
        stats['K_ok'] += 1
        # GAP search
        star = [i for i in alive if (sets[i] >> v) & 1]
        for i in star:
            for g in bottom[i]:
                block_has_v = (T1[g] >> Qv) & 1
                if block_has_v:
                    continue
                if g in F2v and not any(w0 for (_, _, w0) in Wv[g]):
                    stats['gap'] += 1
                    if stats['gap'] <= 2:
                        out.append(('GAP', c.to_dict(), Q, v, g))
        # LIGHT-STAR, written vs repaired
        cost = sum(len(c.sets[i]) - 1 for i in star)
        pool = set(g for i in star for g in bottom[i]) | {g for g in F2 if (T0[g] >> Qv) & 1}
        written = {g for g in pool if not any(w0 for (_, _, w0) in Wv[g])}
        repaired = {g for g in pool if g not in F2v}
        stats.setdefault('_star', {}).setdefault(id(c), []).append((len(written) >= cost, len(repaired) >= cost,
                                                                    len(F2 - F2v) >= cost))


def main():
    N, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    stats = {'light': 0, 'B_ok': 0, 'K_ok': 0, 'gap': 0}
    out = []
    star_w = star_r = step = instances = 0
    for _ in range(N):
        n = rng.choice((4, 5, 6))
        c = random_circuit(rng, n, rng.randrange(6, 18))
        if c is None or len(c.sets) < 2:
            continue
        Q = rng.randrange(1 << n) & rng.randrange(1 << n)
        analyse(c, Q, stats, out)
        fails = [o for o in out if o[0] != 'GAP']
        if fails:
            print('FAIL', fails[0])
            return 1
        res = stats.pop('_star', {}).get(id(c))
        if res:
            instances += 1
            star_w += any(a for a, _, _ in res)
            star_r += any(b for _, b, _ in res)
            step += any(x for _, _, x in res)
    print({k: v for k, v in stats.items()},
          'light instances with an alive v:', instances,
          '| exists v: LIGHT-STAR as written', star_w, ', repaired', star_r, ', the step gain >= cost', step)
    for o in out[:2]:
        print(o[0], o[1:])
    return 0


if __name__ == '__main__':
    sys.exit(main())
