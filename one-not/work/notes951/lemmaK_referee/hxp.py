"""Referee test of front A2's h = x_p theorem (coord 13:10). Lifted circuit M(x, y): the NOT gate replaced by y, so
M(., y) = C_y. Classes (one per alive set, relative to Q; Q = ∅ is the plain theorem; needs h = x_p on the cube x ⊇ Q):
  star w ∋ p : zero point (top_w, 1), atoms (Q + e_u, 1) for u in S_w minus p and (Q + e_p, 0);
  non-star w : zero point (top_w minus p, 1), atoms (Q + e_c, 1) for c in S_w.
Checks: validity (o_w is 0 at the zero point and 1 at every atom, in M); union-find merges = exactly d_w; classes pairwise
disjoint; every merge in F2(Q); |F2(Q)| >= base(alive at Q).
Run from one-not/:  python3 work/notes951/lemmaK_referee/hxp.py N SEED
"""
import random
import sys

sys.path.insert(0, 'tools')
sys.path.insert(0, 'work/notes951/lemmaK_referee')
from kcheck import random_circuit  # noqa: E402
from w951 import Circuit  # noqa: E402
from juf import f2set  # noqa: E402


def classes(c, Q, p):
    n, full = c.n, (1 << c.n) - 1
    C = {0: c.tables(force=0), 1: c.tables(force=1)}
    sets = [sum(1 << u for u in S) for S in c.sets]
    res = {}
    for i, S in enumerate(c.sets):
        if sets[i] & Q:
            continue
        if p in S:
            Z = full & ~sets[i]
            atoms = [(Q | 1 << u, 1) for u in S if u != p] + [(Q | 1 << p, 0)]
        else:
            Z = full & ~sets[i] & ~(1 << p)
            atoms = [(Q | 1 << u, 1) for u in S]
        o = c.outs[i]
        if C[1][o] >> Z & 1 or not all(C[y][o] >> a & 1 for a, y in atoms):
            return None, 'invalid test system at set %d' % i
        comp = list(range(len(atoms)))

        def find(k):
            while comp[k] != k:
                k = comp[k]
            return k

        def block(wire):
            if C[1][wire] >> Z & 1:
                return None
            return [k for k, (a, y) in enumerate(atoms) if C[y][wire] >> a & 1]
        merges = []
        for k, g in enumerate(c.gates):
            if g[0] != 'or':
                continue
            ba, bb = block(g[1]), block(g[2])
            if ba and bb and find(ba[0]) != find(bb[0]):
                comp[find(ba[0])] = find(bb[0])
                merges.append(n + k)
        if len(merges) != len(S) - 1:
            return None, 'set %d: %d merges, d_w = %d' % (i, len(merges), len(S) - 1)
        res[i] = merges
    return res, None


def main():
    N, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    st = {'plain': 0, 'relative': 0}
    for _ in range(N):
        n = rng.choice((4, 5, 6))
        c = random_circuit(rng, n, rng.randrange(6, 18))
        if c is None:
            continue
        T = c.tables()
        h = T[c.h_wire]
        full = (1 << n) - 1
        for Q in ([0] + [rng.randrange(1 << n) & rng.randrange(1 << n)]):
            cube = [x for x in range(1 << n) if x & Q == Q]
            ps = [p for p in range(n) if not (Q >> p & 1) and all((h >> x & 1) == (x >> p & 1) for x in cube)]
            if not ps:
                continue
            p = ps[0]
            res, err = classes(c, Q, p)
            if err:
                print('FAIL', err, c.to_dict(), 'Q =', Q, 'p =', p)
                return 1
            allm = [g for ms in res.values() for g in ms]
            if len(allm) != len(set(allm)):
                print('FAIL disjointness', c.to_dict(), 'Q =', Q, 'p =', p)
                return 1
            F2 = f2set(c, T, Q)
            if not set(allm) <= F2:
                print('FAIL merge not in F2(Q)', c.to_dict(), 'Q =', Q, 'p =', p)
                return 1
            base = sum(len(c.sets[i]) - 1 for i in res)
            if len(F2) < base:
                print('FAIL |F2(Q)| < base', c.to_dict(), Q)
                return 1
            st['plain' if Q == 0 else 'relative'] += 1
    print('no failure:', st)
    return 0


if __name__ == '__main__':
    sys.exit(main())
