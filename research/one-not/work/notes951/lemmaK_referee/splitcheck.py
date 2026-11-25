"""Referee check of gAdyD's item 3 (board agents/qg-d2-nomixed.md): with the worlds of MergeWorld.lean
(world 0: h(z) = 1; world 1: h(z + e_u) = 0 for every u in S; mixed: neither), a set S has only mixed zero points
iff h(e_u) = 1 for some u in S and h(1_{V \\ S}) = 0. Random one-NOT circuits, outputs a random linear family
(kcheck.random_circuit). Run from the research/one-not/ directory (or the repository root of pequalnp-work):
    python3 work/notes951/lemmaK_referee/splitcheck.py N SEED
"""
import random
import sys

sys.path.insert(0, 'tools')
sys.path.insert(0, 'work/notes951/lemmaK_referee')
from kcheck import random_circuit  # noqa: E402


def main():
    N, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    sets = split = 0
    for _ in range(N):
        n = rng.choice((3, 4, 5, 6))
        c = random_circuit(rng, n, rng.randrange(4, 16))
        if c is None:
            continue
        h = c.table(c.h_wire)
        for S in c.sets:
            mask = sum(1 << u for u in S)
            zeros = [z for z in range(1 << n) if z & mask == 0]
            w0 = [h >> z & 1 for z in zeros]
            w1 = [all(not (h >> (z | 1 << u) & 1) for u in S) for z in zeros]
            only_mixed = all(not a and not b for a, b in zip(w0, w1))
            rhs = any(h >> (1 << u) & 1 for u in S) and not (h >> (((1 << n) - 1) & ~mask) & 1)
            sets += 1
            split += only_mixed
            if only_mixed != rhs:
                print('COUNTEREXAMPLE', c.to_dict(), S)
                return 1
    print('item 3: no failure on %d sets (%d split)' % (sets, split))
    return 0


if __name__ == '__main__':
    sys.exit(main())
