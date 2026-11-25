#!/usr/bin/env python3
"""Sex as several traits: counting with two values each, then the cube [0,1]^k. Exhaustive, small.

Fausto-Sterling, Sexing the Body (2000, cited from memory), describes sex as several traits (for example
chromosomes, gonads, hormones, external anatomy, secondary characteristics). Here each trait is simplified to
two values for counting only. This is a toy count, not biology: real traits are not two-valued, and the model
says nothing about any person.
Part 1 (checked-finite, k = 1..6): of the 2^k combinations, 2 are "aligned" (all traits 0 or all 1). The rest are
2^k - 2. A single trait used as the classifier labels differently from another single trait on 2^(k-1) combinations
(exactly half), and some single trait disagrees with trait 0 on 2^k - 2 combinations (every non-aligned one).
Part 2 (FIELDS.md move: extend to the continuous, agree at the corners, re-check): each trait in [0,1].
The binary is the two corners. On the grid of multiples of 1/4 (k <= 4, 5^k points; checked-finite on that grid,
not on all of R) every threshold classifier "x_i >= t" is compared with every threshold classifier on another
coordinate: none reproduces the other, for every pair and every pair of thresholds that gives a non-constant rule.
The same for the mean of the traits as a classifier against each single trait. At the corners (thresholds 1/2)
the extension agrees with the two-valued count (asserted). What survives: "the traits can disagree" survives.
What does not: a single threshold standing in for the rest.
Published disagreement on prevalence of intersex variation, stated without choosing: Fausto-Sterling et al. 2000
(about 1.7% under a broad definition) and Sax 2002 (about 0.018% under a narrow one), both cited from memory.
The gap is mostly a question of which variations count, not of arithmetic. Nothing here settles it.
Run: python3 -I culture/queer/traits.py   (last line is JSON)
"""
import itertools, json, time
from fractions import Fraction as F

def main():
    t0 = time.time(); states = 0; rows = []
    for k in range(1, 7):
        combos = list(itertools.product((0, 1), repeat=k)); states += len(combos)
        aligned = [c for c in combos if len(set(c)) == 1]
        assert len(combos) == 2 ** k and len(aligned) == 2
        rest = len(combos) - len(aligned); assert rest == 2 ** k - 2
        pair = None
        if k >= 2:
            pairs = [sum(c[i] != c[j] for c in combos) for i in range(k) for j in range(i + 1, k)]
            assert set(pairs) == {2 ** (k - 1)}; pair = pairs[0]
            assert sum(any(c[0] != c[j] for j in range(1, k)) for c in combos) == 2 ** k - 2
        rows.append((k, len(combos), 2, rest, pair))
        print(f"k={k}: combinations={len(combos)} aligned=2 not aligned={rest} | one trait vs another labels differently on {pair if pair is not None else 'n/a (one trait)'}")
    grid = [F(i, 4) for i in range(5)]; cuts = grid + [F(5, 4)]; out = {}
    for k in range(2, 5):
        pts = list(itertools.product(grid, repeat=k)); states += len(pts)
        corners = [p for p in pts if all(x in (0, 1) for x in p)]; assert len(corners) == 2 ** k
        interior = len(pts) - len(corners)
        # threshold classifiers on the grid, as sets of points; a cut above 1 or at 0 is constant
        def cls(i, t): return frozenset(p for p in pts if p[i] >= t)
        allp = frozenset(pts); tested = 0
        for i in range(k):
            for j in range(k):
                if i == j: continue
                for s in cuts:
                    cj = cls(j, s)
                    for t in cuts:
                        ci = cls(i, t); tested += 1
                        if ci == cj: assert ci in (frozenset(), allp), "a non-constant threshold reproduced another trait"
        # the mean of traits as a classifier: mean >= m, against each single threshold
        for m in (F(i, 8) for i in range(1, 8)):
            cm = frozenset(p for p in pts if sum(p) >= m * k)
            if cm in (frozenset(), allp): continue
            for i in range(k):
                for t in cuts:
                    tested += 1; assert cm != cls(i, t), "mean reproduced a single trait"
        # corners: at threshold 1/2 the classifier is the two-valued trait
        for c in corners:
            assert all((c[i] >= F(1, 2)) == bool(c[i]) for i in range(k))
        out[k] = {"grid_points": len(pts), "corners": len(corners), "interior": interior, "pairs_tested": tested}
        print(f"k={k}: grid points={len(pts)} corners={len(corners)} between the corners={interior} | threshold comparisons={tested}, none reproduces another trait")
    print("prevalence of intersex variation, not chosen between: about 1.7% (Fausto-Sterling et al. 2000, broad) vs about 0.018% (Sax 2002, narrow); cited from memory")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2),
                      "combos": [r[1] for r in rows], "not_aligned": [r[3] for r in rows],
                      "differ": [r[4] for r in rows if r[4] is not None],
                      "grid": {str(k): out[k]["grid_points"] for k in out}, "tested": {str(k): out[k]["pairs_tested"] for k in out}}))

if __name__ == "__main__":
    main()
