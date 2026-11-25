#!/usr/bin/env python3
"""Condorcet's paradox by exhaustion: 3 voters, strict rankings, 3 options (6^3 = 216 profiles) and 4 options (24^3).
Pairwise majority: x beats y if more voters rank x above y. With 3 voters there are no ties.
Cycle count for 3 options is 12 of 216 = 1/18 (cited from memory; here derived twice). 4 options is derived, not remembered.
Two independent computations: (A) tournament, find a 3-cycle; (B) rank options by wins and test transitivity (win counts all distinct).
Run: python3 -I culture/social/condorcet.py   (last line is JSON)
"""
import itertools, json, time
from fractions import Fraction

def beats(profile, x, y): return sum(r.index(x) < r.index(y) for r in profile) >= 2

def count(m):
    cyc = win = total = 0
    for prof in itertools.product(list(itertools.permutations(range(m))), repeat=3):
        total += 1
        B = {(x, y): beats(prof, x, y) for x in range(m) for y in range(m) if x != y}
        a_cycle = any(B[x, y] and B[y, z] and B[z, x] for x, y, z in itertools.permutations(range(m), 3))   # A
        wins = sorted(sum(B[x, y] for y in range(m) if y != x) for x in range(m))                           # B
        b_cycle = wins != list(range(m))        # a transitive tournament has win counts 0,1,..,m-1 exactly
        assert a_cycle == b_cycle, prof
        cyc += a_cycle
        win += any(all(B[x, y] for y in range(m) if y != x) for x in range(m))
    return total, cyc, win

def main():
    t0 = time.time(); t3, c3, w3 = count(3); t4, c4, w4 = count(4)
    assert (t3, c3, w3) == (216, 12, 204) and Fraction(c3, t3) == Fraction(1, 18)
    assert t4 == 13824
    print("3 options:", t3, "profiles;", c3, "cycles (1/18);", w3, "with a Condorcet winner")
    print("4 options:", t4, "profiles;", c4, "with a cycle;", w4, "with a Condorcet winner;", t4 - w4, "without")
    print("PASS"); print(json.dumps({"states": t3 + t4, "seconds": round(time.time() - t0, 2), "cycles3": c3, "cycles4": c4, "winner4": w4}))

if __name__ == "__main__": main()
