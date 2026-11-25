#!/usr/bin/env python3
"""A first formalized ethics: a deontic frame, checked on every relation on 1..3 worlds. Standard library only.

A deontic frame is a finite set W of worlds (situations) and a relation R on W: w R v says the agent can move
from situation w to situation v. With a valuation V (the set of worlds where p is true):
  O p (obligatory p) is true at w iff p is true at every v with w R v   (Kripke box)
  P p (permitted p)  is   not O not p, so true at w iff p is true at some v with w R v
A formula is valid on a frame if it is true at every world under every valuation of p.
Checked, by two independent counts that must agree frame by frame:
  1. frame conditions on R: serial (every world reaches some world) and symmetric (x R y implies y R x);
  2. brute force: evaluate D = O p -> P p and B = p -> O P p at every world under every valuation.
Claims: (i) D is valid exactly on the serial frames; (ii) D and B are both valid exactly on the mirror frames
(reciprocal and serial); (iii) the counts of each class. Label: checked-finite (exhaustive up to 3 worlds).
Reading (analogy, open): D is ought-implies-can, every situation has a permissible next situation; Beauvoir's
"my freedom requires the other's" is read into B (I can come back from where I let you go). Beauvoir, Pour une
morale de l'ambiguite (1947): cited from memory, not re-read here. The link is a reading, not a result.
Note: core/ontology/mirror.py's "mirror" is reciprocal and successor-serial. For a symmetric R every reached
world reaches back, so its second condition always holds and its counts (2, 8, 64) are all symmetric relations,
dead-end worlds included. The mirror here is the stricter one: reciprocal and serial.
Run: python3 -I core/ontology/ethics.py   (last line is JSON)
"""
import json, math, time


def frames(n):
    pairs = [(i, j) for i in range(n) for j in range(n)]
    for bits in range(1 << len(pairs)):
        yield {p for k, p in enumerate(pairs) if bits >> k & 1}


# 1. frame conditions
def serial(n, R): return all(any((w, v) in R for v in range(n)) for w in range(n))
def symmetric(n, R): return all((y, x) in R for x, y in R)


# 2. brute force on valuations: a formula is a function (n, R, V, w) -> bool
def O(f): return lambda n, R, V, w: all(f(n, R, V, v) for v in range(n) if (w, v) in R)
def Not(f): return lambda n, R, V, w: not f(n, R, V, w)
def P(f): return Not(O(Not(f)))
def Imp(f, g): return lambda n, R, V, w: (not f(n, R, V, w)) or g(n, R, V, w)
p = lambda n, R, V, w: w in V
D = Imp(O(p), P(p))      # ought implies may
B = Imp(p, O(P(p)))      # what holds here stays permitted from everywhere I can go

def valid(f, n, R):
    for vb in range(1 << n):
        V = {w for w in range(n) if vb >> w & 1}
        if not all(f(n, R, V, w) for w in range(n)): return False
    return True


def main():
    t0 = time.time(); total = 0
    by_cond = {"serial": {}, "symmetric": {}, "mirror": {}}
    by_force = {"D": {}, "B": {}, "D and B": {}}
    for n in (1, 2, 3):
        c = dict.fromkeys(["serial", "symmetric", "mirror", "D", "B", "D and B"], 0)
        for R in frames(n):
            total += 1
            s, y = serial(n, R), symmetric(n, R)
            d, b = valid(D, n, R), valid(B, n, R)
            assert d == s, f"(i) fails: n={n} R={sorted(R)}"
            assert b == y, f"B is not symmetry: n={n} R={sorted(R)}"
            assert (d and b) == (s and y), f"(ii) fails: n={n} R={sorted(R)}"
            c["serial"] += s; c["symmetric"] += y; c["mirror"] += s and y
            c["D"] += d; c["B"] += b; c["D and B"] += d and b
        for k in by_cond: by_cond[k][n] = c[k]
        for k in by_force: by_force[k][n] = c[k]
    # independent closed forms: serial (2^n - 1)^n; symmetric 2^(n(n+1)/2);
    # symmetric with no dead-end world, by inclusion-exclusion over the dead-end set
    closed = {"serial": {n: (2 ** n - 1) ** n for n in (1, 2, 3)},
              "symmetric": {n: 2 ** (n * (n + 1) // 2) for n in (1, 2, 3)},
              "mirror": {n: sum((-1) ** k * math.comb(n, k) * 2 ** ((n - k) * (n - k + 1) // 2) for k in range(n + 1)) for n in (1, 2, 3)}}
    assert by_cond == closed, (by_cond, closed)
    assert by_force == {"D": by_cond["serial"], "B": by_cond["symmetric"], "D and B": by_cond["mirror"]}
    assert total == 2 + 16 + 512
    print(f"(i)   D = O p -> P p is valid exactly on the serial frames: {by_cond['serial']} of 2, 16, 512")
    print(f"(ii)  D and B both valid exactly on the mirror frames (reciprocal and serial): {by_cond['mirror']}")
    print(f"      B alone is valid exactly on the symmetric frames: {by_cond['symmetric']}")
    print("(iii) counts agree three ways: frame conditions, brute force on every valuation, closed forms")
    print("PASS")
    print(json.dumps({"frames": total, "seconds": round(time.time() - t0, 3), "serial": by_cond["serial"],
                      "symmetric": by_cond["symmetric"], "mirror": by_cond["mirror"]}))


if __name__ == "__main__":
    main()
