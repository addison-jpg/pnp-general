#!/usr/bin/env python3
"""Attacks on irrational and imaginary numbers: the parts that can be computed, checked exhaustively in exact arithmetic.

  1. Diagonal (Cantor): every list of n binary strings of length n misses the string that flips its diagonal.
     All lists for n <= 4 (65,536 lists at n = 4). The finite form of "the reals cannot be listed".
  2. No fraction squares to 2: no p/q with p^2 = 2 q^2 for 1 <= q <= 20,000 (every q, exact integers).
     The proof for all q is the classical parity argument (cited); this check is the finite range only.
  3. Chaos eats digits: the doubling map x -> 2x mod 1 on every dyadic rational with up to 14 binary digits.
     After k steps the first digit is digit k+1 of the start, and after all digits are used the orbit is 0.
     So a chaotic system reads out ever-finer digits of its initial condition: with finitely many digits,
     the future is fixed only for that many steps (Gisin's argument, read from his abstract only).
  4. i is a rotation: a + bi -> [[a, -b], [b, a]] is injective, adds and multiplies correctly on every
     Gaussian integer with |a|, |b| <= 6, and i maps to J with J^2 = -I. Complex numbers are real 2x2
     rotation-and-scaling matrices: nothing imaginary is needed to define them.
Readings and citations are in philosophy/NUMBERS.md. Run: python3 -I philosophy/numbers.py (last line JSON).
"""
import itertools, json, math, time
from fractions import Fraction as Fr

def main():
    t0 = time.time(); states = 0
    # 1. diagonal
    for n in range(1, 5):
        words = list(itertools.product((0, 1), repeat=n))
        for lst in itertools.product(words, repeat=n):
            states += 1
            diag = tuple(1 - lst[i][i] for i in range(n))
            assert diag not in lst, "diagonal"
    print("1. every list of n binary strings of length n misses its flipped diagonal, n = 1..4")
    # 2. no rational square root of 2
    for q in range(1, 20001):
        p2 = 2 * q * q; p = math.isqrt(p2)
        for c in (p - 1, p, p + 1):
            states += 1
            assert c * c != p2, "p^2 = 2 q^2"
    print("2. p^2 = 2 q^2 has no solution with 1 <= q <= 20000")
    # 3. doubling map on dyadic rationals
    for bits in range(1, 15):
        for m in range(1 << bits):
            x = Fr(m, 1 << bits); digits = [(m >> (bits - 1 - j)) & 1 for j in range(bits)]
            for k in range(bits):
                states += 1
                assert (x >= Fr(1, 2)) == bool(digits[k]), "first digit after k steps is digit k+1"
                x = (2 * x) % 1
            assert x == 0, "all digits used"
    print("3. doubling map: after k steps the first binary digit is digit k+1 of the start (every dyadic rational, <= 14 digits)")
    # 4. complex numbers as real matrices
    M = lambda a, b: ((a, -b), (b, a))
    mul = lambda X, Y: tuple(tuple(sum(X[i][k] * Y[k][j] for k in range(2)) for j in range(2)) for i in range(2))
    add = lambda X, Y: tuple(tuple(X[i][j] + Y[i][j] for j in range(2)) for i in range(2))
    G = [(a, b) for a in range(-6, 7) for b in range(-6, 7)]
    assert len({M(a, b) for a, b in G}) == len(G), "injective"
    for (a, b), (c, d) in itertools.product(G, repeat=2):
        states += 1
        assert add(M(a, b), M(c, d)) == M(a + c, b + d), "adds"
        assert mul(M(a, b), M(c, d)) == M(a * c - b * d, a * d + b * c), "multiplies"
    J = M(0, 1); assert mul(J, J) == M(-1, 0), "J^2 = -I"
    print("4. a + bi -> [[a,-b],[b,a]] is injective, additive and multiplicative on all |a|,|b| <= 6; i -> J, J^2 = -I")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2)}))

if __name__ == "__main__":
    main()
