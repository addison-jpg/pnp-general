#!/usr/bin/env python3
"""Art at the base: the exact facts under music, and the web they join. Exact integers only.
  1. Circle of fifths: a step s walks through all 12 pitch classes (Z/12) exactly when gcd(s, 12) = 1;
     the generating steps are 1, 5, 7, 11 (the semitone, the fourth, the fifth, the major seventh).
     The same Z/12 as culture/zodiac.
  2. The Pythagorean comma: 12 pure fifths never equal 7 octaves, because 3^12 != 2^19 (531441 vs 524288);
     no number of pure fifths k = 1..1000 ever lands exactly on octaves (3^k is odd, 2^m is even).
  3. Equal temperament needs an irrational: no fraction p/q with q <= 2000 has (p/q)^12 = 2, and none can,
     because 2 is not the 12th power of a rational (exact: the integer 12th-root check on numerators and
     denominators). The ties: philosophy/numbers.py (irrationals) and culture/zodiac (Z/12).
  4. The interdependent web: a web of works is joined (no work alone) exactly in the household sense of
     culture/love/family.py; the count of joined webs on 1..6 works is the same 0, 1, 4, 41, 768, 27449.
Readings (Benjamin, Eco, Sontag, Munoz, Lessig; Leonardo, Van Gogh, the Indigo Girls; the Unitarian web) are
in culture/art/ART.md and are analogy. Run: python3 -I culture/art/art.py
"""
import itertools, json, math, time
from fractions import Fraction as Fr

def main():
    t0 = time.time(); states = 0
    gens = [s for s in range(12) if len({(s * i) % 12 for i in range(12)}) == 12]
    assert gens == [s for s in range(12) if math.gcd(s, 12) == 1] == [1, 5, 7, 11]
    states += 12
    print("1. steps that walk all 12 pitch classes:", gens)
    assert 3 ** 12 == 531441 and 2 ** 19 == 524288 and 3 ** 12 != 2 ** 19
    for k in range(1, 1001):
        states += 1
        assert 3 ** k % 2 == 1          # odd, so never a power of 2: no stack of pure fifths closes on octaves
    print("2. Pythagorean comma 531441/524288 =", Fr(3 ** 12, 2 ** 19), "; no stack of 1..1000 pure fifths lands on octaves")
    def r12(x):   # exact integer 12th root or None
        r = round(x ** (1 / 12)) if x > 0 else 0
        for c in (r - 1, r, r + 1):
            if c >= 0 and c ** 12 == x: return c
        return None
    for q in range(1, 2001):
        states += 1
        assert r12(2 * q ** 12) is None   # p^12 = 2 q^12 has no integer p
    print("3. no p/q with q <= 2000 has (p/q)^12 = 2: equal temperament's semitone 2^(1/12) is irrational")
    joined = []
    for n in range(1, 7):
        pairs = list(itertools.combinations(range(n), 2)); c = 0
        for mask in range(1 << len(pairs)):
            states += 1; seen = set()
            for i, (a, b) in enumerate(pairs):
                if mask >> i & 1: seen.add(a); seen.add(b)
            c += len(seen) == n
        joined.append(c)
    assert joined == [0, 1, 4, 41, 768, 27449]
    print("4. webs of 1..6 works with no work alone:", joined, "(the household count of culture/love/family.py)")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2), "generators": gens, "comma": [531441, 524288], "joined": joined}))

if __name__ == "__main__":
    main()
