#!/usr/bin/env python3
"""Black-hole scaling laws, checked exactly. Standard library only.

Formulas are cited from memory (Schwarzschild 1916; Hawking 1974, 1975; Bekenstein 1973; Page 1976 for the
evaporation time). What is checked is how each law scales with the mass M. Every law is a monomial in M, so its
ratio at 2M and at M is a constant that does not depend on G, c, hbar or k_B. Those constants are set to 1 here,
and that is exact for a ratio of monomials.
  1. Schwarzschild radius r = 2 G M / c^2 scales as M^1: r(2M)/r(M) = 2.
  2. Hawking temperature T = hbar c^3 / (8 pi G M k) scales as M^-1: T(2M)/T(M) = 1/2.
  3. Bekenstein-Hawking entropy S = k A c^3 / (4 G hbar), with A = 4 pi r^2, scales as M^2: S(2M)/S(M) = 4.
  4. Evaporation time t ~ G^2 M^3 / (hbar c^4) scales as M^3: t(2M)/t(M) = 8.
  5. The exponents are typed in from the cited formulas and the ratio check only confirms them. The check is a
     consistency test of the stated scaling, not a derivation of the formulas.
Open (not checked here): whether information survives evaporation (the information paradox).
Run: python3 -I physics/blackhole/check.py   (last line is JSON)
"""
import json, time
from fractions import Fraction as Fr

def r(M): return 2 * M                       # 2 G M / c^2 with G = c = 1
def T(M): return Fr(1, 8) / M                 # hbar c^3 / (8 pi G M k) with hbar = c = G = k = 1, pi cancelled
def A(M): return 4 * r(M) ** 2                # horizon area, 4 pi r^2 with the pi cancelled into the coefficient
def S(M): return Fr(1, 4) * A(M)              # k A c^3 / (4 G hbar)
def t(M): return M ** 3                        # G^2 M^3 / (hbar c^4), coefficient set to 1

def exponent(f, M=Fr(7)):
    ratio = f(2 * M) / f(M)
    for k in range(-10, 11):           # exact search: the ratio must equal 2 ** k for some integer k
        if ratio == Fr(2) ** k: return k
    raise AssertionError(f"ratio {ratio} is not a power of 2")

def main():
    t0 = time.time(); results = {}
    for name, f, want in (("radius", r, 1), ("temperature", T, -1), ("entropy", S, 2), ("evaporation", t, 3)):
        e = exponent(f)
        assert e == want, f"{name}: exponent {e}, expected {want}"
        results[name] = e
    # the scaling must hold at other masses too (monomials: the ratio does not depend on M)
    for M in (Fr(1), Fr(3), Fr(11, 2)):
        assert r(2 * M) / r(M) == 2 and T(2 * M) / T(M) == Fr(1, 2) and S(2 * M) / S(M) == 4 and t(2 * M) / t(M) == 8
    print("exponents recovered exactly from the ratios:", results)
    print("open: whether information survives evaporation (not checked here)")
    print("PASS")
    print(json.dumps({"checks": 4, "seconds": round(time.time() - t0, 4), "exponents": results}))

if __name__ == "__main__":
    main()
