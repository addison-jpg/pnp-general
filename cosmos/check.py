"""Cosmos from the whole downward: Friedmann, orbits, and a toy of the multiverse measure problem.
Run from the repository root:  python3 -I cosmos/check.py      (exit 1 on any FAIL; prints PASS at the end)
Python standard library only (fractions, math). sympy is not used.

Algebra (the reductions the exact checks stand on).
1. Flat FLRW: H^2 = (8 pi G / 3) rho, H = a'/a, one component rho = rho0 a^(-3(1+w)).
   Try a = c t^p. Then H = p/t, so H^2 = p^2 t^-2. And rho0 a^(-3(1+w)) = rho0 c^(-3(1+w)) t^(-3p(1+w)).
   The powers of t match for every t > 0 iff 3p(1+w) = 2, i.e. p = 2/(3(1+w)), w != -1.
   Then c^(3(1+w)) = (8 pi G rho0 / 3) / p^2 fixes c. w = 0 (matter) gives p = 2/3; w = 1/3 (radiation) gives 1/2.
   w = -1 (Lambda): rho is constant, H is constant, a' = H a, a = a0 e^(Ht).
2. Deceleration q = -a a''/a'^2. For a = t^p: q = -(p - 1)/p = 1/p - 1 = 3(1+w)/2 - 1 = (1+3w)/2. For e^(Ht): q = -1.
3. Matter + Lambda, Omega_m + Omega_L = 1: H^2/H0^2 = Omega_m x^-1 + Omega_L with x = a^3 (in units a0 = 1).
   q = (Omega_m/(2x) - Omega_L) / (Omega_m/x + Omega_L), zero exactly at x = Omega_m/(2 Omega_L).
4. Kepler: mu = GM, E = v^2/2 - mu/r, h = r x v. Eccentricity vector e = ((v^2 - mu/r) r - (r.v) v)/mu.
   Its square is 1 + 2 E h^2/mu^2. So for h != 0: e^2 < 1 iff E < 0, e^2 = 1 iff E = 0. The grid check computes
   e^2 from the vector, not from this identity, so it tests the identity.
5. Measure toy. Universes are the positive integers; the property is "even".
   Ordering A is 1, 2, 3, ... Among the first N, floor(N/2) are even, so the frequency is floor(N/2)/N -> 1/2,
   since |floor(N/2)/N - 1/2| <= 1/(2N).
   Ordering B lists blocks (4k-3, 4k-1, 2k), k = 1, 2, ...: 1, 3, 2, 5, 7, 4, 9, 11, 6, ...
   It is a bijection onto the positive integers: each even 2k appears once (block k); each odd 2j-1 appears once,
   in block ceil(j/2). Among the first N there are floor(N/3) evens, so the frequency -> 1/3,
   since |floor(N/3)/N - 1/3| <= 2/(3N). Same set, same property, two limits.
"""
import json, math, os, sys
from fractions import Fraction as F
from math import factorial

fails = []; fp = []
def want(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond: fails.append(name)

# ---- 1. power-law solutions, exact: monomials c t^p as (c, p) with Fractions ----
def deriv(m): c, p = m; return (c * p, p - 1)
def mul(m1, m2): return (m1[0] * m2[0], m1[1] + m2[1])
ws = sorted({F(a, b) for a in range(-9, 31) for b in range(1, 10) if F(a, b) > -1 and F(a, b) <= 3})
ok = True
for w in ws:
    p = F(2, 3 * (1 + w)); a = (F(1), p)
    da = deriv(a)
    # H^2 a^(3(1+w)) must be a constant monomial (t-power 0): H = da/a = (p, -1)
    H = (da[0] / a[0], da[1] - a[1])
    lhs = mul(mul(H, H), (F(1), a[1] * 3 * (1 + w)))
    ok &= lhs[1] == 0 and lhs[0] == p * p
    # evaluate at rational times t = u^den(p) so t^p is rational; check H^2 * a^(3(1+w)) = p^2 exactly
    for u in (2, 3, 5, F(1, 2), F(7, 3)):
        t = F(u) ** p.denominator; at = F(u) ** p.numerator
        Ht = p / t                                     # a'/a at t, from a = t^p
        e = p.numerator * 3 * (1 + w)                  # a^(3(1+w)) = u^(num(p) 3(1+w)), an integer power
        ok &= e.denominator == 1 and Ht * Ht * F(u) ** int(e) == p * p
    # deceleration
    dda = deriv(da)
    q = -(a[0] * dda[0]) / (da[0] ** 2)                 # t-powers: p + p-2 - 2(p-1) = 0
    ok &= (a[1] + dda[1] - 2 * da[1]) == 0 and q == (1 + 3 * w) / 2
want(f"power law a = t^(2/(3(1+w))) solves flat Friedmann, and q = (1+3w)/2, for {len(ws)} rational w in (-1, 3] (checked-finite)", ok)
want("matter p = 2/3, radiation p = 1/2", F(2, 3 * (1 + 0)) == F(2, 3) and F(2, 3 * (1 + F(1, 3))) == F(1, 2))

# ---- Lambda: a = e^(Ht) as series; coefficient identity (k+1) c_{k+1} = H c_k to order 40 ----
ok = True
for H in (F(1), F(2, 3), F(-5, 7), F(13, 4)):
    c = [H ** k / factorial(k) for k in range(42)]
    ok &= all((k + 1) * c[k + 1] == H * c[k] for k in range(41))
    # q = -a a''/a'^2 = -1: series of a*a'' equals series of a'^2, coefficient by coefficient to order 40
    d1 = [(k + 1) * c[k + 1] for k in range(41)]; d2 = [(k + 1) * d1[k + 1] for k in range(40)]
    ok &= all(sum(c[i] * d2[n - i] for i in range(n + 1)) == sum(d1[i] * d1[n - i] for i in range(n + 1)) for n in range(40))
want("cosmological constant: da/dt = H a and q = -1 for a = e^(Ht), exact series to order 40, 4 rational H (checked-finite)", ok)

# ---- matter + Lambda: q sign change at a^3 = Om/(2 OL) ----
ok = True
for Om in (F(3, 10), F(315, 1000), F(1, 2), F(9, 10)):
    OL = 1 - Om; x0 = Om / (2 * OL)
    q = lambda x: (Om / (2 * x) - OL) / (Om / x + OL)
    ok &= q(x0) == 0 and all(q(x0 * F(k, 10)) > 0 for k in range(1, 10)) and all(q(x0 * F(k, 10)) < 0 for k in range(11, 40))
want("matter+Lambda: q = 0 exactly at a^3 = Om/(2 OL), q > 0 before and < 0 after on a rational grid (checked-finite on the grid)", ok)
# tested: numeric q from finite differences of a(t) = (Om/OL)^(1/3) sinh(1.5 sqrt(OL) H0 t)^(2/3)
Om, OL = 0.315, 0.685
a = lambda t: (Om / OL) ** (1 / 3) * math.sinh(1.5 * math.sqrt(OL) * t) ** (2 / 3)
def qn(t, h=1e-4): return -a(t) * (a(t + h) - 2 * a(t) + a(t - h)) / h ** 2 / ((a(t + h) - a(t - h)) / (2 * h)) ** 2
lo, hi = 0.1, 1.5
for _ in range(60):
    mid = (lo + hi) / 2; lo, hi = (mid, hi) if qn(mid) > 0 else (lo, mid)
astar = a(lo); pred = (Om / (2 * OL)) ** (1 / 3)
print(f"  q = 0 at a = {astar:.6f} (finite differences), formula {pred:.6f}")
want("matter+Lambda q sign change matches (Om/(2 OL))^(1/3) to 1e-4 (tested)", abs(astar - pred) < 1e-4)

# ---- 2. age, tested: Planck 2018 H0 = 67.4 km/s/Mpc, Om = 0.315 (search result only) ----
Mpc_km = 3.0856775814913673e19; Gyr_s = 3.15576e16
H0 = 67.4 / Mpc_km
t0 = 2 / (3 * H0 * math.sqrt(OL)) * math.asinh(math.sqrt(OL / Om)) / Gyr_s
print(f"  t0 = {t0:.3f} Gyr from the closed form; a(t0) = {a(t0 * Gyr_s * H0):.9f}")
# cross-check by direct quadrature t0 = int_0^1 da / (a H(a)), midpoint rule in s = a^(3/2)
n = 200000; s = 0.0
for i in range(n):
    u = (i + 0.5) / n; aa = u ** (2 / 3)                 # a = u^(2/3), da = (2/3) u^(-1/3) du
    s += (2 / 3) * u ** (-1 / 3) / (aa * math.sqrt(Om / aa ** 3 + OL)) / n
t0q = s / H0 / Gyr_s
print(f"  t0 = {t0q:.3f} Gyr by quadrature")
want("age closed form = quadrature to 1e-3 Gyr, a(t0) = 1, and t0 within 0.1 Gyr of 13.8 (tested)",
     abs(t0 - t0q) < 1e-3 and abs(a(t0 * Gyr_s * H0) - 1) < 1e-9 and abs(t0 - 13.8) < 0.1)

# ---- 3. orbits: e^2 < 1 iff E < 0 (h != 0), exact, mu = 1 ----
vals = [F(k, 2) for k in range(-4, 5)]
cnt = {"bound": 0, "parabolic": 0, "open": 0, "radial": 0}; ok = True
for rx in vals:
    for ry in vals:
        r2 = rx * rx + ry * ry
        if r2 == 0 or r2 not in {F(k * k, 4) for k in range(9)}: continue   # |r| rational: r on axes or a square
        r = F(math.isqrt(int(r2 * 4)), 2)
        if r * r != r2: continue
        for vx in vals:
            for vy in vals:
                v2 = vx * vx + vy * vy; E = v2 / 2 - 1 / r; h = rx * vy - ry * vx; rv = rx * vx + ry * vy
                ex = (v2 - 1 / r) * rx - rv * vx; ey = (v2 - 1 / r) * ry - rv * vy; e2 = ex * ex + ey * ey
                if h == 0: cnt["radial"] += 1; ok &= e2 == 1; continue
                ok &= (e2 < 1) == (E < 0) and (e2 == 1) == (E == 0) and e2 == 1 + 2 * E * h * h
                cnt["bound" if E < 0 else "parabolic" if E == 0 else "open"] += 1
print(f"  orbit grid: {cnt}")
want("orbits: e^2 < 1 iff E < 0 and e^2 = 1 iff E = 0, for every non-radial state on the rational grid; radial states have e^2 = 1 (checked-finite)",
     ok and cnt["bound"] > 0 and cnt["open"] > 0 and cnt["parabolic"] > 0)

# ---- 5. measure toy ----
def orderB(N):
    out, k = [], 1
    while len(out) < N: out += [4 * k - 3, 4 * k - 1, 2 * k]; k += 1
    return out[:N]
NMAX = 3000
B = orderB(NMAX)
ok = sorted(B[:3 * 500]) == sorted(set(B[:1500])) and set(range(1, 1001)) <= set(orderB(3 * 1000))
want("ordering B lists each positive integer at most once, and every integer 1..1000 within its first 3000 (checked-finite)", ok and len(set(B)) == len(B))
fa = [F(N // 2, N) for N in range(1, NMAX + 1)]
ev = 0; fb = []
for N, x in enumerate(B, 1):
    ev += x % 2 == 0; fb.append(F(ev, N))
want("frequency of even: ordering A = floor(N/2)/N, |f - 1/2| <= 1/(2N), N = 1..3000 (checked-finite)",
     all(abs(fa[N - 1] - F(1, 2)) <= F(1, 2 * N) for N in range(1, NMAX + 1)))
want("frequency of even: ordering B = floor(N/3)/N, |f - 1/3| <= 2/(3N), N = 1..3000 (checked-finite)",
     all(fb[N - 1] == F(N // 3, N) and abs(fb[N - 1] - F(1, 3)) <= F(2, 3 * N) for N in range(1, NMAX + 1)))
want("exact at the block cutoffs: A at N = 6 gives 1/2, B at N = 6 gives 1/3", fa[5] == F(1, 2) and fb[5] == F(1, 3))
posB = [B.index(2 * k) + 1 for k in range(1, 13)]
fp.append({"name": "position of universe 2k in ordering B of the measure toy, k=1..12", "seq": posB, "runner": "python3 -I cosmos/check.py"})
want("position of 2k in ordering B is 3k, k = 1..12", posB == [3 * k for k in range(1, 13)])

json.dump(fp, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "fingerprints.json"), "w"), indent=1)
print(f"cosmos: {len(fails)} failures")
if not fails: print("PASS")
sys.exit(1 if fails else 0)
