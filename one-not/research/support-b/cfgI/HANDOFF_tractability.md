# Config (I): exact LP price vectors for Lean (front-612 -> tractability). LP/data from Python, not Lean.
Circuit: front-match w9/fb/cfgI.json (= fc/cfgI.json), n = 9, s = 25, base = 7, sets S0 = {0,1,2,3}, S1 = {0,4,5,6}, S2 = {7,8}.
Gates: g9 = x1|x4, g10 = x2|x5, g11 = x3|x6, g12 = g9|g10, g13 = h = g12|g11 (= x1|...|x6), g14 = NOT h, g15 = h|x0,
g16 = x0|g14, g17 = g16|x4, g18 = g17|x5, g19 = g18|x6, g20 = g15&g19 = OUT S1, g21 = x7&h, g22 = g21|x8, g23 = g22|g14,
g24 = x7|h, g25 = g24|x8, g26 = g23&g25 = OUT S2, g27 = x0|g21, g28 = g27|x1, g29 = g28|x2, g30 = g16|x1, g31 = g30|x2,
g32 = g29&g31, g33 = g32|x3 = OUT S0. Downstream of the NOT: g16..g19, g23, g26, g30..g33.
M_z(w) = union-find merge gates over the wires that are 0 at z, atoms z + e_u, z any point vanishing on S_w (Lemma M).
Code: cfgI_prices.py (scipy HiGHS); full output cfgI_prices.txt.

## 1. MergeFrac (all worlds): L* = 2/3 exactly. 7 extreme optimal price vectors found (400 random re-optimisations):
  pi = 1/3 on {a, b, g33} with a in {g12, g13, g15} (monotone, NOT-free) and b in {g17, g18, g19} (N-dependent),
  all 9 combinations except (g13, g18) and (g15, g18); those two give only 1/3 (checked exactly, not by sampling).
  Not proved: that no other extreme optimal vector exists (sampling only). Each is a certificate sum_w min_z pi(M_z(w)) = 2/3 <= 1 = pi(gates).
  Lean form (finite, decidable): for pi = (1/3)[g12] + (1/3)[g18] + (1/3)[g33]:
    min_z pi(M_z(S0)) = 1/3, min_z pi(M_z(S1)) = 1/3, min_z pi(M_z(S2)) = 0 (scaled by 3: 1 + 1 + 0 = 2 <= 3).

## 2. GLOBAL PRICE CONTRADICTION (world-restricted MergeFrac). Per-set world a_w in {h(z) = 0, h(z) = 1, any}.
  27 assignments. L > 1 exactly when S0 AND S1 are both restricted to the h = 0 world: L* = 2 (for any choice for S2).
  Extreme duals there: the unit price pi = [g13] (h itself), or [g12], or [g15]: every merge set M_z(S0) and M_z(S1)
  with h(z) = 0 contains that gate, so sum_w min pi(M_z(w)) = 2 > 1 = pi(gates).
  Lean form: for every z with z ∩ S0 = ∅ and h(z) = 0: g13 ∈ M_z(S0); same for S1. (4 zero points each have h = 0.)
  Meaning: no proof may put both 4-sets in the h = 0 world. At least one of S0, S1 must be charged in the h = 1 world;
  every other assignment has L <= 1 (L = 1 exactly when exactly one of S0, S1 is forced to h = 0).

## 3. FracMatch (w951 lp.fraclp, maximal counted sets, cost = d_w cheapest): L* = 7/20. One optimal pi: uniform 1/20 on
  the 20 gates {12, 13, 15, 17, ..., 33}.
