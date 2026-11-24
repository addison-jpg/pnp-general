# hplus_fable.md — general surcharge theorems for L-meta-951 (restart-safe log). Code: w9/hplus/
Tags: PROVED (paper, by me) / CHECKED (code) / CONJECTURE / REFUTED.  Notation: d_a = |S_a|-1, base = Σ d_a, sigma = base - s,
Λ(F) := Σ_a (|S_a|-3)^+  (= Σ_a (d_a - min(d_a,2))),  e_u unit vector, z_S = 1 off S, 0 on S.

## 1. CLASS-COUNT SURCHARGE (Theorem X-count). PROVED (elementary; uses Proof A / T3 of PROVED_951.md 3.1-3.2).
For ANY correct one-NOT circuit (no minimality) put, over all gates g (N included),
  L_a = {g <= o_a everywhere, g(e_u)=1 for >= 2 u in S_a},   U_a = {g >= o_a everywhere, g(z_{S_a}) = 0},   P_a = L_a ∪ U_a.
 (i) the P_a are pairwise disjoint; (ii) |P_a| >= min(d_a,2).  [Proof A; re-derived by me line by line.]
Hence, with OUT := gates in no P_a,   s >= Σ_a min(d_a,2) + |OUT| = base - Λ(F) + |OUT|.            (XC)
Gates that are ALWAYS in OUT:
 (o1) N, provided N is not ≡ 0 and there are >= 2 hard sets (h(z_S)=1) [N in L_a => N(0)=0 => h ≡ 1; N in U_a => h∧o_a ≡ 0 => every
      b != a is easy since z_{S_b} hits S_a].  In a MinCE (hz, hhard): ALWAYS.
 (o2) the reader r_v of a single-reader point v of degree >= 2 (any type): OR-type r = x_v|c has c <= OR(S\v) for all S∋v (AL), so
      r(e_u) = 0 for u != v (two sets through v share only v): one unit, and not >= any o_a. AND-type r <= x_v.
 (o3) for OR-type r_v also c_v (c_v(e_u) = 0 for all u, c_v a gate != r_v).
 (o4) every AND-reader x_u&y of a variable; every gate <= x_u; every gate q = x_u | p with p = x_w|x_w' a pair-gate, u not in {w,w'}
      [q <= o_a needs {u,w,w'} ⊆ S_a, impossible as {w,w'} is a set; q >= o_a with q(z_{S_a}) = 0 needs S_a ⊆ {u,w,w'} and
       S_a = {w,w'} fails at z (x_u = 1)... S_a = {u,w}: z_{S_a} has x_w' = 1, q = 1]; every x_u|x_s with u,s in no common set.
COROLLARY 1 (N-count, in a MinCE):  sigma + 1 <= Λ(F).  So 951 holds for EVERY system with Λ(F) <= 1
 (all sets of size <= 3 except at most one set of size 4).
COROLLARY 2 (H+ with defect Λ): s >= base - Λ(F) + κ + [some single-reader point of degree >= 2 has an OR-reader] (+1 for N as in o1),
 κ = #single-reader points of degree >= 2.   In a MinCE scenario (sigma, B), V1 = points off B:
      sigma + 1 + |V1| + [some v in V1 has l(v) = sigma+1 (p-tight => OR-type, (T2))]  <=  Λ(F).           (rule 'X')
COROLLARY 3 (restricted form = the missing death): for every restriction rho (x_Z := 0, x_O := 1) of a MinCE,
      dead(rho) <= loss(rho) - sigma - |OUT(C|rho)| + Λ(F|rho);
 if F|rho has all sets of size <= 3 (e.g. rho touches every set of size >= 4):  dead(rho) + |OUT(C|rho)| <= loss(rho) - sigma.
 With Theorem E (p_fable P1; easy sets have |L_a| >= d_a) Λ may be replaced by Λ_hard = Σ over HARD sets only.
