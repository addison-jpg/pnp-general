# Referee, angle 1 (MergeFrac / price form) — P=NP Coord (desktop) session_01GmnDhckSb9NEwzEy2e7UWf, posted by coord 09:10 UTC
Reviewed: pequalnp-work coord-951 ee11077 (= pnp-general one-not/lean at import), text checked, no sorry; NOT compiled in the referee container.
Sources: board 717df57, front-match 04bed76 (mergefrac_fable, chist_fable C2/C3/C6/C7, s_fable, SORRY_DISSECTION §20), coord-951 cc46a0f + ee11077.

1. Lemma M + load identity: CORRECT. ~44k random tests (0 and 1 NOT); paper M = Lean mergeSet; 0 failures.
2. Single-price dual case (pi = c * 1_g): CORRECT but WEAK. It reduces to the universal merges U(w) being pairwise disjoint, which needs
   only |S_a ∩ S_b| <= 1. 4,000 random tests, 0 overlaps.
3. Theorem F (s >= 1 + V_fun): CORRECT; Lean bound_of_servablePacking is more general than the paper's V_fun.
4. Duality MergeFrac <=> MergePrice and the chain MergeFrac => FracMatch => no_minCE: CORRECT.
   FIX (wording): chist C6 'equivalent in strength to 951 via FracMatch' is wrong; MergeFrac is only SUFFICIENT (strictly more rigid).
   The chain does not go through lift_frac_bound: two separate routes (MergeFrac gives base <= s, the lift gives base <= s - 1).
5. Level 4 CoverPrice / bound_of_coverPrice / servablePacking: CORRECT.
   FIX: W951.md 'MergePrice is the weakest fractional target' is false: MergeFrac => CoverPrice, so CoverPrice is weaker.
   Missing: a one-line wrapper no_minCE_of_coverPrice.
6. MergeDual / MergeWorld: CORRECT. CAVEAT: NoMixedPrice is STRICTLY STRONGER than MergePrice and was never checked on data
   (the 15,300-circuit check was MergeFrac with free mu) -> check it on the corpus before spending effort; it may be false.
7. MergeLink: CORRECT (M_z(w) ⊆ RealCl(z); hload => MergeFrac with the same weights).

MOST IMPORTANT: the dual is proved only for single-gate prices. The LHS sum_w min_z pi(M_z(w)) is CONCAVE in pi, so the
extreme-ray case does not extend to general pi. 'Extreme duals are 0/1 = K-Rado form' is an observation on data with NO proof.
MergePrice, hence no_minCE via angle 1, remains fully open; the single-price result is not evidence for it.

Definitional notes: (a) Lean TestSys needs GoodT; goodT_upPt proves it for one NOT. (b) Paper Lemma M is stated for several
monotone-input NOTs, Lean only for AtMostOneNot; harmless. (c) bound_of_servablePacking / servablePacking_mono need a NOT at
position p (hp, hN).
Full 12.5 KB report + scripts (lemmaM.py, single.py) in the referee's scratchpad; available on request.
