# Referee of one-not/PROOF_PLAN_SUGGESTIONS.md §2–§4 — P=NP Coord (desktop), posted by coord 10:30 UTC (from coord's summary; referee cannot read pnp-general)
Conventions: C_1 = NOT := 1, C_0 = NOT := 0, C_0 <= real <= C_1 (monotone), top_w = indicator of the complement of S_w.
- W1 DISJOINTNESS: CORRECT, with fewer hypotheses: C_1(g)(e_u) = 1 => C_1(g) >= x_u; g in K_1(w) gives u1 != u2 in S_w (C_1(g)(top_w) = 0);
  g also in K_1(w') puts u1, u2 in S_w' => |S_w ∩ S_w'| >= 2. Uses only monotonicity of C_1 and |S_a ∩ S_b| <= 1 ('h(top_w) = 0 / no heavy point' not needed).
- W1 SIZE |K_1(w)| >= d_w: GAP. Lemma M in C_1 at z = top_w gives d_w OR gates with C_1(g)(top_w) = 0 and C_1(g)(top_w + e_u) = 1 for >= 2 u;
  K_1 needs C_1(g)(e_u) = 1 at a SMALLER point (monotonicity goes the wrong way). Shape: g = x_u ∧ x_v, v ∉ S_w. Fix: define K_1 at top_w + e_u
  (breaks the disjointness proof) or prove a bridge: under 'no heavy point' every Lemma-M merge gate of C_1 at top_w has C_1(g)(e_u) = 1 for >= 2 u.
- W0: cannot fully assess; if it is 'classes of distinct (w, minterm) are disjoint unless the minterms cross' it looks like LiftCount S2.2
  (blockP / liftCl_disjoint, Lean); check hypotheses match.
- X: NOT-dependence right if K_0 forces C_0(g) != C_1(g) somewhere (state it); the bounds C_1(g) <= o_w and C_0(g) <= o_w ∧ o_w' are NOT automatic
  (cone membership does not give <= o_w unless all paths go through ORs) — needs justification.
- P1 (forward-only re-picks along a fixed option order from the canonical start): SOUND SHAPE (trivial termination) but STRONGER than LAugmentK;
  the canonical start alone fails on 10,083 circuits; must be data-checked (scaffold K2).
- P2 (acyclic forcing by gate position): FAILS with gate-index order on scaffold's fixh16_clean#20 (forcing path {02}-{12}-{23}-{13} through
  gates 5, 13, 8, not monotone); needs another order (depth, cone inclusion), check on that circuit first.

## Addendum 10:35 (coord, checked step by step; the referee may contest)
- W1 SIZE GAP: RESOLVED. The board integrator's GM (pnp-general 4d2750d, PROOF_PLAN_SUGGESTIONS §2) is correct: invariant "B of a processed wire of V lies in one block"; inputs by (2); OR in V has both inputs in V; AND in V has one input in V with B(g) ⊆ B(that input); so each gate merges at most two blocks and the run makes exactly |S| - 1 merges, at OR gates. No order between Z and the atoms is needed. W1 is GM in C_1 with Z = top_w, p_u = e_u (both in D). The objection (atoms top_w + e_u) applied to the plain Lemma M, not to GM.
- GM IS ALREADY IN LEAN: `LiftCount.lift_merges_pt` (one zero point z, atoms a, hL = condition (2), MonoList), also `TestSys.hT` in GapG.lean; neither requires p_u ≥ z. W0 = `lift_merges_pt` in C_0 + `liftCl_disjoint` / `liftClOr_disjoint` (S2.2). X bounds: justified in the file; Lean via `Kernel/W951Extra.listVal_le` (C_0 ≤ C_1 wirewise, NOT := 0 vs 1).
- d (Lean W1, X; W0 as a corollary of S2.2) may start.
- 10:39 desktop Coord: addendum CONFIRMED; W1 CORRECT in full (paper). Drop 'no heavy point' from W1: only h(top_w) = 0 is used (C_1 ≥ real wirewise gives C_1(o_w)(e_u) = 1).
