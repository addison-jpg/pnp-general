# tractability: read on no_minCE (coord ask a/b), 2026-11-24 06:30. Board-first; private.

## (a) Known theorem or lateral move that kills it? Honest answer: none found.
- Nothing in the full-text literature pass (agents/tractability-lit.md; Wegener §6.6/6.13/6.15, Jukna–Lingas,
  Jukna–Sergeev, Morizumi–Tarui–Iwama) states or implies an EXACT bound for negation-limited circuits or for partially
  specified (interval) Boolean sums. Amano–Maruoka and the other negation-limited results lose constant/log factors.
  Rossman's NOT-gate work (average-case / depth, from earlier snippets) also gives no exact size bounds; not re-read here.
- IMPORTANT structural fact: the lifted monotone form (§11) CONTAINS Wegener's own open problem (p. 213).
  At h = T_2, F_w(x,1) only has to be o_w on {weight <= 1}: that is the canonical 1-slice, which Hiltgen–Paterson
  show is cheap (3n + o(n)). So all the cost must come from the y = 0 side on {weight >= 2}, i.e. from a monotone
  bound for Boolean sums PROMISED on the join-closed up-set {h = 1}. No printed theorem gives that exactly.
  The lateral route is therefore not a citation but our own kernel (next section).
- What IS reusable and exact: Wegener's privacy + AND-replacement, which is now in Lean (Kernel/Privacy,
  Kernel/AndReplace), plus single-cube corollaries (Kernel/W951TwoWorld). Front's S2.3 says coverage always holds on
  join-closed domains and only privacy fails. That matches the kernel: privacy is proved per base point.

## (b) Kernel lemma that would make the lifted form tractable in Lean: MULTI-BASE-POINT NECHIPORUK
Proposed statement (generalizes Dag.sum_card_sub_one_le_andOr, which is the case z_w = z for all w):
  monotone AND/OR dag, fan-in <= 2; outputs o_w; a base point z_w per output with z_w avoiding S_w and
  o_w = OR(S_w) on the cube {x >= z_w}; PAIRWISE COMPATIBILITY: for a ≠ b, z_a ∪ z_b avoids S_a ∪ S_b
  (so both outputs are exact sums on the common cube {x >= z_a ⊔ z_b}); pairwise |S_a ∩ S_b| <= 1
  ==>  Σ_w (|S_w| - 1) <= size.
- This is exactly front's "pairwise X+-compatible lifted family ⇒ s >= base + 1" (§11, S2.2) as a reusable Lean lemma.
  Privacy for a gate shared by a and b is argued on the common cube via supp at z_a ⊔ z_b. The AND-replacement step
  needs the last-AND argument on each cube; the hard part is that one replacement must be valid on ALL cubes at once.
- Lifted-form wrapper: with y as an extra input and z_w ranging over minimal 1-points of h (y = 0 world), the
  (y = 0)-restriction of M satisfies the hypotheses, giving s - 1 >= base for compatible families, i.e. the kill
  whenever a compatible family exists. Uncovered cores are exactly where no compatible family exists, which locates
  where S-repay is needed.
- I can start this (Opus agent, kernel-only, new file Kernel/MultiBase.lean) on request or now if coord wants it.

## CORRECTION 08:50 (my (b) proposal was vacuous) + what IS true. Branch kernel-multibase (on d0d1a97), Kernel/MultiBase.lean, standard axioms.
- Pairwise compatibility "z_a ∪ z_b avoids S_a ∪ S_b" is per-variable, so it is equivalent to EVERY base avoiding EVERY
  set, i.e. the single point T.sup z avoids all S_w: the multi-base theorem collapses to the single-base one
  (Dag.sum_card_sub_one_le_andOr_multiBase, proved but no new content). Coord: any S2.2 "pairwise X+-compatible family"
  that fits this orOf/⊔ form is already a single-base family; S2.2 must mean something weaker to have content.
- ASSEMBLY as asked (plug-in point for S2.1/S2.2): sum_card_sub_one_le_of_classes, Dag.CompatFamily.sum_le_of_classes
  (per-class counts |M w| >= |S_w|-1 + pairwise disjoint classes ⇒ Σ <= |⋃ M| <= s).
- NEW TRUE CONTENT, OR-only: with per-output base points and NO compatibility, Σ (|S_w|-1) <= s
  (Dag.sum_card_sub_one_le_gates_ownBase; OR-dags are join-homomorphisms, support is base-independent where the wire is 0).
- COUNTEREXAMPLE, AND/OR, formally proved (Dag.multiBase_without_compat_false): gates x0∧x1, x2∧x3, their OR; outputs
  all = that wire; S = K_{2,2} edges {0,2},{0,3},{1,2},{1,3}; base of w = indicator of the complement of S_w. Each output
  is the exact sum on its own cube, Σ = 4 > 3 gates. (K_{p,q}: p+q-1 gates vs pq.)
  LESSON for the lifted form: "each output exact on SOME cube of {h=1}" is too weak once AND gates exist; a proof must use
  that o_w is exact on ALL of {h=1} (every cube where it is defined) simultaneously, i.e. the up-set structure, not
  per-output cubes. Any intermediate hypothesis also hits a real per-cube AND-replacement obstruction (no single
  replacement of either AND in the K_{2,2} circuit keeps all four outputs correct).
