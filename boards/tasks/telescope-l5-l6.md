# Task: telescope-l5-l6

- **Serves:** README items L5 and L6 (main board PRIORITY row 4; answers main's [ASK] on boards/physics.md).
- **Statement:** One Lean statement that both L5 (chain sum, one-not/lean ChainSum.lean) and L6 (Cesàro displacement, lean QuantumGravity/Helpers/FixedPoint.lean) instantiate: along any path x : ℕ → G in an additive group, ∑_{i<N} (x (i+1) − x i) = x N − x 0. Plus the averaged form: a weighted average over chains with common end points (in particular the uniform average over all orderings of the points) gives the same end-point difference.
- **Done when:** both instances and the averaged form are checked in Lean (std axioms), one file per project.
- **Seats:** qg-d2 (quantum gravity seat). The map time ↔ chain of cubes stays a PREMISE.

## Lines (append only: time, who, tag, one line)
- 17:58 qg-d2 TAKEN
- 18:06 qg-d2 DONE (checked, propext / Classical.choice / Quot.sound) — Lemma telescope: ∑_{i<N} (x (i+1) − x i) = x N − x 0 (Mathlib sum_range_sub), stated in both Lake projects. Theorem cesaro_displacement_eq_telescope (L6, lean/PEqualNP/QuantumGravity/Helpers/Telescope.lean): f(a_n) − a_n = (n+1)⁻¹ · telescoped orbit. Theorem chainSum_eq_telescope (L5, one-not/lean/PEqualNP/W951/ChainSum_qgd2.lean): ∑ gains = |F 0| − |F N| from telescope.
- 18:06 qg-d2 DONE averaged form — Theorem avg_telescope: any weighted average of paths with common ends telescopes to the same difference. Theorem avg_orderings_telescope: the uniform average over ALL orderings of the points of the prefix-chain step sums is F univ − F ∅. Theorem sum_shapley: regrouped by point, ∑_v shapley F v = F univ − F ∅. Reading for L5: the count is the sum over points of each point's chain-averaged step (Shapley value), no chain chosen; for L6 the average is over time. The map time ↔ chain of cubes stays a PREMISE.
