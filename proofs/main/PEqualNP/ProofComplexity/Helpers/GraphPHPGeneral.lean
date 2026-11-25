import PEqualNP.ProofComplexity.Helpers.GraphPHPReduction

/-!
# Polynomial calculus degree for the graph pigeonhole formula, any expansion `δ ≥ 2`

Row L-pcx-046 asks for a `(s, 2)` boundary expander and `2 (D + 1) ≤ s`. The proof
(`graphPHP_no_pc_refutation`) uses only `1 ≤ s` and `D ≤ s`, and an `(s, δ)` boundary expander
with `δ ≥ 2` is an `(s, 2)` one. So: on an `(s, δ)` boundary expander with `δ ≥ 2` and `s ≥ 1`,
the pigeonhole CNF has no polynomial calculus refutation over F2 of any degree `D ≤ s`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.Expanders

/-- Boundary expansion is monotone in the factor. -/
theorem isBdryExpander_mono {m N : ℕ} {G : BipGraph m N} {s δ δ' : ℕ} (h : IsBdryExpander G s δ)
    (hδ : δ' ≤ δ) : IsBdryExpander G s δ' := fun T hT =>
  le_trans (Nat.mul_le_mul_right _ hδ) (h T hT)

/-- The general form of L-pcx-046: expansion `δ ≥ 2`, every degree `D` up to `s`. -/
theorem graphPHP_no_pc_general {m N : ℕ} (G : BipGraph m N) {s δ D : ℕ}
    (hG : IsBdryExpander G s δ) (hδ : 2 ≤ δ) (hs : 1 ≤ s) (hD : D ≤ s) :
    ¬ PEqualNP.ProofComplexity.PCRefutable
      (PEqualNP.ProofComplexity.cnfSystem (graphPHP G)) D :=
  graphPHP_no_pc_refutation G (isBdryExpander_mono hG hδ) hs hD

end PEqualNP.ProofComplexity.Helpers
