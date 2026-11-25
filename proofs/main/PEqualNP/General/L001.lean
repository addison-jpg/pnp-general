import PEqualNP.General.Gaps

/-! L-gen-001: the full problem implies the fixed-degree form. If some language in NP has no
circuits of polynomial size (gap L-gen-101), then for every degree `k` some language in NP has no
circuits of size `c * n ^ k + c` (gap L-gen-102). -/

theorem PEqualNP.General.L001 : PEqualNP.General.Gap.L101 → PEqualNP.General.Gap.L102 := by
  rintro ⟨L, hNP, hL⟩ k
  refine ⟨L, hNP, fun c hc => hL ⟨Polynomial.C c * Polynomial.X ^ k + Polynomial.C c, ?_⟩⟩
  simpa using hc
