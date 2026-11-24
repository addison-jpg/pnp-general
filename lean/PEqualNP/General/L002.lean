import PEqualNP.General.Gaps

/-! L-gen-002: the fixed-degree form implies the linear case. If for every degree `k` some
language in NP has no circuits of size `c * n ^ k + c` (gap L-gen-102), then some language in NP
has no circuits of linear size (gap L-gen-103). -/

theorem PEqualNP.General.L002 : PEqualNP.General.Gap.L102 → PEqualNP.General.Gap.L103 := by
  intro h
  obtain ⟨L, hNP, hL⟩ := h 1
  exact ⟨L, hNP, fun c hc => hL c (by simpa using hc)⟩
