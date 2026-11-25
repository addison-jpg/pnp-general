import PEqualNP.General.Gaps

/-! L-gen-003: the two ends of the NOT gate ladder. A bound on the number of NOT gates only
restricts the circuits (`SIZENot s t ⊆ SIZE s`), and a bound equal to the size is no restriction
(`SIZE s ⊆ SIZENot s s`). So `SIZENot s s = SIZE s`: the top of the ladder is the general case. -/

theorem PEqualNP.General.L003 :
    ∀ s t : ℕ → ℕ,
      PEqualNP.General.SIZENot s t ⊆ PEqualNP.CircuitLowerBounds.SIZE s ∧
        PEqualNP.CircuitLowerBounds.SIZE s ⊆ PEqualNP.General.SIZENot s s := by
  intro s t
  refine ⟨fun L hL n => ?_, fun L hL n => ?_⟩
  · obtain ⟨C, hb, hs, -, hd⟩ := hL n
    exact ⟨C, hb, hs, hd⟩
  · obtain ⟨C, hb, hs, hd⟩ := hL n
    exact ⟨C, hb, hs, (List.length_filter_le _ _).trans hs, hd⟩
