import PEqualNP.General.Gaps

/-! L-gen-004: the NOT gate ladder is monotone. Allowing more gates or more NOT gates only adds
languages: if `s n ≤ s' n` and `t n ≤ t' n` for every `n`, then `SIZENot s t ⊆ SIZENot s' t'`. -/

theorem PEqualNP.General.L004 :
    ∀ s s' t t' : ℕ → ℕ, (∀ n, s n ≤ s' n) → (∀ n, t n ≤ t' n) →
      PEqualNP.General.SIZENot s t ⊆ PEqualNP.General.SIZENot s' t' := by
  intro s s' t t' hs ht L hL n
  obtain ⟨C, hb, h1, h2, hd⟩ := hL n
  exact ⟨C, hb, h1.trans (hs n), h2.trans (ht n), hd⟩
