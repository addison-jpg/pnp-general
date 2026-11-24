import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.GapG

/-! Matching version of the charging (weaker than Gap-G).

Gap-G asks for test systems whose counted wire sets are pairwise DISJOINT. The bound only needs
each set `w` to own `|S w| - 1` distinct counted gates: an injective assignment of "slots"
`(w, k)`, `k < |S w| - 1`, to gate wires counted by `w`'s test system. Counted sets may overlap.
By Hall's theorem this is a condition on families of sets; data: it holds with the canonical
choice (smallest Good zero set, unit test points) on every circuit tested, including all the
hard-case circuits where disjointness fails. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- MatchG: test systems for all sets and an injective assignment of slots to counted wires. -/
def MatchG {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) :
    Prop :=
  ∃ σ : ∀ w, TestSys n gates (S w) (out w),
    ∃ f : (Σ w : Fin m, Fin ((S w).card - 1)) → ℕ, Function.Injective f ∧
      ∀ x, f x ∈ (σ x.1).cnt

/-- MatchG gives the bound. -/
theorem bound_of_matchG {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (hg : MatchG S gates out) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  classical
  obtain ⟨σ, f, hinj, hmem⟩ := hg
  have hsub : ∀ x, f x ∈ Finset.Ico n (n + gates.length) := by
    intro x
    have h := hmem x
    simp only [TestSys.cnt, DT, Finset.mem_filter, mask_length] at h
    exact h.1
  have hcard : Fintype.card (Σ w : Fin m, Fin ((S w).card - 1)) ≤
      (Finset.Ico n (n + gates.length)).card := by
    rw [← Finset.card_univ, ← Finset.card_image_of_injective _ hinj]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    exact hsub x
  simpa [Fintype.card_sigma] using hcard

/-- Disjointness implies matching (Gap-G ⇒ MatchG), given Lemma G. -/
theorem matchG_of_gapG {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hg : GapG S gates out) : MatchG S gates out := by
  classical
  obtain ⟨σ, hdisj⟩ := hg
  -- each counted set has at least |S w| - 1 elements: pick an embedding of the slots
  have hemb : ∀ w, ∃ e : Fin ((S w).card - 1) → ℕ, Function.Injective e ∧
      ∀ k, e k ∈ (σ w).cnt := by
    intro w
    have hc := (σ w).card_ge (hev w)
    obtain ⟨e⟩ : Nonempty (Fin ((S w).card - 1) ↪ (σ w).cnt) := by
      apply Function.Embedding.nonempty_of_card_le
      simpa using hc
    exact ⟨fun k => (e k).1, fun a b h => e.injective (Subtype.ext h), fun k => (e k).2⟩
  choose e he hme using hemb
  refine ⟨σ, fun x => e x.1 x.2, ?_, fun x => hme x.1 x.2⟩
  rintro ⟨w1, k1⟩ ⟨w2, k2⟩ h
  simp only at h
  by_cases hw : w1 = w2
  · subst hw
    have := he w1 h
    subst this
    rfl
  · exfalso
    have h1 := hme w1 k1
    have h2 := hme w2 k2
    rw [h] at h1
    exact Finset.disjoint_left.mp (hdisj w1 w2 hw) h1 h2

end PEqualNP.Outside.L_meta_951_aux
