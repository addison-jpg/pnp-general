import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Cleanup
import PEqualNP.Kernel.W951Core

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Generalised charging hypothesis -/

/-- THE ISOLATED HYPOTHESIS.  A family of zero sets `Q w ⊇ S w` such that the (unique) NOT gate
(and every other gate) is `Good` at the zero point `Zof (Q w)`, and the sets `D_w` of "counted
wires" (false at `Zof (Q w)`, true at two distinct `eof u`, `eof v`, `u v ∈ S w`) satisfy
`∑_w |D_w| ≤ #gates`. -/
def ChargeOK {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) : Prop :=
  ∃ Q : Fin m → Finset (Fin n), (∀ w, S w ⊆ Q w) ∧ (∀ w, Good (Q w) gates) ∧
    ∑ w, (D (Q w) (S w) gates).card ≤ gates.length

theorem val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ)
    (hj : n + gs.length ≤ j) : val gs x j = false :=
  Kernel.val_ge_viaDag gs x j hj

theorem inv_mem {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) (hgood : Good Q gs) (i : ℕ)
    (u : Fin n) (hz : val gs (Zof Q) i = false) (hu : val gs (eof u) i = true) : u ∈ Q := by
  obtain ⟨l, hinv, -⟩ := main_inv Q ∅ gs hgood
  exact (hinv i u u hz hu hu).1

theorem zero_of_sub {n m : ℕ} (S Q : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hSQ : ∀ w, S w ⊆ Q w) (w : Fin m) : val gates (Zof (Q w)) (out w) = false := by
  rw [hev, decide_eq_false_iff_not]
  rintro ⟨x, hx, hx'⟩
  simp [Zof, hSQ w hx] at hx'

theorem eof_true {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (w : Fin m) (u : Fin n) (hu : u ∈ S w) : val gates (eof u) (out w) = true := by
  rw [hev]
  simp only [decide_eq_true_eq]
  exact ⟨u, hu, by simp [eof]⟩

/-- Main conditional step: the charging hypothesis gives the bound. -/
theorem L951_core {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hc : ChargeOK S gates) : ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  classical
  obtain ⟨Q, hSQ, hgood, hsum⟩ := hc
  choose l hinv hcard using fun o => main_inv (Q o) (S o) gates (hgood o)
  have hbound : ∀ w, (S w).card - 1 ≤ (D (Q w) (S w) gates).card := by
    intro w
    have h1 : ((S w).image (l w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv w (out w) u v (zero_of_sub S Q gates out hev hSQ w)
        (eof_true S gates out hev w u hu) (eof_true S gates out hev w v hv)).2 hu hv
    have := hcard w
    omega
  calc ∑ i : Fin m, ((S i).card - 1) ≤ ∑ w, (D (Q w) (S w) gates).card :=
        Finset.sum_le_sum fun w _ => hbound w
    _ ≤ gates.length := hsum

end PEqualNP.Outside.L_meta_951_aux
