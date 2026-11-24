import PEqualNP.Defs.QuantumGravity
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
Helpers for L-qg-008 to L-qg-010: Deutsch-consistent distributions of a classical register, the
closed timelike curve search map, and the halting time of a finite-state system.
-/

namespace PEqualNP.QuantumGravity.Helpers

open PEqualNP.QuantumGravity

section Deutsch

variable {S : Type}

/-- A consistent distribution is carried to itself by every iterate. -/
theorem map_iterate_of_consistent {f : S → S} {μ : PMF S} (h : DeutschConsistent f μ) (t : ℕ) :
    μ.map (f^[t]) = μ := by
  induction t with
  | zero => exact PMF.map_id μ
  | succ t ih => rw [Function.iterate_succ, ← PMF.map_comp, h, ih]

/-- Every point a consistent distribution charges is reached after `t` steps, for every `t`. -/
theorem mem_range_iterate_of_consistent {f : S → S} {μ : PMF S} (h : DeutschConsistent f μ)
    (t : ℕ) {y : S} (hy : y ∈ μ.support) : ∃ x, f^[t] x = y := by
  rw [← map_iterate_of_consistent h t, PMF.support_map] at hy
  obtain ⟨x, -, rfl⟩ := hy
  exact ⟨x, rfl⟩

/-- On a finite set every map has a point that returns to itself. -/
theorem exists_periodic [Finite S] (f : S → S) (x : S) : ∃ y : S, ∃ q : ℕ, f^[q + 1] y = y := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => f^[i] x)
  have key : ∀ a b : ℕ, a < b → f^[a] x = f^[b] x → ∃ y : S, ∃ q : ℕ, f^[q + 1] y = y := by
    intro a b hab he
    refine ⟨f^[a] x, b - a - 1, ?_⟩
    rw [← Function.iterate_add_apply, show b - a - 1 + 1 + a = b by omega]
    exact he.symm
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h heq
  · exact key j i h heq.symm

/-- The distribution with the same mass on every point of a nonempty finite type is carried to
itself by every bijection. -/
theorem map_equiv_ofFintype_const {α : Type} [Fintype α] (c : ENNReal) (hc : ∑ _a : α, c = 1)
    (e : α ≃ α) : (PMF.ofFintype (fun _ => c) hc).map e = PMF.ofFintype (fun _ => c) hc := by
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp
  · intro a ha
    have hb : b ≠ e a := fun hb => ha (by rw [hb, Equiv.symm_apply_apply])
    simp [hb]

/-- The distribution spread evenly over the cycle `y, f y, ..., f^[q] y` is consistent when
`f^[q + 1] y = y`. -/
theorem consistent_of_periodic (f : S → S) (y : S) (q : ℕ) (hy : f^[q + 1] y = y) :
    ∃ μ : PMF S, DeutschConsistent f μ := by
  have hq : ((q + 1 : ℕ) : ENNReal) ≠ 0 := by simp
  have hsum : ∑ _a : Fin (q + 1), ((q + 1 : ℕ) : ENNReal)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel hq (ENNReal.natCast_ne_top _)
  let ν := PMF.ofFintype (fun _ : Fin (q + 1) => ((q + 1 : ℕ) : ENNReal)⁻¹) hsum
  let orbit : Fin (q + 1) → S := fun i => f^[i.val] y
  refine ⟨ν.map orbit, ?_⟩
  have hrot : f ∘ orbit = orbit ∘ finRotate (q + 1) := by
    funext i
    simp only [Function.comp_apply, orbit]
    rw [coe_finRotate]
    split_ifs with hi
    · subst hi
      rw [← Function.iterate_succ_apply' f, Fin.val_last, Function.iterate_zero_apply]
      exact hy
    · exact (Function.iterate_succ_apply' f i.val y).symm
  unfold DeutschConsistent
  rw [PMF.map_comp, hrot, ← PMF.map_comp, map_equiv_ofFintype_const]

/-- Deutsch's condition always has a solution on a nonempty finite register. -/
theorem exists_consistent [Finite S] [Nonempty S] (f : S → S) :
    ∃ μ : PMF S, DeutschConsistent f μ := by
  obtain ⟨y, q, hy⟩ := exists_periodic f (Classical.arbitrary S)
  exact consistent_of_periodic f y q hy

end Deutsch

section Search

variable {N : ℕ} {φ : ZMod N → Bool}

theorem ctcSearchMap_iterate_of_sat {y : ZMod N} (hy : φ y = true) (i : ℕ) :
    (ctcSearchMap φ)^[i] y = y := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, show ctcSearchMap φ y = y by simp [ctcSearchMap, hy], ih]

theorem ctcSearchMap_iterate_of_unsat {x : ZMod N} (i : ℕ) (h : ∀ j < i, φ (x + j) = false) :
    (ctcSearchMap φ)^[i] x = x + i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (fun j hj => h j (by omega))]
    have hi : φ (x + i) = false := h i (by omega)
    simp only [ctcSearchMap, hi]
    push_cast
    ring

/-- When some point satisfies `φ`, the register holds a point satisfying `φ` after `N` steps,
from every start. -/
theorem ctcSearchMap_iterate_sat [NeZero N] (hs : ∃ s, φ s = true) (x : ZMod N) :
    φ ((ctcSearchMap φ)^[N] x) = true := by
  classical
  obtain ⟨s, hs⟩ := hs
  have hd : φ (x + ((s - x).val : ZMod N)) = true := by
    rw [ZMod.natCast_zmod_val]
    simpa using hs
  have hex : ∃ i : ℕ, φ (x + (i : ZMod N)) = true := ⟨_, hd⟩
  have hi0 : Nat.find hex ≤ (s - x).val := Nat.find_min' hex hd
  have hlt : (s - x).val < N := ZMod.val_lt _
  have hsol : φ (x + (Nat.find hex : ZMod N)) = true := Nat.find_spec hex
  have hwalk : (ctcSearchMap φ)^[Nat.find hex] x = x + (Nat.find hex : ZMod N) :=
    ctcSearchMap_iterate_of_unsat _ (fun j hj => by simpa using Nat.find_min hex hj)
  have key : (ctcSearchMap φ)^[N - Nat.find hex + Nat.find hex] x =
      x + (Nat.find hex : ZMod N) := by
    rw [Function.iterate_add_apply, hwalk, ctcSearchMap_iterate_of_sat hsol]
  have hN : N - Nat.find hex + Nat.find hex = N := by omega
  rw [hN] at key
  rw [key]
  exact hsol

/-- When some point satisfies `φ`, every Deutsch-consistent distribution of the search map
charges only points that satisfy `φ`. -/
theorem consistent_support_sat [NeZero N] (hs : ∃ s, φ s = true) {μ : PMF (ZMod N)}
    (hμ : DeutschConsistent (ctcSearchMap φ) μ) {y : ZMod N} (hy : y ∈ μ.support) :
    φ y = true := by
  obtain ⟨x, rfl⟩ := mem_range_iterate_of_consistent hμ N hy
  exact ctcSearchMap_iterate_sat hs x

end Search

section FiniteState

/-- A system with finitely many states that ever enters `H` enters it within as many steps as
it has states. -/
theorem enters_within_card {S : Type} [Fintype S] (f : S → S) (H : Set S) (x : S)
    (hex : ∃ t, f^[t] x ∈ H) : ∃ t < Fintype.card S, f^[t] x ∈ H := by
  classical
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  by_contra hge
  push Not at hge
  have key : ∀ a b : Fin (Nat.find hex + 1), a.val < b.val → f^[a.val] x = f^[b.val] x → False := by
    intro a b hab he
    have hb : b.val ≤ Nat.find hex := Nat.lt_succ_iff.1 b.isLt
    have h1 : f^[Nat.find hex - b.val + a.val] x ∈ H := by
      rw [Function.iterate_add_apply, he, ← Function.iterate_add_apply, Nat.sub_add_cancel hb]
      exact Nat.find_spec hex
    exact Nat.find_min hex (show Nat.find hex - b.val + a.val < Nat.find hex by omega) h1
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Nat.find hex + 1) => f^[i.val] x) (by simp only [Fintype.card_fin]; omega)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact key i j h heq
  · exact key j i h heq.symm

end FiniteState

end PEqualNP.QuantumGravity.Helpers
