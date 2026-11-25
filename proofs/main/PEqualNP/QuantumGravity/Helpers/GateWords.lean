import PEqualNP.Defs.QuantumGravity
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.OrderOfElement

/-!
Helpers for L-qg-001 to L-qg-007: products of gates from a gate set (`ReachableIn`), the count
of those of at most `k` gates, and minimal gate words.
-/

namespace PEqualNP.QuantumGravity.Helpers

open PEqualNP.QuantumGravity

section Monoid

variable {G : Type} [Monoid G]

theorem one_mem_reachableIn (S : Set G) (k : ℕ) : (1 : G) ∈ ReachableIn S k :=
  ⟨[], by simp, by simp, rfl⟩

theorem reachableIn_mono {S : Set G} {k m : ℕ} (h : k ≤ m) :
    ReachableIn S k ⊆ ReachableIn S m := by
  rintro g ⟨l, hl, hS, rfl⟩
  exact ⟨l, hl.trans h, hS, rfl⟩

theorem word_mem_reachableIn {S : Set G} {l : List G} (hS : ∀ x ∈ l, x ∈ S) :
    l.prod ∈ ReachableIn S l.length :=
  ⟨l, le_rfl, hS, rfl⟩

theorem mul_mem_reachableIn {S : Set G} {k m : ℕ} {g h : G} (hg : g ∈ ReachableIn S k)
    (hh : h ∈ ReachableIn S m) : g * h ∈ ReachableIn S (k + m) := by
  obtain ⟨l, hl, hS, rfl⟩ := hg
  obtain ⟨l', hl', hS', rfl⟩ := hh
  refine ⟨l ++ l', by simp only [List.length_append]; omega, ?_, by simp⟩
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hS x hx
  · exact hS' x hx

theorem pow_mem_reachableIn {S : Set G} {k : ℕ} {g : G} (hg : g ∈ ReachableIn S k) (t : ℕ) :
    g ^ t ∈ ReachableIn S (t * k) := by
  induction t with
  | zero => simpa using one_mem_reachableIn S 0
  | succ t ih =>
    rw [pow_succ, Nat.succ_mul]
    exact mul_mem_reachableIn ih hg

/-- The products of at most `k` elements of `S`, as a finite set. -/
def ball [DecidableEq G] (S : Finset G) : ℕ → Finset G
  | 0 => {1}
  | k + 1 => ball S k ∪ (S ×ˢ ball S k).image (fun p => p.1 * p.2)

theorem card_ball_le [DecidableEq G] (S : Finset G) (k : ℕ) :
    (ball S k).card ≤ (S.card + 1) ^ k := by
  induction k with
  | zero => simp [ball]
  | succ k ih =>
    calc (ball S (k + 1)).card ≤ (ball S k).card + (S ×ˢ ball S k).card :=
          (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
      _ = (S.card + 1) * (ball S k).card := by rw [Finset.card_product]; ring
      _ ≤ (S.card + 1) * (S.card + 1) ^ k := Nat.mul_le_mul_left _ ih
      _ = (S.card + 1) ^ (k + 1) := by ring

theorem reachableIn_subset_ball [DecidableEq G] (S : Finset G) (k : ℕ) :
    ReachableIn (S : Set G) k ⊆ (ball S k : Set G) := by
  induction k with
  | zero =>
    rintro g ⟨l, hl, -, rfl⟩
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [ball]
  | succ k ih =>
    rintro g ⟨l, hl, hS, rfl⟩
    rw [Finset.mem_coe]
    cases l with
    | nil => exact Finset.mem_union_left _ (Finset.mem_coe.1 (ih (one_mem_reachableIn _ _)))
    | cons a l =>
      have ha : a ∈ S := Finset.mem_coe.1 (hS a (by simp))
      have hl' : l.prod ∈ (ball S k : Set G) :=
        ih ⟨l, by simp only [List.length_cons] at hl; omega,
          fun x hx => hS x (List.mem_cons_of_mem a hx), rfl⟩
      refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨(a, l.prod), ?_, by simp⟩)
      exact Finset.mem_product.2 ⟨ha, Finset.mem_coe.1 hl'⟩

theorem ncard_reachableIn_le (S : Finset G) (k : ℕ) :
    (ReachableIn (S : Set G) k).ncard ≤ (S.card + 1) ^ k := by
  classical
  calc (ReachableIn (S : Set G) k).ncard ≤ ((ball S k : Finset G) : Set G).ncard :=
        Set.ncard_le_ncard (reachableIn_subset_ball S k) (Finset.finite_toSet _)
    _ = (ball S k).card := Set.ncard_coe_finset _
    _ ≤ (S.card + 1) ^ k := card_ball_le S k

theorem exists_not_mem_reachableIn [Finite G] (S : Finset G) (k : ℕ)
    (h : (S.card + 1) ^ k < Nat.card G) : ∃ g, g ∉ ReachableIn (S : Set G) k := by
  by_contra hall
  push Not at hall
  have hle := ncard_reachableIn_le S k
  rw [Set.eq_univ_of_forall hall, Set.ncard_univ] at hle
  omega

/-- Every prefix of a minimal gate word is a minimal gate word. -/
theorem take_minimal {S : Set G} {l : List G} (hS : ∀ x ∈ l, x ∈ S)
    (hmin : ∀ m < l.length, l.prod ∉ ReachableIn S m) (t : ℕ) (ht : t ≤ l.length) :
    ∀ m < t, (l.take t).prod ∉ ReachableIn S m := by
  intro m hm hreach
  have hdrop : (l.drop t).prod ∈ ReachableIn S (l.length - t) :=
    ⟨l.drop t, by simp, fun x hx => hS x (List.mem_of_mem_drop hx), rfl⟩
  have hall := mul_mem_reachableIn hreach hdrop
  rw [List.prod_take_mul_prod_drop] at hall
  exact hmin (m + (l.length - t)) (by omega) hall

/-- When every element is a product of gates, every element has a minimal gate word. -/
theorem exists_minimal_word {S : Set G} (hgen : ∀ g, ∃ m, g ∈ ReachableIn S m) (g : G) :
    ∃ l : List G, (∀ x ∈ l, x ∈ S) ∧ l.prod = g ∧ ∀ m < l.length, g ∉ ReachableIn S m := by
  classical
  obtain ⟨l, hl, hS, hprod⟩ := Nat.find_spec (hgen g)
  refine ⟨l, hS, hprod, fun m hm hr => ?_⟩
  have := Nat.find_min' (hgen g) hr
  omega

end Monoid

theorem nat_card_perm_bits (n : ℕ) :
    Nat.card (Equiv.Perm (Fin n → Bool)) = (2 ^ n).factorial := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  simp

/-- A gate word longer than `k` whose prefix of length `t` has complexity exactly `t`, for
every `t`, when the gates generate every reversible map and `(|S| + 1)^k < (2^n)!`. -/
theorem exists_long_minimal_word (n : ℕ) (S : Finset (Equiv.Perm (Fin n → Bool))) (k : ℕ)
    (hgen : ∀ g, ∃ m, g ∈ ReachableIn (S : Set (Equiv.Perm (Fin n → Bool))) m)
    (h : (S.card + 1) ^ k < (2 ^ n).factorial) :
    ∃ l : List (Equiv.Perm (Fin n → Bool)), (∀ x ∈ l, x ∈ S) ∧ k < l.length ∧
      ∀ t ≤ l.length, (l.take t).prod ∈ ReachableIn (S : Set _) t ∧
        ∀ m < t, (l.take t).prod ∉ ReachableIn (S : Set _) m := by
  obtain ⟨g, hg⟩ := exists_not_mem_reachableIn S k (by rw [nat_card_perm_bits]; exact h)
  obtain ⟨l, hS, rfl, hmin⟩ := exists_minimal_word hgen g
  refine ⟨l, fun x hx => Finset.mem_coe.1 (hS x hx), ?_, fun t ht => ⟨?_, ?_⟩⟩
  · by_contra hk
    exact hg (reachableIn_mono (not_lt.1 hk) (word_mem_reachableIn hS))
  · have hS' : ∀ x ∈ l.take t, x ∈ (S : Set _) := fun x hx => hS x (List.mem_of_mem_take hx)
    simpa [List.length_take, Nat.min_eq_left ht] using word_mem_reachableIn hS'
  · exact take_minimal hS hmin t ht

end PEqualNP.QuantumGravity.Helpers
