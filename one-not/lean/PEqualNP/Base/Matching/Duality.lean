import Mathlib

/-!
# LP duality for fractional covering by options: the price form

Helper module (proofs only). Circuit-free.

Every demand vertex `w` has a nonempty finite set `O w` of *options*, each option a finite set
of items. A *fractional choice* puts a probability distribution on `O w` for every `w`; its
*load* on item `a` is the total mass of the chosen options containing `a`.

* `IsFracChoice O lam`, `load O lam`: the definitions.
* `sum_inf'_le_of_frac`: weak duality. A fractional choice of load at most `1` forces
  `∑ w, min_{M ∈ O w} π(M) ≤ π(univ)` for every nonnegative price vector `π`.
* `exists_frac_iff_prices`: strong duality. Such a choice exists exactly when every nonnegative
  price vector satisfies that inequality. The hard direction separates the compact convex set
  of load vectors from the closed convex set `{y | y ≤ 1}` by
  `geometric_hahn_banach_compact_closed`.
-/

namespace PEqualNP.Base.Matching

open Finset

variable {ω α : Type*} [Fintype ω] [Fintype α] [DecidableEq α]

/-- A fractional choice: for every `w` a probability distribution supported on `O w`. -/
def IsFracChoice (O : ω → Finset (Finset α)) (lam : ω → Finset α → ℝ) : Prop :=
  (∀ w M, 0 ≤ lam w M) ∧ (∀ w M, M ∉ O w → lam w M = 0) ∧ ∀ w, ∑ M ∈ O w, lam w M = 1

/-- The load a fractional choice puts on item `a`. -/
def load (O : ω → Finset (Finset α)) (lam : ω → Finset α → ℝ) (a : α) : ℝ :=
  ∑ w, ∑ M ∈ O w, lam w M * (if a ∈ M then 1 else 0)

/-- Pricing the load: `∑ a, load a * π a = ∑ w, ∑ M ∈ O w, lam w M * π(M)`. -/
theorem sum_load_mul (O : ω → Finset (Finset α)) (lam : ω → Finset α → ℝ) (π : α → ℝ) :
    ∑ a, load O lam a * π a = ∑ w, ∑ M ∈ O w, lam w M * ∑ a ∈ M, π a := by
  simp only [load, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ M)]
  · exact Finset.sum_congr rfl fun a ha => by simp [ha]
  · intro a _ ha
    simp [ha]

/-- Weak duality: a fractional choice of load at most `1` bounds the sum of the cheapest
options by the total price. -/
theorem sum_inf'_le_of_frac {O : ω → Finset (Finset α)} (hO : ∀ w, (O w).Nonempty)
    {lam : ω → Finset α → ℝ} (hlam : IsFracChoice O lam) (hload : ∀ a, load O lam a ≤ 1)
    {π : α → ℝ} (hπ : ∀ a, 0 ≤ π a) :
    ∑ w, (O w).inf' (hO w) (fun M => ∑ a ∈ M, π a) ≤ ∑ a, π a := by
  calc ∑ w, (O w).inf' (hO w) (fun M => ∑ a ∈ M, π a)
      ≤ ∑ w, ∑ M ∈ O w, lam w M * ∑ a ∈ M, π a := by
        refine Finset.sum_le_sum fun w _ => ?_
        calc (O w).inf' (hO w) (fun M => ∑ a ∈ M, π a)
            = ∑ M ∈ O w, lam w M * (O w).inf' (hO w) (fun M => ∑ a ∈ M, π a) := by
              rw [← Finset.sum_mul, hlam.2.2 w, one_mul]
          _ ≤ _ := Finset.sum_le_sum fun M hM =>
              mul_le_mul_of_nonneg_left (Finset.inf'_le _ hM) (hlam.1 w M)
    _ = ∑ a, load O lam a * π a := (sum_load_mul O lam π).symm
    _ ≤ ∑ a, 1 * π a := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hload a) (hπ a)
    _ = ∑ a, π a := by simp

omit [Fintype α] in
theorem load_add_smul (O : ω → Finset (Finset α)) (l₁ l₂ : ω → Finset α → ℝ) (s t : ℝ) :
    load O (s • l₁ + t • l₂) = s • load O l₁ + t • load O l₂ := by
  funext a
  simp only [load, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun M _ => ?_
  ring

omit [Fintype ω] [Fintype α] [DecidableEq α] in
theorem convex_isFracChoice (O : ω → Finset (Finset α)) :
    Convex ℝ {lam | IsFracChoice O lam} := by
  intro l₁ h₁ l₂ h₂ s t hs ht hst
  refine ⟨fun w M => ?_, fun w M hM => ?_, fun w => ?_⟩
  · have := h₁.1 w M
    have := h₂.1 w M
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  · simp [h₁.2.1 w M hM, h₂.2.1 w M hM]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, h₁.2.2 w, h₂.2.2 w]
    linarith

omit [Fintype ω] [Fintype α] in
theorem isCompact_isFracChoice (O : ω → Finset (Finset α)) :
    IsCompact {lam | IsFracChoice O lam} := by
  have hcl : IsClosed {lam : ω → Finset α → ℝ | IsFracChoice O lam} := by
    simp only [IsFracChoice, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun w => isClosed_iInter fun M =>
        isClosed_le continuous_const (by fun_prop)
    · exact isClosed_iInter fun w => isClosed_iInter fun M => isClosed_iInter fun _ =>
        isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_iInter fun w => isClosed_eq (by fun_prop) continuous_const
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ω → Finset α → ℝ)) (b := 1))
    hcl fun lam h => ⟨fun w M => h.1 w M, fun w M => ?_⟩
  by_cases hM : M ∈ O w
  · rw [Pi.one_apply, Pi.one_apply, ← h.2.2 w]
    exact Finset.single_le_sum (fun N _ => h.1 w N) hM
  · rw [h.2.1 w M hM]
    exact zero_le_one

/-- **LP duality, price form.** A fractional choice of load at most `1` exists iff every
nonnegative price vector prices the cheapest options, summed over `w`, at most the total. -/
theorem exists_frac_iff_prices (O : ω → Finset (Finset α)) (hO : ∀ w, (O w).Nonempty) :
    (∃ lam : ω → Finset α → ℝ, IsFracChoice O lam ∧ ∀ a, load O lam a ≤ 1) ↔
      ∀ π : α → ℝ, (∀ a, 0 ≤ π a) →
        ∑ w, (O w).inf' (hO w) (fun M => ∑ a ∈ M, π a) ≤ ∑ a, π a := by
  constructor
  · rintro ⟨lam, hlam, hload⟩ π hπ
    exact sum_inf'_le_of_frac hO hlam hload hπ
  intro hprice
  by_contra hne
  have hne : ∀ lam : ω → Finset α → ℝ, IsFracChoice O lam → ¬ ∀ a, load O lam a ≤ 1 :=
    fun lam hlam hl => hne ⟨lam, hlam, hl⟩
  -- the two sets to separate
  set S : Set (α → ℝ) := load O '' {lam | IsFracChoice O lam} with hS
  set T : Set (α → ℝ) := {y | ∀ a, y a ≤ 1} with hT
  have hSconv : Convex ℝ S := by
    rintro _ ⟨l₁, h₁, rfl⟩ _ ⟨l₂, h₂, rfl⟩ s t hs ht hst
    exact ⟨s • l₁ + t • l₂, convex_isFracChoice O h₁ h₂ hs ht hst, load_add_smul O l₁ l₂ s t⟩
  have hScomp : IsCompact S := by
    refine (isCompact_isFracChoice O).image ?_
    unfold load
    fun_prop
  have hTconv : Convex ℝ T := by
    intro x hx y hy s t hs ht hst a
    have := hx a
    have := hy a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  have hTcl : IsClosed T := by
    simp only [hT, Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_le (by fun_prop) continuous_const
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_left]
    rintro _ ⟨lam, hlam, rfl⟩ hl
    exact hne lam hlam hl
  obtain ⟨f, u, v, hfS, huv, hfT⟩ :=
    geometric_hahn_banach_compact_closed hSconv hScomp hTconv hTcl hdisj
  -- coordinates of the separating functional
  set c : α → ℝ := fun a => f (Pi.single a 1) with hc
  have hf : ∀ y : α → ℝ, f y = ∑ a, y a * c a := by
    intro y
    have := LinearMap.pi_apply_eq_sum_univ (f : (α → ℝ) →ₗ[ℝ] ℝ) y
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    funext b
    simp [Pi.single_apply, eq_comm]
  have h1 : v < ∑ a, c a := by
    have := hfT 1 (fun a => le_rfl)
    rw [hf] at this
    simpa using this
  -- the functional is nonpositive in every coordinate, as `T` is downward closed
  have hcle : ∀ a, c a ≤ 0 := by
    intro a
    by_contra hpos
    rw [not_le] at hpos
    set r : ℝ := (∑ b, c b - v) / c a with hr
    have hr0 : 0 ≤ r := div_nonneg (by linarith) hpos.le
    have hy : (1 - r • Pi.single a 1 : α → ℝ) ∈ T := by
      intro b
      by_cases hb : b = a
      · subst hb; simp [hr0]
      · simp [hb]
    have := hfT _ hy
    rw [map_sub, map_smul, hf 1] at this
    simp only [Pi.one_apply, one_mul, smul_eq_mul] at this
    have hrc : r * c a = ∑ b, c b - v := by
      rw [hr]; field_simp
    change v < ∑ b, c b - r * c a at this
    linarith
  -- a pure choice of cheapest options
  choose m hmO hm using fun w => Finset.exists_mem_eq_inf' (hO w) (fun M => ∑ a ∈ M, -c a)
  classical
  set lam : ω → Finset α → ℝ := fun w M => if M = m w then 1 else 0 with hlamdef
  have hlam : IsFracChoice O lam := by
    refine ⟨fun w M => ?_, fun w M hM => ?_, fun w => ?_⟩
    · simp only [hlamdef]; split_ifs <;> norm_num
    · simp only [hlamdef, ite_eq_right_iff]
      rintro rfl
      exact absurd (hmO w) hM
    · simp [hlamdef, hmO w]
  have hlt := hfS _ ⟨lam, hlam, rfl⟩
  rw [hf, sum_load_mul] at hlt
  have hp := hprice (fun a => -c a) (fun a => by have := hcle a; linarith)
  have heq : ∑ w, ∑ M ∈ O w, lam w M * ∑ a ∈ M, c a
      = -∑ w, (O w).inf' (hO w) (fun M => ∑ a ∈ M, -c a) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hm w]
    simp [hlamdef, hmO w]
  rw [heq] at hlt
  have hsum : ∑ a, -c a = -∑ a, c a := Finset.sum_neg_distrib _
  linarith

end PEqualNP.Base.Matching
