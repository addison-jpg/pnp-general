import PEqualNP.Defs
import PEqualNP.Gct.Helpers.PermHessian
import PEqualNP.Gct.Helpers.OrderConditions

/-! General-size version of `BlockIsotropic`. If `W` is a linear space of `n × n` complex
matrices (`n ≥ 2`) with `perm (J + t) = n!` for all `t ∈ W`, then `W` is totally isotropic for the
form `B (t, u) = ∑ over (i, j), (k, l) with i ≠ k, j ≠ l of t (i, j) u (k, l)`, which is the
Hessian of the permanent at `J` divided by `(n - 2)!`. The form has the operator
`t ↦ S - R_i - C_j + t_ij`, which is injective for `n ≥ 2`, so `2 * dim W ≤ n ^ 2`. -/

namespace PEqualNP.Gct.PermIsotropicGeneral

open Finset MvPolynomial PEqualNP.Gct.Helpers

variable {n : ℕ}

/-- Operator of the form: sum of entries in a different row and a different column. -/
noncomputable def M (n : ℕ) : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ) where
  toFun t := fun p => ∑ b, if p.1 ≠ b.1 ∧ p.2 ≠ b.2 then t b else 0
  map_add' t u := by
    ext p
    simp only [Pi.add_apply, ← sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  map_smul' c t := by
    ext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> simp

theorem M_apply (t : Fin n × Fin n → ℂ) (p : Fin n × Fin n) :
    M n t p = ∑ b, if p.1 ≠ b.1 ∧ p.2 ≠ b.2 then t b else 0 := rfl

theorem M_formula (t : Fin n × Fin n → ℂ) (p : Fin n × Fin n) :
    M n t p = (∑ q, t q) - (∑ l, t (p.1, l)) - (∑ k, t (k, p.2)) + t p := by
  have key : ∀ b : Fin n × Fin n, (if p.1 ≠ b.1 ∧ p.2 ≠ b.2 then t b else 0) =
      t b - (if b.1 = p.1 then t b else 0) - (if b.2 = p.2 then t b else 0)
        + (if b = p then t b else 0) := by
    intro b
    obtain ⟨b1, b2⟩ := b
    obtain ⟨p1, p2⟩ := p
    by_cases h1 : b1 = p1 <;> by_cases h2 : b2 = p2 <;> simp [h1, h2, Ne.symm, eq_comm]
  rw [M_apply, sum_congr rfl fun b _ => key b, sum_add_distrib, sum_sub_distrib, sum_sub_distrib]
  congr 1
  congr 1
  congr 1
  · rw [Fintype.sum_prod_type, sum_eq_single p.1 (by intro x _ hx; simp [hx]) (by simp)]
    simp
  · rw [Fintype.sum_prod_type, sum_comm, sum_eq_single p.2 (by intro x _ hx; simp [hx]) (by simp)]
    simp
  · simp

theorem M_injective (hn : 2 ≤ n) : Function.Injective (M n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  have h : ∀ i j, (∑ q, t q) - (∑ l, t (i, l)) - (∑ k, t (k, j)) + t (i, j) = 0 := fun i j => by
    have := congrFun ht (i, j)
    rw [M_formula] at this
    simpa using this
  have hn' : ((n : ℂ) - 1) ≠ 0 := by
    intro h0
    have : (n : ℂ) = 1 := by linear_combination h0
    have h1 : n = 1 := by exact_mod_cast this
    omega
  set S := ∑ q, t q with hS
  have hR : ∀ i, ∑ l, t (i, l) = S := fun i => by
    have e := sum_congr rfl fun j (_ : j ∈ (univ : Finset (Fin n))) => h i j
    simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul] at e
    have e2 : ∑ j, ∑ k, t (k, j) = S := by
      rw [hS, Fintype.sum_prod_type, sum_comm]
    rw [e2] at e
    have : ((n : ℂ) - 1) * (S - ∑ l, t (i, l)) = 0 := by linear_combination e
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hn'
    · linear_combination -h0
  have hC : ∀ j, ∑ k, t (k, j) = S := fun j => by
    have e := sum_congr rfl fun i (_ : i ∈ (univ : Finset (Fin n))) => h i j
    simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul] at e
    have e2 : ∑ i, ∑ l, t (i, l) = S := by
      rw [hS, Fintype.sum_prod_type]
    rw [e2] at e
    have : ((n : ℂ) - 1) * (S - ∑ k, t (k, j)) = 0 := by linear_combination e
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hn'
    · linear_combination -h0
  have hS0 : S = 0 := by
    have e : ∑ i, ∑ l, t (i, l) = S := by rw [hS, Fintype.sum_prod_type]
    simp only [hR, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at e
    have : ((n : ℂ) - 1) * S = 0 := by linear_combination e
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hn'
    · exact h0
  ext ⟨i, j⟩
  have := h i j
  rw [hR, hC, hS0] at this
  simpa using this

/-- The Hessian of the permanent at the all ones matrix. -/
theorem hess_at_one (m : ℕ) (a b : Fin (m + 2) × Fin (m + 2)) :
    eval (fun _ => (1 : ℂ)) (pderiv a (pderiv b (PEqualNP.Gct.permPoly ℂ (m + 2)))) =
      if a.1 ≠ b.1 ∧ a.2 ≠ b.2 then (m.factorial : ℂ) else 0 := by
  have step : ∀ σ : Equiv.Perm (Fin (m + 2)),
      eval (fun _ => (1 : ℂ)) (pderiv a (pderiv b
        (∏ i : Fin (m + 2), (X (σ i, i) : MvPolynomial (Fin (m + 2) × Fin (m + 2)) ℂ)))) =
      if σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 then 1 else 0 := by
    intro σ
    rw [pderiv_perm_mon]
    by_cases hb : σ b.2 = b.1
    · rw [if_pos ⟨mem_univ _, hb⟩, pderiv_perm_mon]
      by_cases ha : a.2 ≠ b.2 ∧ σ a.2 = a.1
      · rw [if_pos ⟨mem_erase.mpr ⟨ha.1, mem_univ _⟩, ha.2⟩, if_pos ⟨hb, ha⟩]
        simp
      · rw [if_neg, map_zero, if_neg]
        · rintro ⟨_, h1, h2⟩; exact ha ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ha ⟨(mem_erase.mp h1).1, h2⟩
    · rw [if_neg (fun h => hb h.2), map_zero, map_zero, if_neg (fun h => hb h.1)]
  simp only [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, map_sum]
  rw [sum_congr rfl fun σ _ => step σ, sum_boole]
  by_cases hc : a.1 ≠ b.1 ∧ a.2 ≠ b.2
  · rw [if_pos hc, card_two a b hc.2 hc.1]
  · rw [if_neg hc]
    have : (univ.filter fun σ : Equiv.Perm (Fin (m + 2)) =>
        σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1) = ∅ := by
      refine filter_eq_empty_iff.2 fun σ _ h => hc ⟨fun h1 => ?_, h.2.1⟩
      have : σ b.2 = σ a.2 := by rw [h.1, h.2.2, h1]
      exact h.2.1 (σ.injective this).symm
    rw [this]; simp

/-- Vanishing of the quadratic form on `W`. -/
theorem quad_zero (m : ℕ) (W : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ))
    (h : ∀ t ∈ W, eval ((fun _ => (1 : ℂ)) + t) (PEqualNP.Gct.permPoly ℂ (m + 2)) =
      ((m + 2).factorial : ℂ)) (t : Fin (m + 2) × Fin (m + 2) → ℂ) (ht : t ∈ W) :
    ∑ p, M (m + 2) t p * t p = 0 := by
  have h1 := OrderCond.order_conditions_of_vanish_on_line
    (PEqualNP.Gct.permPoly ℂ (m + 2) - C ((m + 2).factorial : ℂ)) (fun _ => (1 : ℂ)) t
    (fun s => by
      rw [map_sub, eval_C, sub_eq_zero]
      exact h _ (W.smul_mem s ht))
  have h2 := h1.2
  simp only [map_sub, pderiv_C, sub_zero, hess_at_one] at h2
  have : ∑ a, ∑ b, (if a.1 ≠ b.1 ∧ a.2 ≠ b.2 then (m.factorial : ℂ) else 0) * t a * t b =
      (m.factorial : ℂ) * ∑ p, M (m + 2) t p * t p := by
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [M_apply, sum_mul, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [this] at h2
  rcases mul_eq_zero.1 h2 with h0 | h0
  · exact absurd h0 (by exact_mod_cast (Nat.factorial_pos m).ne')
  · exact h0

theorem M_symm (t u : Fin n × Fin n → ℂ) :
    ∑ p, M n t p * u p = ∑ p, M n u p * t p := by
  simp only [M_apply, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  simp only [ne_comm]
  split_ifs <;> ring

theorem isotropic (m : ℕ) (W : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ))
    (h : ∀ t ∈ W, eval ((fun _ => (1 : ℂ)) + t) (PEqualNP.Gct.permPoly ℂ (m + 2)) =
      ((m + 2).factorial : ℂ)) (t u : Fin (m + 2) × Fin (m + 2) → ℂ) (ht : t ∈ W)
    (hu : u ∈ W) : ∑ p, M (m + 2) t p * u p = 0 := by
  have h1 := quad_zero m W h _ (W.add_mem ht hu)
  have h2 := quad_zero m W h t ht
  have h3 := quad_zero m W h u hu
  have e : ∑ p, M (m + 2) (t + u) p * (t + u) p =
      ∑ p, M (m + 2) t p * t p + ∑ p, M (m + 2) u p * u p +
        (∑ p, M (m + 2) t p * u p + ∑ p, M (m + 2) u p * t p) := by
    simp only [map_add, Pi.add_apply, add_mul, mul_add, sum_add_distrib]
    ring
  rw [e, h2, h3, M_symm u t] at h1
  have : (2 : ℂ) * ∑ p, M (m + 2) t p * u p = 0 := by linear_combination h1
  rcases mul_eq_zero.1 this with h0 | h0
  · norm_num at h0
  · exact h0

noncomputable def polar (n : ℕ) : (Fin n × Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n × Fin n → ℂ) :=
  LinearMap.mk₂ ℂ (fun t u => ∑ p, M n t p * u p)
    (fun t t' u => by simp only [map_add, Pi.add_apply, add_mul, sum_add_distrib])
    (fun c t u => by simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc])
    (fun t u u' => by simp only [Pi.add_apply, mul_add, sum_add_distrib])
    (fun c t u => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun p _ => by ring)

theorem polar_apply (t u : Fin n × Fin n → ℂ) : polar n t u = ∑ p, M n t p * u p := rfl

theorem polar_injective (hn : 2 ≤ n) : Function.Injective (polar n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  apply M_injective hn
  rw [map_zero]
  ext p
  have h : polar n t (Pi.single p 1) = 0 := by rw [ht]; rfl
  rw [polar_apply] at h
  simpa [Pi.single_apply] using h

/-- A totally isotropic subspace has at most half the dimension. -/
theorem two_mul_finrank_le (hn : 2 ≤ n) (W : Submodule ℂ (Fin n × Fin n → ℂ))
    (h : ∀ t ∈ W, ∀ u ∈ W, ∑ p, M n t p * u p = 0) : 2 * Module.finrank ℂ W ≤ n ^ 2 := by
  have hr : ∀ t : W, (polar n).domRestrict W t ∈ W.dualAnnihilator := fun t =>
    (Submodule.mem_dualAnnihilator _).2 fun u hu => h t t.2 u hu
  have hinj : Function.Injective (((polar n).domRestrict W).codRestrict W.dualAnnihilator hr) :=
    fun a b hab => Subtype.ext (polar_injective hn (congrArg Subtype.val hab))
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have h3 : Module.finrank ℂ (Fin n × Fin n → ℂ) = n ^ 2 := by
    rw [Module.finrank_fintype_fun_eq_card]; simp [sq]
  omega

/-- Main theorem: for `n ≥ 2`, a space of `n × n` matrices with `perm (J + t) = n!` for all `t`
in it has `2 * dim ≤ n ^ 2`. -/
theorem main (n : ℕ) (hn : 2 ≤ n) (W : Submodule ℂ (Fin n × Fin n → ℂ))
    (h : ∀ t ∈ W, eval ((fun _ => (1 : ℂ)) + t) (PEqualNP.Gct.permPoly ℂ n) =
      (n.factorial : ℂ)) : 2 * Module.finrank ℂ W ≤ n ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact two_mul_finrank_le hn W fun t ht u hu => isotropic m W h t u ht hu

end PEqualNP.Gct.PermIsotropicGeneral
