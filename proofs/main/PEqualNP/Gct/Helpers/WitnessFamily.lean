import Mathlib

/-!
# A uniform witness family for the `L_gct` rows

For every `q ≥ 4` we exhibit a subspace `L` of `Fin 4 × Fin q → ℂ` of dimension `q + 1`
on which every row sums to zero and the quadratic, cubic and quartic distinct-column sums
vanish. Row 0 is an arbitrary sum-zero vector; rows 1–3 live on columns `0..3` and are
`(x₀, -x₀, x₁, -x₁)` twisted by a primitive cube root of unity.
-/

namespace PEqualNP.Gct.WitnessFamily

open Finset

noncomputable section

variable {n : ℕ}

/-- Split a sum over `Fin (4 + n)` into the first four columns and the tail. -/
theorem sum_split (n : ℕ) (f : Fin (4 + n) → ℂ) :
    ∑ j, f j = ∑ k : Fin 4, f (Fin.castAdd n k) + ∑ i : Fin n, f (Fin.natAdd 4 i) :=
  Fin.sum_univ_add f

@[simp] theorem natAdd_ne_castAdd (i : Fin n) (k : Fin 4) :
    (Fin.natAdd 4 i = Fin.castAdd n k) ↔ False := by
  simp only [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd, iff_false]; omega

@[simp] theorem castAdd_ne_natAdd (i : Fin n) (k : Fin 4) :
    (Fin.castAdd n k = Fin.natAdd 4 i) ↔ False := by
  simp only [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd, iff_false]; omega

/-- Reduce a sum over `Fin (4 + n)` to the first four columns, when the tail contributes
`r j * c` with `∑ r = 0`. -/
theorem sum_tail_reduce (S r : Fin (4 + n) → ℂ) (c : ℂ) (hr : ∑ j, r j = 0)
    (hS : ∀ i : Fin n, S (Fin.natAdd 4 i) = r (Fin.natAdd 4 i) * c) :
    ∑ j, S j = ∑ k : Fin 4, (S (Fin.castAdd n k) - r (Fin.castAdd n k) * c) := by
  rw [sum_split n] at hr ⊢
  simp only [hS, ← Finset.sum_mul, Finset.sum_sub_distrib]
  rw [eq_neg_of_add_eq_zero_right hr]
  ring

/-- The three twisted rows on the first four columns. -/
def M (z : ℂ) (x : Fin 2 → ℂ) : Fin 4 → Fin 4 → ℂ :=
  ![![0, 0, 0, 0],
    ![x 0, -x 0, x 1, -x 1],
    ![z * x 0, -(z * x 0), z ^ 2 * x 1, -(z ^ 2 * x 1)],
    ![z ^ 2 * x 0, -(z ^ 2 * x 0), z * x 1, -(z * x 1)]]

/-- Row `b ≥ 1` extended by zero to `Fin (4 + n)`. -/
def row (z : ℂ) (x : Fin 2 → ℂ) (b : Fin 4) : Fin (4 + n) → ℂ :=
  Fin.addCases (fun k => M z x b k) (fun _ => 0)

def entries (z : ℂ) (r : Fin (4 + n) → ℂ) (x : Fin 2 → ℂ) (p : Fin 4 × Fin (4 + n)) : ℂ :=
  ![r p.2, row z x 1 p.2, row z x 2 p.2, row z x 3 p.2] p.1

/-- Simp set reducing everything to the first four columns. -/
macro "reduce_cols" : tactic => `(tactic|
  (simp (config := { decide := true }) only [sum_split _, Fin.sum_univ_four, entries, row,
      Fin.addCases_left, Fin.addCases_right, natAdd_ne_castAdd, castAdd_ne_natAdd]
   simp (config := { decide := true }) [M]))

theorem quadratic (z : ℂ) (hz : 1 + z + z ^ 2 = 0) (r : Fin (4 + n) → ℂ) (hr : ∑ j, r j = 0)
    (x : Fin 2 → ℂ) :
    (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
      if a < b then entries z r x (a, j) * entries z r x (b, l) else 0) = 0 := by
  refine (sum_tail_reduce _ r
    (∑ l, ∑ b : Fin 4, if (0 : Fin 4) < b then entries z r x (b, l) else 0) hr ?_).trans ?_
  · intro i
    reduce_cols
    ring
  · reduce_cols
    grobner

theorem cubic (z : ℂ) (hz : 1 + z + z ^ 2 = 0) (r : Fin (4 + n) → ℂ) (hr : ∑ j, r j = 0)
    (x : Fin 2 → ℂ) :
    (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then
        entries z r x (a, j) * entries z r x (b, l) * entries z r x (c, m) else 0) = 0 := by
  refine (sum_tail_reduce _ r
    (∑ l, ∑ m, if l = m then 0 else ∑ b : Fin 4, ∑ c : Fin 4,
      if (0 : Fin 4) < b ∧ b < c then entries z r x (b, l) * entries z r x (c, m) else 0)
    hr ?_).trans ?_
  · intro i
    reduce_cols
    ring
  · reduce_cols
    grobner

theorem quartic (z : ℂ) (hz : 1 + z + z ^ 2 = 0) (r : Fin (4 + n) → ℂ) (hr : ∑ j, r j = 0)
    (x : Fin 2 → ℂ) :
    (∑ j, ∑ l, ∑ m, ∑ k,
      if j = l ∨ j = m ∨ j = k ∨ l = m ∨ l = k ∨ m = k then 0 else
        entries z r x (0, j) * entries z r x (1, l) *
          entries z r x (2, m) * entries z r x (3, k)) = 0 := by
  refine (sum_tail_reduce _ r
    (∑ l, ∑ m, ∑ k, if l = m ∨ l = k ∨ m = k then 0 else
      entries z r x (1, l) * entries z r x (2, m) * entries z r x (3, k))
    hr ?_).trans ?_
  · intro i
    reduce_cols
    ring
  · reduce_cols
    grobner

/-- The row-sum functional. -/
def sumL (n : ℕ) : (Fin (4 + n) → ℂ) →ₗ[ℂ] ℂ where
  toFun r := ∑ j, r j
  map_add' r s := by simp [Finset.sum_add_distrib]
  map_smul' c r := by simp [Finset.mul_sum]

theorem finrank_ker_sumL (n : ℕ) : Module.finrank ℂ (LinearMap.ker (sumL n)) = 3 + n := by
  have hsurj : LinearMap.range (sumL n) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun c => ⟨Pi.single (Fin.castAdd n 0) c, ?_⟩
    simp [sumL]
  have h := LinearMap.finrank_range_add_finrank_ker (sumL n)
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

/-- The parametrisation: a sum-zero row 0 and two twist parameters. -/
def family (z : ℂ) (n : ℕ) :
    (LinearMap.ker (sumL n) × (Fin 2 → ℂ)) →ₗ[ℂ] (Fin 4 × Fin (4 + n) → ℂ) where
  toFun p := entries z p.1.val p.2
  map_add' p p' := by
    funext ⟨a, j⟩
    refine Fin.addCases (fun k => ?_) (fun i => ?_) j <;> fin_cases a <;>
      simp [entries, row, M] <;> fin_cases k <;> simp <;> ring
  map_smul' c p := by
    funext ⟨a, j⟩
    refine Fin.addCases (fun k => ?_) (fun i => ?_) j <;> fin_cases a <;>
      simp [entries, row, M] <;> fin_cases k <;> simp <;> ring

theorem family_injective (z : ℂ) (n : ℕ) : Function.Injective (family z n) := by
  rintro ⟨⟨r, hr⟩, x⟩ ⟨⟨r', hr'⟩, x'⟩ h
  have h0 : r = r' := funext fun j => congrFun h (0, j)
  have h1 : x = x' := by
    funext k
    fin_cases k
    · simpa [family, entries, row, M] using congrFun h (1, Fin.castAdd n 0)
    · simpa [family, entries, row, M] using congrFun h (1, Fin.castAdd n 2)
  subst h0 h1
  rfl

theorem witness_family_aux (n : ℕ) :
    ∃ L : Submodule ℂ (Fin 4 × Fin (4 + n) → ℂ), (∀ t ∈ L, (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧
      (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
        if a < b then t (a, j) * t (b, l) else 0) = 0 ∧
      (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
        ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then
          t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧
      (∑ j, ∑ l, ∑ m, ∑ k, if j = l ∨ j = m ∨ j = k ∨ l = m ∨ l = k ∨ m = k then 0 else
        t (0, j) * t (1, l) * t (2, m) * t (3, k)) = 0) ∧
      Module.finrank ℂ L = 4 + n + 1 := by
  obtain ⟨z, hprim⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ 3
  have hz : 1 + z + z ^ 2 = 0 := by
    simpa [Finset.sum_range_succ] using hprim.geom_sum_eq_zero (by decide)
  refine ⟨LinearMap.range (family z n), ?_, ?_⟩
  · rintro t ⟨⟨⟨r, hr⟩, x⟩, rfl⟩
    have hr' : ∑ j, r j = 0 := hr
    refine ⟨fun i => ?_, quadratic z hz r hr' x, cubic z hz r hr' x, quartic z hz r hr' x⟩
    fin_cases i
    · exact hr'
    all_goals
      simp [family, entries, row, sum_split n, Fin.sum_univ_four, M]
  · rw [LinearMap.finrank_range_of_inj (family_injective z n), Module.finrank_prod,
      finrank_ker_sumL, Module.finrank_fin_fun]
    omega

/-- **Witness family.** For every `q ≥ 4` there is a `(q + 1)`-dimensional subspace of
`Fin 4 × Fin q → ℂ` on which all row sums and the quadratic, cubic and quartic
distinct-column sums vanish (generalising `L_gct_197`, `L_gct_180`, `L_gct_198`). -/
theorem witness_family (q : ℕ) (hq : 4 ≤ q) :
    ∃ L : Submodule ℂ (Fin 4 × Fin q → ℂ), (∀ t ∈ L, (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧
      (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
        if a < b then t (a, j) * t (b, l) else 0) = 0 ∧
      (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
        ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then
          t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧
      (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else
        t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) ∧ Module.finrank ℂ L = q + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, q = 4 + n := ⟨q - 4, by omega⟩
  exact witness_family_aux n

end

end PEqualNP.Gct.WitnessFamily
