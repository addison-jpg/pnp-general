import Mathlib.LinearAlgebra.UnitaryGroup
import PEqualNP.Defs.QuantumGravity

/-!
Seat S4 of `qg-frontier` (rank 3): two-level saturation.

`twoLevel ι` is the set of unitaries that are the identity outside a `2 × 2` block (indices `a`,
`b`). `reachable_twoLevel`: every unitary of `Fin d` is a product of at most `d (d+1) / 2`
two-level unitaries (Givens / Reck column elimination: `d (d-1) / 2` rotations and `d` phases).
-/

namespace PEqualNP.QuantumGravity.Open.TwoLevel

open PEqualNP.QuantumGravity Matrix

/-- Unitaries that are the identity outside a `2 × 2` block. -/
def twoLevel (ι : Type) [Fintype ι] [DecidableEq ι] : Set (Matrix.unitaryGroup ι ℂ) :=
  {U | ∃ a b : ι, ∀ x y : ι, (x ≠ a ∧ x ≠ b) ∨ (y ≠ a ∧ y ≠ b) →
    (U : Matrix ι ι ℂ) x y = (1 : Matrix ι ι ℂ) x y}

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sum2 (x s : ι) (hxs : x ≠ s) (p q : ℂ) (h : ι → ℂ) :
    ∑ w, (if w = s then p else if w = x then q else 0) * h w = p * h s + q * h x := by
  rw [Finset.sum_eq_add s x hxs.symm]
  · simp [hxs]
  · intro c _ hc
    simp [hc.1, hc.2]
  · simp
  · simp


/-- The `2 × 2` block matrix with entries `c1 c2 / c3 c4` at rows and columns `s, x`. -/
def blk (x s : ι) (c1 c2 c3 c4 : ℂ) : Matrix ι ι ℂ := fun y z =>
  if y = s then (if z = s then c1 else if z = x then c2 else 0)
  else if y = x then (if z = s then c3 else if z = x then c4 else 0)
  else (1 : Matrix ι ι ℂ) y z

theorem blk_off (x s : ι) (hxs : x ≠ s) (c1 c2 c3 c4 : ℂ) (y z : ι)
    (h : (y ≠ x ∧ y ≠ s) ∨ (z ≠ x ∧ z ≠ s)) :
    blk x s c1 c2 c3 c4 y z = (1 : Matrix ι ι ℂ) y z := by
  by_cases hys : y = s
  · have hz : z ≠ x ∧ z ≠ s := by
      rcases h with h | h
      · exact absurd hys h.2
      · exact h
    subst hys
    simp [blk, hz.1, hz.2, Matrix.one_apply_ne (Ne.symm hz.2)]
  · by_cases hyx : y = x
    · have hz : z ≠ x ∧ z ≠ s := by
        rcases h with h | h
        · exact absurd hyx h.1
        · exact h
      subst hyx
      simp [blk, hxs, hz.1, hz.2, Matrix.one_apply_ne (Ne.symm hz.1)]
    · simp [blk, hys, hyx]

theorem blk_mul_star (x s : ι) (hxs : x ≠ s) (c1 c2 c3 c4 : ℂ)
    (h11 : c1 * star c1 + c2 * star c2 = 1) (h22 : c3 * star c3 + c4 * star c4 = 1)
    (h12 : c1 * star c3 + c2 * star c4 = 0) :
    blk x s c1 c2 c3 c4 * star (blk x s c1 c2 c3 c4) = 1 := by
  have h21 : c3 * star c1 + c4 * star c2 = 0 := by
    have := congrArg star h12
    simpa [mul_comm] using this
  simp only [Complex.star_def] at h11 h22 h12 h21
  ext y z
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, Complex.star_def]
  by_cases hys : y = s
  · subst hys
    have : ∀ w, blk x y c1 c2 c3 c4 y w = (if w = y then c1 else if w = x then c2 else 0) := by
      intro w; simp [blk]
    simp_rw [this]
    rw [sum2 x y hxs]
    by_cases hzs : z = y
    · subst hzs; simp [blk, h11, hxs]
    · by_cases hzx : z = x
      · subst hzx; simp [blk, hxs, h12, hzs, Ne.symm hzs]
      · simp [blk, hzs, hzx, Ne.symm hzs]
  · by_cases hyx : y = x
    · subst hyx
      have : ∀ w, blk y s c1 c2 c3 c4 y w = (if w = s then c3 else if w = y then c4 else 0) := by
        intro w; simp [blk, hys]
      simp_rw [this]
      rw [sum2 y s hxs]
      by_cases hzs : z = s
      · subst hzs; simp [blk, hxs, h21, Ne.symm hxs]
      · by_cases hzx : z = y
        · subst hzx; simp [blk, hxs, hzs, h22]
        · simp [blk, hzs, hzx, Ne.symm hzx, Ne.symm hxs]
    · have : ∀ w, blk x s c1 c2 c3 c4 y w = (1 : Matrix ι ι ℂ) y w := by
        intro w; simp [blk, hys, hyx]
      simp_rw [this]
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
      by_cases hzs : z = s
      · subst hzs; simp [blk, hys, hyx, Ne.symm hys]
      · by_cases hzx : z = x
        · subst hzx; simp [blk, hys, hyx, Ne.symm hyx, hzs]
        · simp [blk, hzs, hzx, Matrix.one_apply, eq_comm]


/-- A Givens rotation killing the entry `(x, s)`. -/
theorem givens (W : Matrix.unitaryGroup ι ℂ) (x s : ι) (hxs : x ≠ s) :
    ∃ G : Matrix.unitaryGroup ι ℂ,
      (∀ y z, (y ≠ x ∧ y ≠ s) ∨ (z ≠ x ∧ z ≠ s) →
        (G : Matrix ι ι ℂ) y z = (1 : Matrix ι ι ℂ) y z) ∧
      ((G * W : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) x s = 0 := by
  by_cases hb : (W : Matrix ι ι ℂ) x s = 0
  · refine ⟨1, fun y z _ => rfl, ?_⟩
    simpa using hb
  set a : ℂ := (W : Matrix ι ι ℂ) s s with ha
  set b : ℂ := (W : Matrix ι ι ℂ) x s with hbdef
  have hn : 0 < Complex.normSq a + Complex.normSq b := by
    have h1 : 0 < Complex.normSq b := Complex.normSq_pos.mpr hb
    have h2 := Complex.normSq_nonneg a
    linarith
  set r : ℝ := Real.sqrt (Complex.normSq a + Complex.normSq b) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hn
  have hr2 : (r : ℂ) ^ 2 = (Complex.normSq a + Complex.normSq b : ℝ) := by
    rw [← Complex.ofReal_pow, hr, Real.sq_sqrt hn.le]
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hab : ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) = a * (starRingEnd ℂ) a + b * (starRingEnd ℂ) b := by
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    ring
  have h11 : (starRingEnd ℂ a / r) * star (starRingEnd ℂ a / r)
      + (starRingEnd ℂ b / r) * star (starRingEnd ℂ b / r) = 1 := by
    simp only [Complex.star_def, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    field_simp
    rw [hr2, hab]
    ring
  have h22 : (-b / r) * star (-b / r) + (a / r) * star (a / r) = 1 := by
    simp only [Complex.star_def, map_div₀, map_neg, Complex.conj_ofReal]
    field_simp
    rw [hr2, hab]
    ring
  have h12 : (starRingEnd ℂ a / r) * star (-b / r) + (starRingEnd ℂ b / r) * star (a / r) = 0 := by
    simp only [Complex.star_def, map_div₀, map_neg, Complex.conj_conj, Complex.conj_ofReal]
    field_simp
    ring
  have hmem : blk x s (starRingEnd ℂ a / r) (starRingEnd ℂ b / r) (-b / r) (a / r) ∈
      Matrix.unitaryGroup ι ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    exact blk_mul_star x s hxs _ _ _ _ h11 h22 h12
  refine ⟨⟨_, hmem⟩, fun y z h => blk_off x s hxs _ _ _ _ y z h, ?_⟩
  show (blk x s (starRingEnd ℂ a / r) (starRingEnd ℂ b / r) (-b / r) (a / r) * (W : Matrix ι ι ℂ)) x s = 0
  rw [Matrix.mul_apply]
  have : ∀ w, blk x s (starRingEnd ℂ a / r) (starRingEnd ℂ b / r) (-b / r) (a / r) x w
      = (if w = s then -b / r else if w = x then a / r else 0) := by
    intro w; simp [blk, hxs]
  simp_rw [this]
  rw [sum2 x s hxs]
  rw [← ha, ← hbdef]
  field_simp
  ring


/-- `M` is the identity outside `S × S`. -/
def Supp (S : Finset ι) (M : Matrix ι ι ℂ) : Prop :=
  ∀ x y, (x ∉ S ∨ y ∉ S) → M x y = (1 : Matrix ι ι ℂ) x y

theorem Supp.mul {S : Finset ι} {M N : Matrix ι ι ℂ} (hM : Supp S M) (hN : Supp S N) :
    Supp S (M * N) := by
  intro x y h
  rcases h with h | h
  · have h1 : ∀ w, M x w = (1 : Matrix ι ι ℂ) x w := fun w => hM x w (Or.inl h)
    have : (M * N) x y = ((1 : Matrix ι ι ℂ) * N) x y := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun w _ => by rw [h1 w]
    rw [this, Matrix.one_mul]
    exact hN x y (Or.inl h)
  · have h1 : ∀ w, N w y = (1 : Matrix ι ι ℂ) w y := fun w => hN w y (Or.inr h)
    have : (M * N) x y = (M * (1 : Matrix ι ι ℂ)) x y := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun w _ => by rw [h1 w]
    rw [this, Matrix.mul_one]
    exact hM x y (Or.inr h)

theorem Supp.one (S : Finset ι) : Supp S (1 : Matrix ι ι ℂ) := fun _ _ _ => rfl

theorem Supp.list_prod {S : Finset ι} (l : List (Matrix.unitaryGroup ι ℂ))
    (h : ∀ g ∈ l, Supp S (g : Matrix ι ι ℂ)) : Supp S (l.prod : Matrix ι ι ℂ) := by
  induction l with
  | nil => exact Supp.one S
  | cons g l ih =>
    rw [List.prod_cons, Matrix.UnitaryGroup.mul_val]
    exact (h g (by simp)).mul (ih fun g hg => h g (by simp [hg]))

theorem reach_mono {k m : ℕ} (hkm : k ≤ m) {A : Matrix.unitaryGroup ι ℂ}
    (h : A ∈ ReachableIn (twoLevel ι) k) : A ∈ ReachableIn (twoLevel ι) m := by
  obtain ⟨l, hl, hs, hp⟩ := h
  exact ⟨l, hl.trans hkm, hs, hp⟩

theorem reach_mul {k m : ℕ} {A B : Matrix.unitaryGroup ι ℂ}
    (hA : A ∈ ReachableIn (twoLevel ι) k) (hB : B ∈ ReachableIn (twoLevel ι) m) :
    A * B ∈ ReachableIn (twoLevel ι) (k + m) := by
  obtain ⟨l, hl, hs, rfl⟩ := hA
  obtain ⟨l', hl', hs', rfl⟩ := hB
  refine ⟨l ++ l', by simp; omega, ?_, by simp⟩
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hs x h
  · exact hs' x h

theorem twoLevel_inv {A : Matrix.unitaryGroup ι ℂ} (h : A ∈ twoLevel ι) : A⁻¹ ∈ twoLevel ι := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨a, b, fun x y hxy => ?_⟩
  rw [Matrix.UnitaryGroup.inv_val, Matrix.star_apply]
  have := hab y x (by tauto)
  rw [this]
  by_cases hxy' : x = y
  · subst hxy'; simp
  · simp [Matrix.one_apply, hxy', Ne.symm hxy']

theorem reach_inv {k : ℕ} {A : Matrix.unitaryGroup ι ℂ}
    (h : A ∈ ReachableIn (twoLevel ι) k) : A⁻¹ ∈ ReachableIn (twoLevel ι) k := by
  obtain ⟨l, hl, hs, rfl⟩ := h
  refine ⟨(l.map (·⁻¹)).reverse, by simpa using hl, ?_, ?_⟩
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
    exact twoLevel_inv (hs g hg)
  · rw [List.prod_inv_reverse]


/-- Column elimination: zero the entries of column `s` in the rows `T ⊆ S \ {s}` by Givens
rotations, one per row. -/
theorem col_elim (S : Finset ι) (s : ι) (hs : s ∈ S) (U : Matrix.unitaryGroup ι ℂ)
    (T : Finset ι) (hT : T ⊆ S.erase s) :
    ∃ l : List (Matrix.unitaryGroup ι ℂ), l.length ≤ T.card ∧
      (∀ g ∈ l, g ∈ twoLevel ι ∧ Supp S (g : Matrix ι ι ℂ)) ∧
      ∀ x ∈ T, ((l.prod * U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) x s = 0 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp, by simp⟩
  | insert x T hxT ih =>
    have hT' : T ⊆ S.erase s := fun y hy => hT (Finset.mem_insert_of_mem hy)
    obtain ⟨l, hl, hg, hz⟩ := ih hT'
    have hx := hT (Finset.mem_insert_self x T)
    rw [Finset.mem_erase] at hx
    obtain ⟨G, hG1, hG2⟩ := givens (l.prod * U) x s hx.1
    refine ⟨G :: l, by simp [Finset.card_insert_of_notMem hxT]; omega, ?_, ?_⟩
    · intro g hg'
      rcases List.mem_cons.mp hg' with rfl | hg'
      · refine ⟨⟨x, s, fun y z h => hG1 y z h⟩, fun y z h => hG1 y z ?_⟩
        rcases h with h | h
        · left; exact ⟨fun e => h (e ▸ hx.2), fun e => h (e ▸ hs)⟩
        · right; exact ⟨fun e => h (e ▸ hx.2), fun e => h (e ▸ hs)⟩
      · exact hg g hg'
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [List.prod_cons, mul_assoc]; exact hG2
      · have hyx : y ≠ x := fun e => hxT (e ▸ hy)
        have hys : y ≠ s := (Finset.mem_erase.mp (hT' hy)).1
        rw [List.prod_cons, mul_assoc, Matrix.UnitaryGroup.mul_val, Matrix.mul_apply]
        have : ∀ w, (G : Matrix ι ι ℂ) y w = (1 : Matrix ι ι ℂ) y w :=
          fun w => hG1 y w (Or.inl ⟨hyx, hys⟩)
        simp_rw [this]
        rw [← Matrix.mul_apply, Matrix.one_mul]
        exact hz y hy


/-- The phase gate: `star a` at index `s`, `1` elsewhere. -/
def phaseGate (s : ι) (a : ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun y => if y = s then star a else 1

theorem phaseGate_mem (s : ι) (a : ℂ) (ha : star a * a = 1) :
    phaseGate s a ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, phaseGate, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
  funext y
  by_cases hy : y = s
  · subst hy; simpa using ha
  · simp [hy]

theorem phaseGate_off (s : ι) (a : ℂ) (x y : ι) (h : (x ≠ s ∧ x ≠ s) ∨ (y ≠ s ∧ y ≠ s)) :
    phaseGate s a x y = (1 : Matrix ι ι ℂ) x y := by
  unfold phaseGate
  by_cases hxy : x = y
  · subst hxy
    have : x ≠ s := by tauto
    simp [this]
  · simp [Matrix.diagonal_apply_ne _ hxy, Matrix.one_apply_ne hxy]

theorem reach_supp (n : ℕ) : ∀ (S : Finset ι), S.card = n → ∀ U : Matrix.unitaryGroup ι ℂ,
    Supp S (U : Matrix ι ι ℂ) → U ∈ ReachableIn (twoLevel ι) (n * (n + 1) / 2) := by
  induction n with
  | zero =>
    intro S hS U hU
    have : S = ∅ := Finset.card_eq_zero.mp hS
    subst this
    have hU1 : U = 1 := by
      apply Subtype.ext
      ext x y
      exact hU x y (Or.inl (Finset.notMem_empty x))
    exact ⟨[], by simp, by simp, by simp [hU1]⟩
  | succ m ih =>
    intro S hS U hU
    obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have hS' : (S.erase s).card = m := by rw [Finset.card_erase_of_mem hs]; omega
    obtain ⟨l, hl, hg, hz⟩ := col_elim S s hs U (S.erase s) subset_rfl
    set W : Matrix.unitaryGroup ι ℂ := l.prod * U with hW
    have hWs : Supp S (W : Matrix ι ι ℂ) := by
      rw [hW, Matrix.UnitaryGroup.mul_val]
      exact (Supp.list_prod l fun g hg' => (hg g hg').2).mul hU
    have hcol : ∀ x, x ≠ s → (W : Matrix ι ι ℂ) x s = 0 := by
      intro x hx
      by_cases hxS : x ∈ S
      · exact hz x (Finset.mem_erase.mpr ⟨hx, hxS⟩)
      · rw [hWs x s (Or.inl hxS)]; simp [Matrix.one_apply_ne hx]
    have ha : star ((W : Matrix ι ι ℂ) s s) * (W : Matrix ι ι ℂ) s s = 1 := by
      have h1 := congrFun (congrFun (Matrix.UnitaryGroup.star_mul_self W) s) s
      rw [Matrix.mul_apply, Finset.sum_eq_single s] at h1
      · simpa using h1
      · intro x _ hx; simp [hcol x hx]
      · simp
    have hPm := phaseGate_mem s _ ha
    set Pu : Matrix.unitaryGroup ι ℂ := ⟨_, hPm⟩ with hPu
    have hPt : Pu ∈ twoLevel ι := ⟨s, s, fun x y h => phaseGate_off s _ x y h⟩
    have hPs : Supp S (Pu : Matrix ι ι ℂ) := fun x y h => phaseGate_off s _ x y (by
      rcases h with h | h
      · left; exact ⟨fun e => h (e ▸ hs), fun e => h (e ▸ hs)⟩
      · right; exact ⟨fun e => h (e ▸ hs), fun e => h (e ▸ hs)⟩)
    set W' : Matrix.unitaryGroup ι ℂ := Pu * W with hW'
    have hcol' : ∀ x, (W' : Matrix ι ι ℂ) x s = (1 : Matrix ι ι ℂ) x s := by
      intro x
      rw [hW', Matrix.UnitaryGroup.mul_val, hPu]
      have hPeq : (Pu : Matrix ι ι ℂ) = phaseGate s ((W : Matrix ι ι ℂ) s s) := rfl
      rw [hPeq, phaseGate, Matrix.diagonal_mul]
      by_cases hx : x = s
      · subst hx; simpa using ha
      · simp [hx, hcol x hx, Matrix.one_apply_ne hx]
    have hrow : ∀ y, y ≠ s → (W' : Matrix ι ι ℂ) s y = 0 := by
      have h1 := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp W'.2) s) s
      rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at h1
      have hss : (W' : Matrix ι ι ℂ) s s = 1 := by simpa using hcol' s
      simp only [Matrix.star_apply, hss, star_one, mul_one, Matrix.one_apply_eq] at h1
      have h2 : ∑ y ∈ Finset.univ.erase s,
          (W' : Matrix ι ι ℂ) s y * star ((W' : Matrix ι ι ℂ) s y) = 0 := by
        have : (1 : ℂ) + ∑ y ∈ Finset.univ.erase s,
          (W' : Matrix ι ι ℂ) s y * star ((W' : Matrix ι ι ℂ) s y) = 1 + 0 := by
          rw [add_zero]; exact h1
        exact add_left_cancel this
      have h3 := congrArg Complex.re h2
      rw [Complex.re_sum] at h3
      have h4 : ∀ y ∈ Finset.univ.erase s,
          ((W' : Matrix ι ι ℂ) s y * star ((W' : Matrix ι ι ℂ) s y)).re
            = Complex.normSq ((W' : Matrix ι ι ℂ) s y) := by
        intro y _
        rw [Complex.star_def, Complex.mul_conj]; simp
      rw [Finset.sum_congr rfl h4] at h3
      intro y hy
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).mp
        (by simpa using h3) y (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩)
      exact Complex.normSq_eq_zero.mp this
    have hW's : Supp (S.erase s) (W' : Matrix ι ι ℂ) := by
      intro x y h
      have hS1 : Supp S (W' : Matrix ι ι ℂ) := by
        rw [hW', Matrix.UnitaryGroup.mul_val]; exact hPs.mul hWs
      by_cases hxy : x ∈ S ∧ y ∈ S
      · have hor : x = s ∨ y = s := by
          rcases h with h | h
          · left; by_contra hne; exact h (Finset.mem_erase.mpr ⟨hne, hxy.1⟩)
          · right; by_contra hne; exact h (Finset.mem_erase.mpr ⟨hne, hxy.2⟩)
        rcases hor with rfl | rfl
        · by_cases hy : y = x
          · subst hy; simp [hcol']
          · rw [hrow y hy, Matrix.one_apply_ne (Ne.symm hy)]
        · rw [hcol' x]
      · apply hS1
        by_contra hnot
        push Not at hnot
        exact hxy hnot
    have hIH := ih (S.erase s) hS' W' hW's
    have hQ : Pu * l.prod ∈ ReachableIn (twoLevel ι) (m + 1) := by
      refine ⟨Pu :: l, by simp; omega, ?_, by simp⟩
      intro g hg'
      rcases List.mem_cons.mp hg' with rfl | hg'
      · exact hPt
      · exact (hg g hg').1
    have hU : U = (Pu * l.prod)⁻¹ * W' := by
      rw [hW', hW, ← mul_assoc Pu, inv_mul_cancel_left]
    rw [hU]
    have := reach_mul (reach_inv hQ) hIH
    refine reach_mono (le_of_eq ?_) this
    have e : (m + 1) * (m + 1 + 1) = m * (m + 1) + (m + 1) * 2 := by ring
    rw [e, Nat.add_mul_div_right _ _ (by norm_num)]
    omega


/-- Two-level saturation: every unitary of `Fin d` is a product of at most `d (d + 1) / 2`
two-level unitaries (`d (d - 1) / 2` Givens rotations and `d` phases). -/
theorem reachable_twoLevel (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    U ∈ ReachableIn (twoLevel (Fin d)) (d * (d + 1) / 2) :=
  reach_supp d Finset.univ (by simp) U fun x _ h => by
    rcases h with h | h <;> exact absurd (Finset.mem_univ _) h

end PEqualNP.QuantumGravity.Open.TwoLevel
