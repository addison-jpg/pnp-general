import PEqualNP.QuantumGravity.Open.KnillParam
import PEqualNP.QuantumGravity.Open.L115
import PEqualNP.QuantumGravity.Open.L116OfL115

namespace PEqualNP.QuantumGravity.Open.GateNet

open PEqualNP.QuantumGravity PEqualNP.QuantumGravity.Open.KnillParam MeasureTheory

section OpNorm

open scoped Matrix.Norms.L2Operator Matrix

variable {n : ℕ}

/-- The matrix unit `|x⟩⟨y|` of the qubits in `T`, acting on `n` qubits. -/
noncomputable def unitE (T : Finset (Fin n)) (x y : T → Bool) : Matrix (Qubits n) (Qubits n) ℂ :=
  gateMat T (Matrix.single x y (1 : ℂ))

theorem gateMat_eq_sum (T : Finset (Fin n)) (W : Matrix (T → Bool) (T → Bool) ℂ) :
    gateMat T W = ∑ x, ∑ y, W x y • unitE T x y := by
  classical
  ext a b
  simp only [unitE, gateMat, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul]
  by_cases h : ∀ i, i ∉ T → a i = b i
  · simp only [if_pos h]
    simp [ite_and, Finset.sum_ite_eq']
  · simp only [if_neg h]
    simp

/-- Restriction to the qubits in `T`. -/
def restr (T : Finset (Fin n)) (b : Qubits n) : T → Bool := fun i => b i

/-- `b` with the qubits of `T` overwritten by `x`. -/
def extend (T : Finset (Fin n)) (x : T → Bool) (b : Qubits n) : Qubits n :=
  fun i => if h : i ∈ T then x ⟨i, h⟩ else b i

theorem unitE_entry (T : Finset (Fin n)) (x y : T → Bool) (a b : Qubits n) :
    unitE T x y a b = if restr T b = y ∧ a = extend T x b then 1 else 0 := by
  classical
  simp only [unitE, gateMat, Matrix.of_apply, Matrix.single_apply]
  by_cases h : ∀ i, i ∉ T → a i = b i
  · simp only [if_pos h]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2.symm, ?_⟩
      funext i
      by_cases hi : i ∈ T
      · simp only [extend, dif_pos hi]
        exact (congrFun h1 ⟨i, hi⟩).symm
      · simp only [extend, dif_neg hi]
        exact h i hi
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1.symm⟩
      funext i
      rw [h2]
      simp [extend, restr]
  · simp only [if_neg h]
    symm
    rw [if_neg]
    rintro ⟨_, h2⟩
    apply h
    intro i hi
    rw [h2]
    simp [extend, hi]

theorem extend_inj (T : Finset (Fin n)) (x y : T → Bool) {b c : Qubits n} (hb : restr T b = y)
    (hc : restr T c = y) (h : extend T x b = extend T x c) : b = c := by
  funext i
  by_cases hi : i ∈ T
  · have h1 := congrFun hb ⟨i, hi⟩
    have h2 := congrFun hc ⟨i, hi⟩
    simp only [restr] at h1 h2
    rw [h1, h2]
  · have := congrFun h i
    simpa [extend, hi] using this

theorem unitE_gram (T : Finset (Fin n)) (x y : T → Bool) :
    (unitE T x y)ᴴ * unitE T x y = Matrix.diagonal (fun b => if restr T b = y then (1 : ℂ) else 0) := by
  classical
  ext b c
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, unitE_entry, Matrix.diagonal_apply]
  by_cases hb : restr T b = y
  · by_cases hc : restr T c = y
    · simp only [hb, hc, true_and]
      simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      by_cases hbc : b = c
      · subst hbc; simp
      · have : ¬ extend T x b = extend T x c := fun h => hbc (extend_inj T x y hb hc h)
        simp [hbc, this]
    · simp [hc]
      intro h; subst h; exact hc
  · simp [hb]

theorem norm_unitE_le (T : Finset (Fin n)) (x y : T → Bool) : ‖unitE T x y‖ ≤ 1 := by
  classical
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (unitE T x y)
  rw [unitE_gram, Matrix.l2_opNorm_diagonal] at h1
  have h2 : ‖(fun b : Qubits n => if restr T b = y then (1 : ℂ) else 0)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => ?_
    by_cases h : restr T b = y <;> simp [h]
  nlinarith [norm_nonneg (unitE T x y)]

/-- L-qg-frontier rank 1a: the operator norm of `W ⊗ 1` is at most the sum of the moduli of the
entries of `W`. -/
theorem opNorm_gateMat_le {n : ℕ} (T : Finset (Fin n))
    (W : Matrix (T → Bool) (T → Bool) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Qubits n) (KnillParam.gateMat T W)‖ ≤
      ∑ x, ∑ y, ‖W x y‖ := by
  rw [Matrix.l2_opNorm_toEuclideanCLM, gateMat_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [norm_smul]
  calc ‖W x y‖ * ‖unitE T x y‖ ≤ ‖W x y‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_unitE_le T x y) (norm_nonneg _)
    _ = ‖W x y‖ := mul_one _

end OpNorm

section Net

variable {n : ℕ}

theorem gateMat_sub (T : Finset (Fin n)) (A B : Matrix (T → Bool) (T → Bool) ℂ) :
    gateMat T (A - B) = gateMat T A - gateMat T B := by
  ext a b
  simp only [gateMat, Matrix.of_apply, Matrix.sub_apply]
  split_ifs <;> simp

/-- The cell of a complex number in the grid of mesh `η`. -/
noncomputable def cell (η : ℝ) (z : ℂ) : ℤ × ℤ := (⌊z.re / η⌋, ⌊z.im / η⌋)

theorem norm_sub_le_of_cell {η : ℝ} (hη : 0 < η) {z w : ℂ} (h : cell η z = cell η w) :
    ‖z - w‖ ≤ 2 * η := by
  simp only [cell, Prod.mk.injEq] at h
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h.1
  have h2 := Int.abs_sub_lt_one_of_floor_eq_floor h.2
  rw [← sub_div, abs_div, abs_of_pos hη, div_lt_one hη] at h1 h2
  have := Complex.norm_le_abs_re_add_abs_im (z - w)
  simp only [Complex.sub_re, Complex.sub_im] at this
  linarith

theorem cell_mem {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    cell η z ∈ Finset.Icc (-⌈1 / η⌉) ⌈1 / η⌉ ×ˢ Finset.Icc (-⌈1 / η⌉) ⌈1 / η⌉ := by
  have key : ∀ a : ℝ, |a| ≤ 1 → ⌊a / η⌋ ∈ Finset.Icc (-⌈1 / η⌉) ⌈1 / η⌉ := by
    intro a ha
    have hM := Int.le_ceil (1 / η)
    have hb : |a / η| ≤ 1 / η := by
      rw [abs_div, abs_of_pos hη]
      exact div_le_div_of_nonneg_right ha hη.le
    have hb' := abs_le.1 hb
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]
      push_cast
      linarith [hb'.1]
    · rw [← Int.cast_le (R := ℝ)]
      exact (Int.floor_le _).trans (hb'.2.trans hM)
  exact Finset.mem_product.2 ⟨key _ ((Complex.abs_re_le_norm z).trans hz),
    key _ ((Complex.abs_im_le_norm z).trans hz)⟩

/-- The gates of the index set `T` whose block lies in the cell `c`. -/
def Good (η : ℝ) (T : TT n) (c : (T.1 → Bool) × (T.1 → Bool) → ℤ × ℤ)
    (h : qubitUnitaryGroup n) : Prop :=
  ∃ W : Matrix (T.1 → Bool) (T.1 → Bool) ℂ, (h : Matrix (Qubits n) (Qubits n) ℂ) = gateMat T.1 W ∧
    ∀ p, cell η (W p.1 p.2) = c p

theorem card_pairs_le (T : TT n) :
    ((Fintype.card (T.1 → Bool) : ℕ) : ℝ) * (Fintype.card (T.1 → Bool) : ℕ) ≤ 16 := by
  have h2 : 2 ^ T.1.card ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) T.2
  have : Fintype.card (T.1 → Bool) ≤ 4 := by
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using h2
  have h4 : ((Fintype.card (T.1 → Bool) : ℕ) : ℝ) ≤ 4 := by exact_mod_cast this
  nlinarith [(Nat.cast_nonneg (Fintype.card (T.1 → Bool)) : (0 : ℝ) ≤ _)]

theorem good_close {η : ℝ} (hη : 0 < η) (T : TT n) (c : (T.1 → Bool) × (T.1 → Bool) → ℤ × ℤ)
    {h g : qubitUnitaryGroup n} (hh : Good η T c h) (hg : Good η T c g) :
    opDist (h : Matrix (Qubits n) (Qubits n) ℂ) (g : Matrix (Qubits n) (Qubits n) ℂ) ≤ 32 * η := by
  obtain ⟨W1, h1, c1⟩ := hh
  obtain ⟨W2, h2, c2⟩ := hg
  unfold opDist
  rw [h1, h2, ← gateMat_sub]
  refine (opNorm_gateMat_le T.1 _).trans ?_
  have hb : ∀ x y, ‖(W1 - W2) x y‖ ≤ 2 * η := fun x y =>
    norm_sub_le_of_cell hη (by rw [c1 (x, y), c2 (x, y)])
  calc ∑ x, ∑ y, ‖(W1 - W2) x y‖ ≤ ∑ _x : T.1 → Bool, ∑ _y : T.1 → Bool, 2 * η :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hb x y
    _ = ((Fintype.card (T.1 → Bool) : ℕ) : ℝ) * (Fintype.card (T.1 → Bool) : ℕ) * (2 * η) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ 16 * (2 * η) := mul_le_mul_of_nonneg_right (card_pairs_le T) (by positivity)
    _ = 32 * η := by ring

theorem card_TT_le (n : ℕ) : Fintype.card (TT n) ≤ (n + 1) ^ 2 := by
  classical
  rw [Fintype.card_subtype]
  have hsub : (Finset.univ.filter fun T : Finset (Fin n) => T.card ≤ 2) ⊆
      Finset.powersetCard 0 (Finset.univ : Finset (Fin n)) ∪
        Finset.powersetCard 1 (Finset.univ : Finset (Fin n)) ∪
        Finset.powersetCard 2 (Finset.univ : Finset (Fin n)) := by
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    simp only [Finset.mem_union, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    omega
  have h1 := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Nat.choose_zero_right,
    Nat.choose_one_right] at h1
  have h2 : n.choose 2 ≤ n ^ 2 := Nat.choose_le_pow n 2
  nlinarith

theorem twoQubitGates_net : ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∃ N : Finset (qubitUnitaryGroup n), (↑N : Set (qubitUnitaryGroup n)) ⊆ twoQubitGates n ∧
      (N.card : ℝ) ≤ ((n : ℝ) + 1) ^ 2 * (C / δ) ^ 32 ∧
      ∀ g ∈ twoQubitGates n, ∃ h ∈ N,
        opDist (h : Matrix (Qubits n) (Qubits n) ℂ) (g : Matrix (Qubits n) (Qubits n) ℂ) ≤ δ := by
  classical
  refine ⟨100, by norm_num, fun n δ hδ hδ1 => ?_⟩
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = δ / 32 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  obtain ⟨M, hM⟩ : ∃ M : ℤ, M = ⌈1 / η⌉ := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]
    have : (0 : ℝ) < 1 / η := by positivity
    exact_mod_cast Int.one_le_ceil_iff.2 this
  have hM2 : (M : ℝ) ≤ 32 / δ + 1 := by
    have h1 := Int.ceil_lt_add_one (1 / η)
    rw [← hM] at h1
    have : 1 / η = 32 / δ := by rw [hηdef]; field_simp
    linarith
  set Box : Finset (ℤ × ℤ) := Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M with hBox
  have hBcard : ((Box.card : ℕ) : ℝ) = (2 * (M : ℝ) + 1) ^ 2 := by
    have hM0 : (0 : ℤ) ≤ M := by exact_mod_cast (by linarith : (0 : ℝ) ≤ M)
    have hc : ((Finset.Icc (-M) M).card : ℝ) = 2 * (M : ℝ) + 1 := by
      rw [Int.card_Icc]
      have : ((M + 1 - -M).toNat : ℤ) = 2 * M + 1 := by
        rw [Int.toNat_of_nonneg (by omega)]; ring
      have h2 : (((M + 1 - -M).toNat : ℕ) : ℝ) = (((M + 1 - -M).toNat : ℤ) : ℝ) := by
        norm_cast
      rw [h2, this]; push_cast; ring
    rw [hBox, Finset.card_product]
    push_cast
    rw [hc]; ring
  have hB1 : (1 : ℝ) ≤ ((Box.card : ℕ) : ℝ) := by
    rw [hBcard]; nlinarith
  let I : Finset (Σ T : TT n, ((T.1 → Bool) × (T.1 → Bool) → ℤ × ℤ)) :=
    (Finset.univ : Finset (TT n)).sigma (fun T => Fintype.piFinset fun _ => Box)
  let S := I.filter fun i => ∃ h, Good η i.1 i.2 h
  let f : (Σ T : TT n, ((T.1 → Bool) × (T.1 → Bool) → ℤ × ℤ)) → qubitUnitaryGroup n :=
    fun i => if hh : ∃ h, Good η i.1 i.2 h then hh.choose else 1
  have hf : ∀ i ∈ S, Good η i.1 i.2 (f i) := by
    intro i hi
    have hh : ∃ h, Good η i.1 i.2 h := (Finset.mem_filter.1 hi).2
    simp only [f, dite_eq_left_iff]
    rw [dif_pos hh]
    exact hh.choose_spec
  refine ⟨S.image f, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hh)
    obtain ⟨W, hW, -⟩ := hf i hi
    refine ⟨i.1.1, i.1.2, W, fun x y => ?_⟩
    have := congrFun (congrFun hW x) y
    exact this
  · have hIcard : (I.card : ℝ) ≤ (Fintype.card (TT n) : ℝ) * ((Box.card : ℕ) : ℝ) ^ 16 := by
      have : I.card = ∑ T : TT n, Box.card ^ Fintype.card ((T.1 → Bool) × (T.1 → Bool)) := by
        simp only [I, Finset.card_sigma, Fintype.card_piFinset, Finset.prod_const,
          Finset.card_univ]
      rw [this]
      push_cast
      calc ∑ T : TT n, ((Box.card : ℕ) : ℝ) ^ Fintype.card ((T.1 → Bool) × (T.1 → Bool))
          ≤ ∑ _T : TT n, ((Box.card : ℕ) : ℝ) ^ 16 := by
            refine Finset.sum_le_sum fun T _ => pow_le_pow_right₀ hB1 ?_
            simpa using card_le_sixteen T
        _ = _ := by simp
    have hcard : (S.image f).card ≤ I.card :=
      (Finset.card_image_le).trans (Finset.card_le_card (Finset.filter_subset _ _))
    have hTT : (Fintype.card (TT n) : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by exact_mod_cast card_TT_le n
    have h3 : (2 * (M : ℝ) + 1) ≤ 100 / δ := by
      have : (1 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
      have e : 100 / δ = 100 * (1 / δ) := by ring
      have e2 : 32 / δ = 32 * (1 / δ) := by ring
      rw [e]; rw [e2] at hM2; linarith
    calc ((S.image f).card : ℝ) ≤ I.card := by exact_mod_cast hcard
      _ ≤ (Fintype.card (TT n) : ℝ) * ((Box.card : ℕ) : ℝ) ^ 16 := hIcard
      _ ≤ ((n : ℝ) + 1) ^ 2 * (100 / δ) ^ 32 := by
        rw [hBcard, ← pow_mul]
        refine mul_le_mul hTT ?_ (by positivity) (by positivity)
        exact pow_le_pow_left₀ (by linarith) h3 32
  · intro g hg
    obtain ⟨T, hT, W, hW⟩ := hg
    have hU : (g : Matrix (Qubits n) (Qubits n) ℂ) * star (g : Matrix (Qubits n) (Qubits n) ℂ)
        = 1 := Matrix.mem_unitaryGroup_iff.1 g.2
    have hWu : W * star W = 1 := block_unitary hU hW
    have hWm : W ∈ Matrix.unitaryGroup (T → Bool) ℂ := Matrix.mem_unitaryGroup_iff.2 hWu
    have hent : ∀ x y, ‖W x y‖ ≤ 1 := fun x y => entry_norm_bound_of_unitary hWm x y
    let Ts : TT n := ⟨T, hT⟩
    let c : (Ts.1 → Bool) × (Ts.1 → Bool) → ℤ × ℤ := fun p => cell η (W p.1 p.2)
    have hgood : Good η Ts c g := ⟨W, by funext x y; exact hW x y, fun p => rfl⟩
    have hmem : (⟨Ts, c⟩ : Σ T : TT n, ((T.1 → Bool) × (T.1 → Bool) → ℤ × ℤ)) ∈ S := by
      refine Finset.mem_filter.2 ⟨?_, g, hgood⟩
      refine Finset.mem_sigma.2 ⟨Finset.mem_univ _, Fintype.mem_piFinset.2 fun p => ?_⟩
      have := cell_mem hη (hent p.1 p.2)
      rw [hBox, hM]; exact this
    refine ⟨f ⟨Ts, c⟩, Finset.mem_image_of_mem f hmem, ?_⟩
    have := good_close hη Ts c (hf _ hmem) hgood
    rw [hηdef] at this
    linarith

end Net

end PEqualNP.QuantumGravity.Open.GateNet
