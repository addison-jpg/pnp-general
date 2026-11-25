import PEqualNP.QuantumGravity.Open.L119
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Seat C4 of `open-qg`: the weaker parametrization of `L119`, with `16` real parameters per gate.

`KnillParametrization` (`9k + 3n + 1` parameters) needs the KAK decomposition of `U(4)`, which is
not in Mathlib. Here the cheaper route is taken: a unitary `W` is `u • cayley (skewOf A)` for a
unit scalar `u` from a countable family and a real matrix `A` (the Cayley chart of `L119.lean`
reaches every unitary after a suitable phase, because a matrix has finitely many eigenvalues).
A gate acts on at most two qubits, so `W` is a `4 × 4` unitary (or smaller) and `A` has at most
`16` entries. Hence the products of at most `k` two-qubit gates are covered by countably many
everywhere differentiable maps from `ℝ^(16 k)`, and

`L119_weak : 16 * k < 4 ^ n → μ (ReachableIn (twoQubitGates n) k) = 0`.
-/

set_option linter.unusedSectionVars false

namespace PEqualNP.QuantumGravity.Open.KnillParam

open MeasureTheory Matrix PEqualNP.QuantumGravity PEqualNP.QuantumGravity.Open.L119

/-! ### Entrywise differentiability of matrix-valued maps -/

section ED

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type} [Fintype ι]
  [DecidableEq ι]

theorem diff_prod {κ : Type*} [DecidableEq κ] (s : Finset κ) {f : κ → E → ℂ}
    (h : ∀ i ∈ s, Differentiable ℝ (f i)) : Differentiable ℝ fun q => ∏ i ∈ s, f i q := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    have h1 : Differentiable ℝ (f a) := h a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact h1.mul h2

/-- A matrix-valued map all of whose entries are differentiable. -/
def ED (M : E → Matrix ι ι ℂ) : Prop := ∀ i j, Differentiable ℝ fun q => M q i j

theorem ED.const (C : Matrix ι ι ℂ) : ED (fun _ : E => C) := fun _ _ => differentiable_const _

theorem ED.add {M N : E → Matrix ι ι ℂ} (hM : ED M) (hN : ED N) : ED (fun q => M q + N q) :=
  fun i j => (hM i j).add (hN i j)

theorem ED.sub {M N : E → Matrix ι ι ℂ} (hM : ED M) (hN : ED N) : ED (fun q => M q - N q) :=
  fun i j => (hM i j).sub (hN i j)

theorem ED.smul (c : ℂ) {M : E → Matrix ι ι ℂ} (hM : ED M) : ED (fun q => c • M q) :=
  fun i j => by
    have : Differentiable ℝ (fun q => c * M q i j) := (differentiable_const c).mul (hM i j)
    simpa using this

theorem ED.mul {M N : E → Matrix ι ι ℂ} (hM : ED M) (hN : ED N) : ED (fun q => M q * N q) :=
  fun i j => by
    simp only [Matrix.mul_apply]
    have h : ∀ z ∈ (Finset.univ : Finset ι),
        Differentiable ℝ (fun q => M q i z * N q z j) := fun z _ => (hM i z).mul (hN z j)
    have h' := Differentiable.sum h
    convert h' using 1
    funext q
    simp [Finset.sum_apply]

theorem ED.comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {M : E → Matrix ι ι ℂ}
    (hM : ED M) {g : F → E} (hg : Differentiable ℝ g) : ED (fun q => M (g q)) :=
  fun i j => (hM i j).comp hg

theorem ED.det {M : E → Matrix ι ι ℂ} (hM : ED M) : Differentiable ℝ fun q => (M q).det := by
  simp only [Matrix.det_apply]
  have h : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), Differentiable ℝ (fun q =>
      (Equiv.Perm.sign σ : ℤˣ) • ∏ i, M q (σ i) i) := by
    intro σ _
    simp only [Units.smul_def, zsmul_eq_mul]
    have h2 : Differentiable ℝ (fun q => ∏ i, M q (σ i) i) := by
      exact diff_prod Finset.univ fun i _ => hM _ _
    exact (differentiable_const _).mul h2
  have h' := Differentiable.sum h
  convert h' using 1
  funext q
  simp [Finset.sum_apply]

theorem ED.adjugate {M : E → Matrix ι ι ℂ} (hM : ED M) : ED fun q => (M q).adjugate := by
  intro i j
  simp only [Matrix.adjugate_apply]
  refine ED.det (M := fun q => (M q).updateRow j (Pi.single i 1)) ?_
  intro a b
  by_cases ha : a = j
  · subst ha; simp [Matrix.updateRow_apply]
  · simpa [Matrix.updateRow_apply, ha] using hM a b

theorem ED.inv {M : E → Matrix ι ι ℂ} (hM : ED M) (hdet : ∀ q, (M q).det ≠ 0) :
    ED fun q => (M q)⁻¹ := by
  intro i j
  have : ∀ q, (M q)⁻¹ i j = ((M q).det)⁻¹ * (M q).adjugate i j := by
    intro q; rw [Matrix.inv_def, Ring.inverse_eq_inv']; simp
  simp only [this]
  exact Differentiable.mul (Differentiable.inv (ED.det hM) hdet) (ED.adjugate hM i j)

end ED

/-! ### The Cayley chart reaches every unitary after a phase -/

section Chart2

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The skew-Hermitian matrix `X` is recovered from `realOf X`. -/
theorem skewOf_realOf {X : Matrix ι ι ℂ} (hX : Xᴴ = -X) : skewOf (realOf X) = X := by
  ext i j
  have h1 := congrFun (congrFun hX i) j
  have h2 := congrFun (congrFun hX j) i
  simp only [conjTranspose_apply, Matrix.neg_apply, Pi.neg_apply] at h1 h2
  have e1 := congrArg Complex.re h1
  have e2 := congrArg Complex.im h1
  have e3 := congrArg Complex.re h2
  have e4 := congrArg Complex.im h2
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.neg_re,
    Complex.neg_im] at e1 e2 e3 e4
  apply Complex.ext <;> simp [skewOf, realOf] <;> linarith

/-- Every unitary `U` with `U + 1` invertible is a Cayley transform of a skew-Hermitian matrix. -/
theorem cayley_surj {U : Matrix ι ι ℂ} (h1 : star U * U = 1) (hV : IsUnit (U + 1)) :
    ∃ A : ι → ι → ℝ, cayley (skewOf A) = U := by
  have hdet : IsUnit (U + 1).det := (Matrix.isUnit_iff_isUnit_det _).1 hV
  set V := U + 1 with hVdef
  set W := V⁻¹ with hW
  have hWV : W * V = 1 := nonsing_inv_mul _ hdet
  have hVW : V * W = 1 := mul_nonsing_inv _ hdet
  set X := W * (U - 1) with hX
  have hX1 : 1 - X = (2 : ℂ) • W := by
    have h2 : V - (U - 1) = (2 : ℂ) • (1 : Matrix ι ι ℂ) := by rw [hVdef, two_smul]; abel
    calc 1 - X = W * V - W * (U - 1) := by rw [hWV]
      _ = W * (V - (U - 1)) := (Matrix.mul_sub _ _ _).symm
      _ = _ := by rw [h2, Matrix.mul_smul, Matrix.mul_one]
  have hsV : star V = star U * V := by
    rw [hVdef, Matrix.mul_add, h1, Matrix.mul_one, star_add, star_one, add_comm]
  have hVZ : star V * (W * U) = 1 := by
    rw [hsV, Matrix.mul_assoc, ← Matrix.mul_assoc V, hVW, Matrix.one_mul, h1]
  have hWs : star W = W * U := by
    have h3 : star W * star V = 1 := by rw [← star_mul, hVW, star_one]
    calc star W = star W * (star V * (W * U)) := by rw [hVZ, Matrix.mul_one]
      _ = (star W * star V) * (W * U) := by rw [Matrix.mul_assoc]
      _ = W * U := by rw [h3, Matrix.one_mul]
  have hsum : W * U + W = 1 := by
    calc W * U + W = W * (U + 1) := by rw [Matrix.mul_add, Matrix.mul_one]
      _ = 1 := hWV
  have hUW : U * W = 1 - W := by
    have : (U + 1) * W = 1 := hVW
    rw [Matrix.add_mul, Matrix.one_mul] at this
    rw [← this]; abel
  have hXeq : X = 1 - (2 : ℂ) • W := by rw [← hX1]; abel
  have hskew : Xᴴ = -X := by
    have : Xᴴ = star X := rfl
    rw [this, hXeq, star_sub, star_one, star_smul, hWs, show W * U = 1 - W by
      rw [← hsum]; abel]
    have h2 : star (2 : ℂ) = 2 := by simp
    rw [h2]
    module
  refine ⟨realOf X, ?_⟩
  rw [skewOf_realOf hskew]
  have hu : IsUnit (1 - X).det := isUnit_det_one_sub hskew
  have key : U * (1 - X) = 1 + X := by
    rw [hX1, Matrix.mul_smul, hUW, hXeq]; module
  have key2 := cayley_mul_one_sub hskew
  have : cayley X * (1 - X) = U * (1 - X) := by rw [key2, key]
  calc cayley X = cayley X * ((1 - X) * (1 - X)⁻¹) := by
        rw [mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = (cayley X * (1 - X)) * (1 - X)⁻¹ := by rw [Matrix.mul_assoc]
    _ = (U * (1 - X)) * (1 - X)⁻¹ := by rw [this]
    _ = U := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]

/-- The countable family of unit phases. -/
noncomputable def phase (m : ℕ) : ℂ := (1 + (m : ℂ) * Complex.I) / (1 - (m : ℂ) * Complex.I)

theorem one_sub_ne (m : ℕ) : (1 - (m : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem one_add_ne (m : ℕ) : (1 + (m : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem star_phase_mul (m : ℕ) : star (phase m) * phase m = 1 := by
  have h1 := one_sub_ne m
  have h2 := one_add_ne m
  have : star (phase m) = (1 - (m : ℂ) * Complex.I) / (1 + (m : ℂ) * Complex.I) := by
    simp [phase, Complex.star_def, sub_eq_add_neg]
  rw [this, phase]
  field_simp

theorem phase_injective : Function.Injective phase := by
  intro a b h
  have h1 := one_sub_ne a
  have h2 := one_sub_ne b
  rw [phase, phase, div_eq_div_iff h1 h2] at h
  have h3 : ((a : ℂ) - b) * (2 * Complex.I) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact_mod_cast sub_eq_zero.1 h4
  · simp at h4

/-- Every unitary is `phase m • cayley (skewOf A)` for some `m` and some real matrix `A`. -/
theorem unitary_chart {W : Matrix ι ι ℂ} (hW1 : W * star W = 1) :
    ∃ (m : ℕ) (A : ι → ι → ℝ), W = phase m • cayley (skewOf A) := by
  have hW2 : star W * W = 1 := mul_eq_one_comm.1 hW1
  have hfin : (spectrum ℂ W).Finite := Matrix.finite_spectrum W
  have hbad : {m : ℕ | -phase m ∈ spectrum ℂ W}.Finite := by
    refine Set.Finite.preimage (f := fun m : ℕ => -phase m) ?_ hfin
    intro a _ b _ h
    exact phase_injective (neg_injective h)
  obtain ⟨m, hm⟩ := hbad.infinite_compl.nonempty
  have hm' : -phase m ∉ spectrum ℂ W := hm
  rw [spectrum.mem_iff, not_not] at hm'
  have hDdet : (algebraMap ℂ (Matrix ι ι ℂ) (-phase m) - W).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 hm').ne_zero
  set u := phase m with hu
  set v := star u with hv
  have hvu : v * u = 1 := star_phase_mul m
  have hv0 : v ≠ 0 := left_ne_zero_of_mul_eq_one hvu
  have huv : u * v = 1 := by rw [mul_comm]; exact hvu
  set C := v • W with hC
  have hCs : star C * C = 1 := by
    rw [hC, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hW2]
    have : star v * v = 1 := by rw [hv, star_star]; exact huv
    rw [this, one_smul]
  have hCV : IsUnit (C + 1) := by
    have h3 : C + 1 = (-v) • (algebraMap ℂ (Matrix ι ι ℂ) (-u) - W) := by
      rw [Algebra.algebraMap_eq_smul_one, hC, smul_sub, smul_smul, neg_mul_neg, hvu, one_smul]
      module
    rw [Matrix.isUnit_iff_isUnit_det, h3, Matrix.det_smul, isUnit_iff_ne_zero]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 hv0)) hDdet
  obtain ⟨A, hA⟩ := cayley_surj hCs hCV
  refine ⟨m, A, ?_⟩
  rw [hA, hC, smul_smul, huv, one_smul]

end Chart2

/-! ### ED for the chart -/

section EDChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type} [Fintype ι]
  [DecidableEq ι]

theorem ED.cayley {X : E → Matrix ι ι ℂ} (hX : ED X) (hs : ∀ q, (X q)ᴴ = -X q) :
    ED fun q => cayley (X q) := by
  unfold PEqualNP.QuantumGravity.Open.L119.cayley
  refine ED.mul (ED.add (ED.const 1) hX) (ED.inv (ED.sub (ED.const 1) hX) fun q => ?_)
  exact (isUnit_det_one_sub (hs q)).ne_zero

theorem ED.ofFn_prod {l : ℕ} (F : Fin l → E → Matrix ι ι ℂ) (h : ∀ i, ED (F i)) :
    ED fun q => (List.ofFn fun i => F i q).prod := by
  induction l with
  | zero => simpa using ED.const (E := E) (1 : Matrix ι ι ℂ)
  | succ l ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact ED.mul (h 0) (ih (fun i => F i.succ) fun i => h _)

end EDChart

/-! ### Gates -/

section Gates

variable {n : ℕ}

/-- The matrix `W ⊗ 1` of `n` qubits, for a matrix `W` of the qubits in `T`. -/
def gateMat (T : Finset (Fin n)) (W : Matrix (T → Bool) (T → Bool) ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y => if ∀ i, i ∉ T → x i = y i then W (fun i => x i) (fun i => y i) else 0

theorem ed_gateMat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : Finset (Fin n))
    {W : E → Matrix (T → Bool) (T → Bool) ℂ} (hW : ED W) : ED fun q => gateMat T (W q) := by
  intro x y
  by_cases h : ∀ i, i ∉ T → x i = y i
  · have : (fun q => gateMat T (W q) x y) = fun q => W q (fun i => x i) (fun i => y i) := by
      funext q; simp only [gateMat, of_apply]; rw [if_pos h]
    rw [this]; exact hW _ _
  · have : (fun q => gateMat T (W q) x y) = fun _ => (0 : ℂ) := by
      funext q; simp only [gateMat, of_apply]; rw [if_neg h]
    rw [this]; exact differentiable_const _

/-- A unitary acting on the qubits of `T` has a unitary block `W`. -/
theorem block_unitary {T : Finset (Fin n)} {W : Matrix (T → Bool) (T → Bool) ℂ}
    {U : Matrix (Qubits n) (Qubits n) ℂ} (hU : U * star U = 1)
    (hW : ∀ x y : Qubits n,
      U x y = if ∀ i, i ∉ T → x i = y i then W (fun i => x i) (fun i => y i) else 0) :
    W * star W = 1 := by
  classical
  let ext0 : (T → Bool) → Qubits n := fun s i => if h : i ∈ T then s ⟨i, h⟩ else false
  have hres : ∀ s, (fun i : T => ext0 s i) = s := by
    intro s; funext i; simp [ext0, i.2]
  have hinj : Function.Injective ext0 := by
    intro a b h; rw [← hres a, ← hres b, h]
  have hUW : ∀ s u, U (ext0 s) (ext0 u) = W s u := by
    intro s u
    rw [hW, if_pos, hres, hres]
    intro i hi; simp [ext0, hi]
  have hzero : ∀ s z, z ∉ Finset.univ.image ext0 → U (ext0 s) z = 0 := by
    intro s z hz
    rw [hW, if_neg]
    intro h
    apply hz
    refine Finset.mem_image.2 ⟨fun i => z i, Finset.mem_univ _, ?_⟩
    funext i
    by_cases hi : i ∈ T
    · simp [ext0, hi]
    · simp [ext0, hi, ← h i hi]
  ext s t
  have key : ∀ x y : Qubits n, (U * star U) x y = ∑ z, U x z * star (U y z) := by
    intro x y; simp [Matrix.mul_apply, Matrix.star_apply]
  have h1 := key (ext0 s) (ext0 t)
  rw [hU] at h1
  have h2 : ∑ z, U (ext0 s) z * star (U (ext0 t) z) =
      ∑ u, W s u * star (W t u) := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ext0))]
    · rw [Finset.sum_image (fun a _ b _ h => hinj h)]
      simp only [hUW]
    · intro z _ hz
      rw [hzero s z hz]; simp
  have h3 : (W * star W) s t = ∑ u, W s u * star (W t u) := by
    simp [Matrix.mul_apply, Matrix.star_apply]
  rw [h3, ← h2, ← h1]
  by_cases hst : s = t
  · subst hst; simp
  · have : ext0 s ≠ ext0 t := fun h => hst (hinj h)
    simp [Matrix.one_apply, hst, this]

/-- The two-qubit index sets. -/
abbrev TT (n : ℕ) : Type := {T : Finset (Fin n) // T.card ≤ 2}

instance : Inhabited (TT n) := ⟨⟨∅, by simp⟩⟩

theorem card_le_sixteen (T : TT n) :
    Fintype.card ((T.1 → Bool) × (T.1 → Bool)) ≤ Fintype.card (Fin 16) := by
  have h2 : 2 ^ T.1.card ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) T.2
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    Fintype.card_fin]
  calc 2 ^ T.1.card * 2 ^ T.1.card ≤ 4 * 4 := Nat.mul_le_mul h2 h2
    _ = 16 := by norm_num

/-- An embedding of the `≤ 16` matrix positions of a two-qubit gate into `Fin 16`. -/
noncomputable def eT (T : TT n) : ((T.1 → Bool) × (T.1 → Bool)) ↪ Fin 16 :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (card_le_sixteen T))

/-- The real matrix of a block, from 16 parameters. -/
noncomputable def Amat (T : TT n) (a : Fin 16 → ℝ) : (T.1 → Bool) → (T.1 → Bool) → ℝ :=
  fun s t => a (eT T (s, t))

/-- The gate with chart parameters `a`, phase index `m` on the qubits `T`. -/
noncomputable def gateF (T : TT n) (m : ℕ) (a : Fin 16 → ℝ) : Matrix (Qubits n) (Qubits n) ℂ :=
  gateMat T.1 (phase m • cayley (skewOf (Amat T a)))

theorem ED_skewOf (T : TT n) : ED fun a : Fin 16 → ℝ => skewOf (Amat T a) := by
  intro i j
  simp only [skewOf, Amat, of_apply]
  have hr : ∀ f : (Fin 16 → ℝ) → ℝ, Differentiable ℝ f →
      Differentiable ℝ fun a => (f a : ℂ) := fun f hf => Complex.ofRealCLM.differentiable.comp hf
  have hc : ∀ k : Fin 16, Differentiable ℝ fun a : Fin 16 → ℝ => a k := fun k => differentiable_apply k
  have hh : ∀ f : (Fin 16 → ℝ) → ℝ, Differentiable ℝ f → Differentiable ℝ fun a => f a / 2 :=
    fun f hf => by
      have h : Differentiable ℝ fun a => f a * 2⁻¹ := hf.mul (differentiable_const (2⁻¹ : ℝ))
      simpa [div_eq_mul_inv] using h
  exact (hr _ (hh _ ((hc _).sub (hc _)))).add ((hr _ (hh _ ((hc _).add (hc _)))).mul
    (differentiable_const _))

theorem ED_gateF (T : TT n) (m : ℕ) : ED fun a : Fin 16 → ℝ => gateF T m a := by
  unfold gateF
  exact ed_gateMat _ (ED.smul _ (ED.cayley (ED_skewOf T) fun a => skewOf_conjTranspose _))

/-- Every two-qubit gate is covered by the chart. -/
theorem gate_cover {U : Matrix (Qubits n) (Qubits n) ℂ} (hU : U * star U = 1)
    (hT : ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ActsOnQubits T U) :
    ∃ (T : TT n) (m : ℕ) (a : Fin 16 → ℝ), U = gateF T m a := by
  obtain ⟨T, hT, W, hW⟩ := hT
  have hWu := block_unitary hU hW
  obtain ⟨m, A, hA⟩ := unitary_chart hWu
  let T' : TT n := ⟨T, hT⟩
  refine ⟨T', m, Function.extend (eT T') (fun st => A st.1 st.2) 0, ?_⟩
  have hAm : Amat T' (Function.extend (eT T') (fun st => A st.1 st.2) 0) = A := by
    funext s t
    exact (eT T').injective.extend_apply (fun st => A st.1 st.2) 0 (s, t)
  ext x y
  rw [hW x y]
  simp only [gateF, hAm, gateMat, of_apply, ← hA]
  rfl

end Gates

/-! ### The weaker parametrization and `L119_weak` -/

section Weak

variable (n k : ℕ)

/-- Index set: the number of gates, and for each position the qubit pair and the phase index. -/
abbrev Idx : Type := Fin (k + 1) × (Fin k → TT n × ℕ)

/-- Embedding of the first `ℓ` positions. -/
def pos (ℓ : Fin (k + 1)) : Fin ℓ.val → Fin k := Fin.castLE (Nat.lt_succ_iff.1 ℓ.2)

/-- Block `i` of the parameter vector. -/
def blk (p : Fin (k * 16) → ℝ) (i : Fin k) : Fin 16 → ℝ := fun a => p (finProdFinEquiv (i, a))

/-- The product of the gates of the index `j`. -/
noncomputable def prodM (j : Idx n k) (p : Fin (k * 16) → ℝ) : Matrix (Qubits n) (Qubits n) ℂ :=
  (List.ofFn fun i : Fin j.1.val =>
    gateF (j.2 (pos k j.1 i)).1 (j.2 (pos k j.1 i)).2 (blk k p (pos k j.1 i))).prod

theorem ED_prodM (j : Idx n k) : ED (prodM n k j) := by
  unfold prodM
  refine ED.ofFn_prod _ fun i => ?_
  refine ED.comp (ED_gateF _ _) ?_
  exact differentiable_pi.2 fun a => differentiable_apply _

/-- The weaker parametrization: countably many everywhere differentiable maps from
`ℝ^(16 k)` cover the products of at most `k` two-qubit gates. -/
theorem knillParametrization_weak :
    ∃ (J : Type) (_ : Countable J)
      (φ : J → (Fin (k * 16) → ℝ) → (Qubits n → Qubits n → ℂ)),
      (∀ j, Differentiable ℝ (φ j)) ∧
        ∀ U ∈ ReachableIn (twoQubitGates n) k, ∃ j p, φ j p = (U : Matrix (Qubits n) (Qubits n) ℂ) := by
  refine ⟨Idx n k, inferInstance, fun j p => prodM n k j p, ?_, ?_⟩
  · intro j
    exact differentiable_pi.2 fun x => differentiable_pi.2 fun y => ED_prodM n k j x y
  · intro U hU
    obtain ⟨l, hl, hS, hprod⟩ := hU
    have hc : ∀ u : qubitUnitaryGroup n, u ∈ twoQubitGates n →
        ∃ (T : TT n) (m : ℕ) (a : Fin 16 → ℝ), (u : Matrix (Qubits n) (Qubits n) ℂ) = gateF T m a :=
      fun u hu => gate_cover (Matrix.mem_unitaryGroup_iff.1 u.2) hu
    choose! Tf mf af hcov using hc
    have hℓ : l.length < k + 1 := Nat.lt_succ_of_le hl
    let q : Fin k → Fin 16 → ℝ := fun i => if h : i.val < l.length then af (l.get ⟨i, h⟩) else 0
    let tm : Fin k → TT n × ℕ := fun i =>
      if h : i.val < l.length then (Tf (l.get ⟨i, h⟩), mf (l.get ⟨i, h⟩)) else (default, 0)
    refine ⟨(⟨l.length, hℓ⟩, tm), fun t => q (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2,
      ?_⟩
    have hblk : ∀ i, blk k (fun t => q (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2) i
        = q i := by
      intro i; funext a; simp [blk]
    have hlist : (List.ofFn fun i : Fin l.length =>
        gateF (tm (pos k ⟨l.length, hℓ⟩ i)).1 (tm (pos k ⟨l.length, hℓ⟩ i)).2
          (blk k (fun t => q (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)
            (pos k ⟨l.length, hℓ⟩ i))) =
        l.map Subtype.val := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        have hi : i < l.length := by simpa using h2
        rw [List.getElem_ofFn, List.getElem_map, hblk]
        have hpos : (pos k ⟨l.length, hℓ⟩ ⟨i, by simpa using h1⟩).val = i := rfl
        have e1 : tm (pos k ⟨l.length, hℓ⟩ ⟨i, by simpa using h1⟩) =
            (Tf (l.get ⟨i, hi⟩), mf (l.get ⟨i, hi⟩)) := by
          simp only [tm, hpos, dif_pos hi]
        have e2 : q (pos k ⟨l.length, hℓ⟩ ⟨i, by simpa using h1⟩) = af (l.get ⟨i, hi⟩) := by
          simp only [q, hpos, dif_pos hi]
        rw [e1, e2, ← hcov _ (hS _ (List.get_mem _ _))]
        simp
    have hmain : prodM n k (⟨l.length, hℓ⟩, tm)
        (fun t => q (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2) =
        ((l.prod : qubitUnitaryGroup n) : Matrix (Qubits n) (Qubits n) ℂ) := by
      rw [Submonoid.coe_list_prod, ← hlist]
      rfl
    rw [hprod] at hmain
    exact hmain

end Weak

/-- The weak form of L-qg-119: the dimension count with `16` real parameters per gate. If
`16 k < 4^n`, the products of at most `k` two-qubit gates form a Haar-null set. -/
theorem L119_weak (n k : ℕ) (μ : Measure (qubitUnitaryGroup n)) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] (hlt : 16 * k < 4 ^ n) :
    μ (ReachableIn (twoQubitGates n) k) = 0 := by
  obtain ⟨J, hJ, φ, hφ, hcov⟩ := knillParametrization_weak n k
  refine haar_null_of_cover ?_ μ φ hφ _ hcov
  have : Fintype.card (Qubits n) * Fintype.card (Qubits n) = 4 ^ n := by
    simp [Qubits, ← mul_pow]
  rw [this]; omega

end PEqualNP.QuantumGravity.Open.KnillParam
