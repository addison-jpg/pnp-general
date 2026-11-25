import PEqualNP.QuantumGravity.Open.KAK

/-!
Seat F2: `KnillParametrization`, hence the exact `Gap.L119` (`9 k + 3 n + 1 < 4 ^ n`).

A product of `k` two-qubit gates is `exp (i θ) • N₁ ⋯ N_k • (V₁ ⊗ ⋯ ⊗ V_n)`: each gate is put in
Cartan form `(A₁ ⊗ A₂) (Qm diag Qd) (B₁ ⊗ B₂)` (`KAK.kak`), its right factor is pushed into the
layer of single-qubit gates travelling to the right, and the layer's phases into `θ`. So `N_i`
has `3 + 3 + 3 = 9` real parameters, the final layer `3 n`, and the phase `1`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PEqualNP.QuantumGravity.Open.KAKParam

open Matrix Kronecker PEqualNP.QuantumGravity PEqualNP.QuantumGravity.Open.L119
  PEqualNP.QuantumGravity.Open.KnillParam PEqualNP.QuantumGravity.Open.KnillParam15
  PEqualNP.QuantumGravity.Open.KAK

/-! ### Layers of single-qubit matrices and two-qubit matrices on `n` qubits -/

section Layer

variable {n : ℕ}

/-- The tensor product `V 0 ⊗ ⋯ ⊗ V (n-1)` of single-qubit matrices. -/
def layer (V : Fin n → Matrix Bool Bool ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y => ∏ i, V i (x i) (y i)

theorem layer_mul (V V' : Fin n → Matrix Bool Bool ℂ) :
    layer V * layer V' = layer fun i => V i * V' i := by
  ext x y
  simp only [layer, Matrix.mul_apply, of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun z _ => Finset.prod_mul_distrib.symm

theorem layer_one : layer (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext x y
  simp only [layer, of_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem layer_smul (c : Fin n → ℂ) (V : Fin n → Matrix Bool Bool ℂ) :
    layer (fun i => c i • V i) = (∏ i, c i) • layer V := by
  ext x y
  simp [layer, Finset.prod_mul_distrib]

theorem layer_split (S : Finset (Fin n)) (V : Fin n → Matrix Bool Bool ℂ) (x y : Qubits n) :
    layer V x y = (∏ i ∈ S, V i (x i) (y i)) * ∏ i ∈ Sᶜ, V i (x i) (y i) :=
  (Finset.prod_mul_prod_compl S _).symm

theorem compl_prod_one (S : Finset (Fin n)) (V : Fin n → Matrix Bool Bool ℂ)
    (hV : ∀ i, i ∉ S → V i = 1) (x y : Qubits n) :
    ∏ i ∈ Sᶜ, V i (x i) (y i) = if ∀ i, i ∉ S → x i = y i then 1 else 0 := by
  have : ∏ i ∈ Sᶜ, V i (x i) (y i) = ∏ i ∈ Sᶜ, if x i = y i then (1 : ℂ) else 0 :=
    Finset.prod_congr rfl fun i hi => by
      rw [hV i (Finset.mem_compl.1 hi), Matrix.one_apply]
  rw [this, Finset.prod_ite_zero]
  simp

/-- The matrix `W` on the qubits `a`, `b`, tensored with the identity. -/
def twoQ (a b : Fin n) (W : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y =>
    if ∀ i, i ∉ ({a, b} : Finset (Fin n)) → x i = y i then W (x a, x b) (y a, y b) else 0

theorem twoQ_smul (a b : Fin n) (c : ℂ) (W : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    twoQ a b (c • W) = c • twoQ a b W := by
  ext x y
  by_cases h : ∀ i, i ∉ ({a, b} : Finset (Fin n)) → x i = y i <;> simp [twoQ]

theorem twoQ_of {a b : Fin n} {W : Matrix (Bool × Bool) (Bool × Bool) ℂ} {x y : Qubits n}
    (h : ∀ i, i ∉ ({a, b} : Finset (Fin n)) → x i = y i) :
    twoQ a b W x y = W (x a, x b) (y a, y b) := if_pos h

theorem twoQ_not {a b : Fin n} {W : Matrix (Bool × Bool) (Bool × Bool) ℂ} {x y : Qubits n}
    (h : ¬ ∀ i, i ∉ ({a, b} : Finset (Fin n)) → x i = y i) : twoQ a b W x y = 0 := if_neg h

/-- The basis state that agrees with `x` outside `a`, `b` and has the bits `st` there. -/
def emb (a b : Fin n) (x : Qubits n) (st : Bool × Bool) : Qubits n :=
  Function.update (Function.update x a st.1) b st.2

theorem emb_a {a b : Fin n} (hab : a ≠ b) (x : Qubits n) (st : Bool × Bool) :
    emb a b x st a = st.1 := by
  simp [emb, Function.update_of_ne hab]

theorem emb_b (a b : Fin n) (x : Qubits n) (st : Bool × Bool) : emb a b x st b = st.2 := by
  simp [emb]

theorem emb_off {a b : Fin n} (x : Qubits n) (st : Bool × Bool) {i : Fin n}
    (hi : i ∉ ({a, b} : Finset (Fin n))) : emb a b x st i = x i := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  simp [emb, Function.update_of_ne hi.1, Function.update_of_ne hi.2]

theorem sum_agree {a b : Fin n} (hab : a ≠ b) (x : Qubits n) (f : Qubits n → ℂ)
    (hf : ∀ z, ¬ (∀ i, i ∉ ({a, b} : Finset (Fin n)) → x i = z i) → f z = 0) :
    ∑ z, f z = ∑ st : Bool × Bool, f (emb a b x st) := by
  have hinj : Function.Injective (emb a b x) := by
    intro s t h
    have h1 := congrFun h a
    have h2 := congrFun h b
    rw [emb_a hab, emb_a hab] at h1
    rw [emb_b, emb_b] at h2
    exact Prod.ext h1 h2
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (emb a b x)))]
  · rw [Finset.sum_image fun s _ t _ h => hinj h]
  · intro z _ hz
    apply hf
    intro hag
    apply hz
    refine Finset.mem_image.2 ⟨(z a, z b), Finset.mem_univ _, ?_⟩
    funext i
    by_cases hb : i = b
    · subst hb; rw [emb_b]
    · by_cases ha : i = a
      · subst ha; rw [emb_a hab]
      · rw [emb_off, hag] <;> simp [ha, hb]

theorem twoQ_emb_right {a b : Fin n} (hab : a ≠ b) (W : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (x : Qubits n) (st : Bool × Bool) : twoQ a b W x (emb a b x st) = W (x a, x b) st := by
  have h : ∀ i, i ∉ ({a, b} : Finset (Fin n)) → x i = emb a b x st i :=
    fun i hi => (emb_off x st hi).symm
  rw [twoQ_of h, emb_a hab, emb_b]

theorem twoQ_emb_left {a b : Fin n} (hab : a ≠ b) (W : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (x y : Qubits n) (st : Bool × Bool) :
    twoQ a b W (emb a b x st) y =
      if ∀ i, i ∉ ({a, b} : Finset (Fin n)) → x i = y i then W st (y a, y b) else 0 := by
  have h : (∀ i, i ∉ ({a, b} : Finset (Fin n)) → emb a b x st i = y i) ↔
      ∀ i, i ∉ ({a, b} : Finset (Fin n)) → x i = y i :=
    forall_congr' fun i => imp_congr_right fun hi => by rw [emb_off x st hi]
  simp only [twoQ, of_apply, h]
  rw [emb_a hab, emb_b]

theorem twoQ_mul {a b : Fin n} (hab : a ≠ b) (W W' : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    twoQ a b W * twoQ a b W' = twoQ a b (W * W') := by
  ext x y
  rw [Matrix.mul_apply, sum_agree hab x]
  · simp only [twoQ_emb_right hab, twoQ_emb_left hab]
    by_cases h : ∀ i, i ∉ ({a, b} : Finset (Fin n)) → x i = y i
    · rw [twoQ_of h]; simp only [if_pos h, Matrix.mul_apply]
    · rw [twoQ_not h]; simp only [if_neg h, mul_zero, Finset.sum_const_zero]
  · intro z hz
    rw [twoQ_not hz, zero_mul]

/-- `A` on qubit `a`, `B` on qubit `b`, the identity elsewhere. -/
def upd2 (a b : Fin n) (A B : Matrix Bool Bool ℂ) : Fin n → Matrix Bool Bool ℂ :=
  Function.update (Function.update (fun _ => 1) a A) b B

theorem upd2_a {a b : Fin n} (hab : a ≠ b) (A B : Matrix Bool Bool ℂ) : upd2 a b A B a = A := by
  simp [upd2, Function.update_of_ne hab]

theorem upd2_b (a b : Fin n) (A B : Matrix Bool Bool ℂ) : upd2 a b A B b = B := by
  simp [upd2]

theorem upd2_off {a b : Fin n} (A B : Matrix Bool Bool ℂ) {i : Fin n}
    (hi : i ∉ ({a, b} : Finset (Fin n))) : upd2 a b A B i = 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  simp [upd2, Function.update_of_ne hi.1, Function.update_of_ne hi.2]

/-- A tensor product on the qubits `a`, `b` is a layer. -/
theorem twoQ_kronecker {a b : Fin n} (hab : a ≠ b) (A B : Matrix Bool Bool ℂ) :
    twoQ a b (A ⊗ₖ B) = layer (upd2 a b A B) := by
  ext x y
  rw [layer_split {a, b}, Finset.prod_pair hab, upd2_a hab, upd2_b,
    compl_prod_one _ _ (fun i hi => upd2_off A B hi)]
  by_cases h : ∀ i, i ∉ ({a, b} : Finset (Fin n)) → x i = y i <;>
    simp [twoQ, Matrix.kroneckerMap_apply]

theorem sum_delta_right (g : Bool × Bool → ℂ) (u v : Bool) (P : ℂ) :
    ∑ st : Bool × Bool, g st * ((1 : Matrix Bool Bool ℂ) st.1 u *
      (1 : Matrix Bool Bool ℂ) st.2 v * P) = g (u, v) * P := by
  cases u <;> cases v <;> simp [Fintype.sum_prod_type, Matrix.one_apply]

theorem sum_delta_left (g : Bool × Bool → ℂ) (u v : Bool) (P : ℂ) :
    ∑ st : Bool × Bool, ((1 : Matrix Bool Bool ℂ) u st.1 *
      (1 : Matrix Bool Bool ℂ) v st.2 * P) * g st = P * g (u, v) := by
  cases u <;> cases v <;> simp [Fintype.sum_prod_type, Matrix.one_apply]

/-- A two-qubit matrix commutes with a layer that is trivial on its qubits. -/
theorem twoQ_comm_layer {a b : Fin n} (hab : a ≠ b) (W : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (V : Fin n → Matrix Bool Bool ℂ) (ha : V a = 1) (hb : V b = 1) :
    layer V * twoQ a b W = twoQ a b W * layer V := by
  ext x y
  have hrest : ∀ st, ∏ i ∈ ({a, b} : Finset (Fin n))ᶜ, V i (emb a b x st i) (y i) =
      ∏ i ∈ ({a, b} : Finset (Fin n))ᶜ, V i (x i) (y i) := fun st =>
    Finset.prod_congr rfl fun i hi => by rw [emb_off x st (Finset.mem_compl.1 hi)]
  have hrest' : ∀ st, ∏ i ∈ ({a, b} : Finset (Fin n))ᶜ, V i (x i) (emb a b y st i) =
      ∏ i ∈ ({a, b} : Finset (Fin n))ᶜ, V i (x i) (y i) := fun st =>
    Finset.prod_congr rfl fun i hi => by rw [emb_off y st (Finset.mem_compl.1 hi)]
  have hR : (twoQ a b W * layer V) x y =
      W (x a, x b) (y a, y b) * ∏ i ∈ ({a, b} : Finset (Fin n))ᶜ, V i (x i) (y i) := by
    rw [Matrix.mul_apply, sum_agree hab x]
    · simp only [twoQ_emb_right hab, layer_split {a, b} V, Finset.prod_pair hab, emb_a hab,
        emb_b, ha, hb, hrest]
      exact sum_delta_right _ _ _ _
    · intro z hz
      rw [twoQ_not hz, zero_mul]
  have hL : (layer V * twoQ a b W) x y =
      (∏ i ∈ ({a, b} : Finset (Fin n))ᶜ, V i (x i) (y i)) * W (x a, x b) (y a, y b) := by
    rw [Matrix.mul_apply, sum_agree hab y]
    · have h1 : ∀ st, twoQ a b W (emb a b y st) y = W st (y a, y b) := by
        intro st; rw [twoQ_emb_left hab]; exact if_pos fun _ _ => rfl
      simp only [h1, layer_split {a, b} V, Finset.prod_pair hab, emb_a hab,
        emb_b, ha, hb, hrest']
      exact sum_delta_left _ _ _ _
    · intro z hz
      have : ¬ ∀ i, i ∉ ({a, b} : Finset (Fin n)) → z i = y i :=
        fun h => hz fun i hi => (h i hi).symm
      rw [twoQ_not this, mul_zero]
  rw [hL, hR, mul_comm]

end Layer

/-! ### The 9-parameter family and the Cartan form with phases removed -/

section Nine

theorem unit_exp (c : ℂ) (h : c * star c = 1) : ∃ α : ℝ, c = Complex.exp (α * Complex.I) := by
  have h1 : Complex.normSq c = 1 := by
    rw [Complex.star_def, Complex.mul_conj] at h; exact_mod_cast h
  have h2 : ‖c‖ = 1 := by
    have : ‖c‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, h1]
    nlinarith [norm_nonneg c]
  refine ⟨Complex.arg c, ?_⟩
  have := Complex.norm_mul_exp_arg_mul_I c
  rw [h2] at this
  simpa using this.symm

/-- A real `2 × 2` matrix of trace zero, from three parameters. -/
def A3 (x y z : ℝ) : Bool → Bool → ℝ := fun s t =>
  match s, t with
  | false, false => x
  | false, true => y
  | true, false => z
  | true, true => -x

/-- The 3-parameter chart of the `2 × 2` unitaries up to phase. -/
noncomputable def C3 (q : Fin 3 → ℝ) : Matrix Bool Bool ℂ :=
  cayley (skewOf (A3 (q 0) (q 1) (q 2)))

theorem C3_unitary (q : Fin 3 → ℝ) : C3 q * star (C3 q) = 1 :=
  Matrix.mem_unitaryGroup_iff.1 (cayley_mem_unitaryGroup (skewOf_conjTranspose _))

theorem unitary_C3 (W : Matrix Bool Bool ℂ) (hW : W * star W = 1) :
    ∃ (α : ℝ) (q : Fin 3 → ℝ), W = Complex.exp (α * Complex.I) • C3 q := by
  obtain ⟨α, A, hA, hWA⟩ := exists_trace_chart W hW
  refine ⟨α, ![A false false, A false true, A true false], ?_⟩
  have h : A3 (A false false) (A false true) (A true false) = A := by
    rw [Fintype.sum_bool] at hA
    funext s t
    cases s <;> cases t <;> simp only [A3]
    linarith
  rw [hWA, C3]
  simp [h]

/-- The diagonal part: three phases. -/
noncomputable def dg (p : Fin 9 → ℝ) : Fin 4 → ℂ :=
  ![Complex.exp (p 6 * Complex.I), Complex.exp (p 7 * Complex.I), Complex.exp (p 8 * Complex.I), 1]

/-- The 9-parameter family of two-qubit matrices: `(C ⊗ C') (Qm diag Qd)`. -/
noncomputable def N9 (p : Fin 9 → ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (C3 ![p 0, p 1, p 2] ⊗ₖ C3 ![p 3, p 4, p 5]) * (Qm * diagonal (dg p) * Qd)

/-- Every `4 × 4` unitary is a phase times `N9 p` times a tensor product of unitaries. -/
theorem kak9 (W : Matrix (Bool × Bool) (Bool × Bool) ℂ) (hW : W * star W = 1) :
    ∃ (α : ℝ) (p : Fin 9 → ℝ) (B₁ B₂ : Matrix Bool Bool ℂ), B₁ * star B₁ = 1 ∧
      B₂ * star B₂ = 1 ∧ W = Complex.exp (α * Complex.I) • (N9 p * (B₁ ⊗ₖ B₂)) := by
  obtain ⟨A₁, A₂, B₁, B₂, δ, hA₁, hA₂, hB₁, hB₂, hδ, hWeq⟩ := kak W hW
  obtain ⟨α₁, q₁, h₁⟩ := unitary_C3 A₁ hA₁
  obtain ⟨α₂, q₂, h₂⟩ := unitary_C3 A₂ hA₂
  choose θ hθ using fun i => unit_exp (δ i) (hδ i)
  refine ⟨α₁ + α₂ + θ 3,
    ![q₁ 0, q₁ 1, q₁ 2, q₂ 0, q₂ 1, q₂ 2, θ 0 - θ 3, θ 1 - θ 3, θ 2 - θ 3], B₁, B₂, hB₁, hB₂, ?_⟩
  have hq₁ : (![q₁ 0, q₁ 1, q₁ 2] : Fin 3 → ℝ) = q₁ := by funext i; fin_cases i <;> rfl
  have hq₂ : (![q₂ 0, q₂ 1, q₂ 2] : Fin 3 → ℝ) = q₂ := by funext i; fin_cases i <;> rfl
  have hN : N9 ![q₁ 0, q₁ 1, q₁ 2, q₂ 0, q₂ 1, q₂ 2, θ 0 - θ 3, θ 1 - θ 3, θ 2 - θ 3] =
      (C3 q₁ ⊗ₖ C3 q₂) * (Qm * diagonal ![Complex.exp ((θ 0 - θ 3 : ℝ) * Complex.I),
        Complex.exp ((θ 1 - θ 3 : ℝ) * Complex.I), Complex.exp ((θ 2 - θ 3 : ℝ) * Complex.I), 1]
        * Qd) := by
    conv_rhs => rw [← hq₁, ← hq₂]
    rfl
  have hd : diagonal δ = Complex.exp (θ 3 * Complex.I) •
      diagonal ![Complex.exp ((θ 0 - θ 3 : ℝ) * Complex.I),
        Complex.exp ((θ 1 - θ 3 : ℝ) * Complex.I), Complex.exp ((θ 2 - θ 3 : ℝ) * Complex.I), 1] := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    fin_cases i <;> simp [hθ, ← Complex.exp_add] <;> ring_nf
  rw [hN, hWeq, h₁, h₂, hd]
  simp only [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← Complex.exp_add]
  congr 2
  push_cast; ring

end Nine

/-! ### Gates as layers and two-qubit matrices; absorbing a layer -/

section Gate

variable {n : ℕ}

/-- A family of unitary single-qubit matrices. -/
def Uy (V : Fin n → Matrix Bool Bool ℂ) : Prop := ∀ i, V i * star (V i) = 1

theorem Uy.mul {V V' : Fin n → Matrix Bool Bool ℂ} (h : Uy V) (h' : Uy V') :
    Uy fun i => V i * V' i := fun i => by
  rw [star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (V' i), h' i, Matrix.one_mul, h i]

theorem Uy.update {V : Fin n → Matrix Bool Bool ℂ} (h : Uy V) (i : Fin n)
    {W : Matrix Bool Bool ℂ} (hW : W * star W = 1) : Uy (Function.update V i W) := fun j => by
  by_cases hj : j = i
  · subst hj; simpa using hW
  · simpa [Function.update_of_ne hj] using h j

theorem uy_one : Uy (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) := fun _ => by simp

theorem uy_upd2 (a b : Fin n) {A B : Matrix Bool Bool ℂ} (hA : A * star A = 1)
    (hB : B * star B = 1) : Uy (upd2 a b A B) := (uy_one.update a hA).update b hB

/-- The bits of two qubits, as a state of the pair. -/
def dec {a b : Fin n} (hab : a ≠ b) : Bool × Bool ≃ (({a, b} : Finset (Fin n)) → Bool) where
  toFun u i := if i.1 = a then u.1 else u.2
  invFun s := (s ⟨a, by simp⟩, s ⟨b, by simp⟩)
  left_inv u := by ext <;> simp [hab.symm]
  right_inv s := by
    funext ⟨i, hi⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [hab.symm]

theorem gate_two {a b : Fin n} (hab : a ≠ b) {U : Matrix (Qubits n) (Qubits n) ℂ}
    (hU : U * star U = 1) (h : ActsOnQubits {a, b} U) :
    ∃ W : Matrix (Bool × Bool) (Bool × Bool) ℂ, W * star W = 1 ∧ U = twoQ a b W := by
  obtain ⟨W₀, hW₀⟩ := h
  have hu := block_unitary hU hW₀
  refine ⟨W₀.submatrix (dec hab) (dec hab), ?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose, hu, Matrix.submatrix_one_equiv]
  · have hd : ∀ x : Qubits n, dec hab (x a, x b) = fun i : ({a, b} : Finset (Fin n)) => x i := by
      intro x
      funext ⟨i, hi⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp [dec, hab.symm]
    ext x y
    rw [hW₀ x y]
    simp only [twoQ, of_apply, submatrix_apply, hd]

theorem gate_one (i : Fin n) {U : Matrix (Qubits n) (Qubits n) ℂ}
    (hU : U * star U = 1) (h : ActsOnQubits {i} U) :
    ∃ W : Matrix Bool Bool ℂ, W * star W = 1 ∧
      U = layer (Function.update (fun _ => 1) i W) := by
  obtain ⟨W₀, hW₀⟩ := h
  have hu := block_unitary hU hW₀
  let d1 : Bool ≃ (({i} : Finset (Fin n)) → Bool) :=
    { toFun := fun s _ => s
      invFun := fun f => f ⟨i, by simp⟩
      left_inv := fun s => rfl
      right_inv := fun f => by
        funext ⟨j, hj⟩
        have : j = i := by simpa using hj
        subst this; rfl }
  refine ⟨W₀.submatrix d1 d1, ?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose, hu, Matrix.submatrix_one_equiv]
  · have hd : ∀ x : Qubits n, d1 (x i) = fun j : ({i} : Finset (Fin n)) => x j := by
      intro x
      funext ⟨j, hj⟩
      have : j = i := by simpa using hj
      subst this; rfl
    ext x y
    rw [hW₀ x y, layer_split {i}, Finset.prod_singleton, Function.update_self,
      compl_prod_one {i} _ (fun j hj => Function.update_of_ne (by simpa using hj) _ _)]
    simp only [submatrix_apply, hd]
    by_cases hxy : ∀ j, j ∉ ({i} : Finset (Fin n)) → x j = y j
    · rw [if_pos hxy, if_pos hxy, mul_one]
    · rw [if_neg hxy, if_neg hxy, mul_zero]

theorem gate_zero {U : Matrix (Qubits n) (Qubits n) ℂ}
    (hU : U * star U = 1) (h : ActsOnQubits ∅ U) :
    ∃ c : ℂ, c * star c = 1 ∧ U = c • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
  obtain ⟨W₀, hW₀⟩ := h
  have hu := block_unitary hU hW₀
  have hsub : ∀ f g : ((∅ : Finset (Fin n)) → Bool), f = g :=
    fun f g => funext fun i => absurd i.2 (Finset.notMem_empty _)
  set d : ((∅ : Finset (Fin n)) → Bool) := fun _ => false
  refine ⟨W₀ d d, ?_, ?_⟩
  · have := congrFun (congrFun hu d) d
    rw [Matrix.mul_apply, Finset.sum_eq_single d (fun s _ hs => absurd (hsub s d) hs)
      (fun h => absurd (Finset.mem_univ d) h)] at this
    simpa [Matrix.star_apply] using this
  · ext x y
    rw [hW₀ x y, hsub (fun i => x i) d, hsub (fun i => y i) d]
    by_cases hxy : x = y
    · subst hxy; simp
    · have : ¬ ∀ i, i ∉ (∅ : Finset (Fin n)) → x i = y i :=
        fun h => hxy (funext fun i => h i (Finset.notMem_empty _))
      rw [if_neg this]; simp [hxy]

/-- The parametrised gate of an index: nothing, or `N9 p` on a pair of qubits. -/
noncomputable def gM (j : Option (Fin n × Fin n)) (p : Fin 9 → ℝ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  match j with
  | none => 1
  | some ab => twoQ ab.1 ab.2 (N9 p)

/-- A layer followed by a two-qubit gate is a phase, a parametrised gate and a layer. -/
theorem gate_absorb {U : Matrix (Qubits n) (Qubits n) ℂ} (hU : U * star U = 1)
    (hT : ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ActsOnQubits T U)
    (V : Fin n → Matrix Bool Bool ℂ) (hV : Uy V) :
    ∃ (j : Option (Fin n × Fin n)) (p : Fin 9 → ℝ) (α : ℝ) (V' : Fin n → Matrix Bool Bool ℂ),
      Uy V' ∧ layer V * U = Complex.exp (α * Complex.I) • (gM j p * layer V') := by
  obtain ⟨T, hc, hact⟩ := hT
  have h012 : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
  rcases h012 with h0 | h1 | h2
  · rw [Finset.card_eq_zero] at h0
    subst h0
    obtain ⟨c, hc1, rfl⟩ := gate_zero hU hact
    obtain ⟨α, rfl⟩ := unit_exp c hc1
    exact ⟨none, 0, α, V, hV, by simp [gM]⟩
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h1
    obtain ⟨W, hW, rfl⟩ := gate_one i hU hact
    exact ⟨none, 0, 0, _, hV.mul (uy_one.update i hW), by simp [gM, layer_mul]⟩
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h2
    obtain ⟨W, hW, rfl⟩ := gate_two hab hU hact
    set V₀ := Function.update (Function.update V a 1) b 1 with hV₀
    have hV₀u : Uy V₀ := (hV.update a (by simp)).update b (by simp)
    have hV₀a : V₀ a = 1 := by simp [hV₀, Function.update_of_ne hab]
    have hV₀b : V₀ b = 1 := by simp [hV₀]
    have hsplit : layer V = layer V₀ * twoQ a b (V a ⊗ₖ V b) := by
      rw [twoQ_kronecker hab, layer_mul]
      congr 1
      funext i
      by_cases hb : i = b
      · subst hb; rw [hV₀b, upd2_b, Matrix.one_mul]
      · by_cases ha : i = a
        · subst ha; rw [hV₀a, upd2_a hab, Matrix.one_mul]
        · rw [upd2_off _ _ (by simp [ha, hb]), Matrix.mul_one, hV₀, Function.update_of_ne hb,
            Function.update_of_ne ha]
    have hX : ((V a ⊗ₖ V b) * W) * star ((V a ⊗ₖ V b) * W) = 1 := by
      rw [star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc W, hW, Matrix.one_mul,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, hV a, hV b,
        Matrix.one_kronecker_one]
    obtain ⟨α, p, B₁, B₂, hB₁, hB₂, hK⟩ := kak9 _ hX
    refine ⟨some (a, b), p, α, fun i => V₀ i * upd2 a b B₁ B₂ i,
      hV₀u.mul (uy_upd2 a b hB₁ hB₂), ?_⟩
    calc layer V * twoQ a b W = layer V₀ * (twoQ a b (V a ⊗ₖ V b) * twoQ a b W) := by
          rw [hsplit, Matrix.mul_assoc]
      _ = layer V₀ * twoQ a b (Complex.exp (α * Complex.I) • (N9 p * (B₁ ⊗ₖ B₂))) := by
          rw [twoQ_mul hab, hK]
      _ = Complex.exp (α * Complex.I) •
            (layer V₀ * twoQ a b (N9 p) * layer (upd2 a b B₁ B₂)) := by
          rw [twoQ_smul, ← twoQ_mul hab, twoQ_kronecker hab, Matrix.mul_smul, Matrix.mul_assoc]
      _ = Complex.exp (α * Complex.I) •
            (twoQ a b (N9 p) * layer V₀ * layer (upd2 a b B₁ B₂)) := by
          rw [twoQ_comm_layer hab _ V₀ hV₀a hV₀b]
      _ = _ := by rw [Matrix.mul_assoc, layer_mul]; rfl

end Gate

/-! ### Products of gates -/

section Absorb

variable {n : ℕ}

/-- A layer followed by gates is a phase, the parametrised gates and one layer. -/
theorem list_absorb (l : List (Matrix (Qubits n) (Qubits n) ℂ))
    (hl : ∀ G ∈ l, G * star G = 1 ∧ ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ActsOnQubits T G) :
    ∀ V : Fin n → Matrix Bool Bool ℂ, Uy V →
      ∃ (ms : List (Option (Fin n × Fin n) × (Fin 9 → ℝ))) (α : ℝ)
        (V' : Fin n → Matrix Bool Bool ℂ), ms.length = l.length ∧ Uy V' ∧
        layer V * l.prod =
          Complex.exp (α * Complex.I) • ((ms.map fun m => gM m.1 m.2).prod * layer V') := by
  induction l with
  | nil => intro V hV; exact ⟨[], 0, V, rfl, hV, by simp⟩
  | cons G l ih =>
    intro V hV
    obtain ⟨j, p, α₁, V₁, hV₁, e₁⟩ :=
      gate_absorb (hl G List.mem_cons_self).1 (hl G List.mem_cons_self).2 V hV
    obtain ⟨ms, α₂, V₂, hlen, hV₂, e₂⟩ :=
      ih (fun G' h => hl G' (List.mem_cons_of_mem _ h)) V₁ hV₁
    refine ⟨(j, p) :: ms, α₁ + α₂, V₂, by simp [hlen], hV₂, ?_⟩
    rw [List.prod_cons, ← Matrix.mul_assoc, e₁, Matrix.smul_mul, Matrix.mul_assoc, e₂]
    simp only [List.map_cons, List.prod_cons, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
      ← Complex.exp_add]
    congr 2
    push_cast; ring

end Absorb

/-! ### Differentiability -/

section Diff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem ED_C3 : ED fun q : Fin 3 → ℝ => C3 q := by
  unfold C3
  refine ED.cayley (ED_skewOf' _ fun s t => ?_) fun q => skewOf_conjTranspose _
  cases s <;> cases t <;> simp only [A3]
  · exact differentiable_apply _
  · exact differentiable_apply _
  · exact differentiable_apply _
  · exact (differentiable_apply (0 : Fin 3)).neg

theorem ED_kron {A B : E → Matrix Bool Bool ℂ} (hA : ED A) (hB : ED B) :
    ED fun q => A q ⊗ₖ B q := fun i j => by
  simp only [Matrix.kroneckerMap_apply]
  exact (hA _ _).mul (hB _ _)

theorem diff_exp_coord (i : Fin 9) :
    Differentiable ℝ fun p : Fin 9 → ℝ => Complex.exp ((p i : ℂ) * Complex.I) :=
  (Complex.differentiable_exp (𝕜 := ℝ)).comp
    ((Complex.ofRealCLM.differentiable.comp (differentiable_apply i)).mul_const _)

theorem diff_dg (t : Fin 4) : Differentiable ℝ fun p : Fin 9 → ℝ => dg p t := by
  fin_cases t
  · exact diff_exp_coord 6
  · exact diff_exp_coord 7
  · exact diff_exp_coord 8
  · exact differentiable_const _

theorem ED_N9 : ED fun p : Fin 9 → ℝ => N9 p := by
  unfold N9
  refine ED.mul (ED_kron (ED.comp ED_C3 ?_) (ED.comp ED_C3 ?_)) ?_
  · refine differentiable_pi.2 fun i => ?_
    fin_cases i
    · exact differentiable_apply (0 : Fin 9)
    · exact differentiable_apply (1 : Fin 9)
    · exact differentiable_apply (2 : Fin 9)
  · refine differentiable_pi.2 fun i => ?_
    fin_cases i
    · exact differentiable_apply (3 : Fin 9)
    · exact differentiable_apply (4 : Fin 9)
    · exact differentiable_apply (5 : Fin 9)
  · intro u v
    have h : ∀ t ∈ (Finset.univ : Finset (Fin 4)),
        Differentiable ℝ (fun p : Fin 9 → ℝ => Qm u t * dg p t * Qd t v) := fun t _ =>
      ((differentiable_const _).mul (diff_dg t)).mul (differentiable_const _)
    have h' := Differentiable.sum h
    convert h' using 1
    funext p
    show (Qm * diagonal (dg p) * Qd) u v = _
    rw [Matrix.mul_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun t _ => by rw [Matrix.mul_diagonal]

theorem ED_twoQ (a b : Fin n) {W : E → Matrix (Bool × Bool) (Bool × Bool) ℂ} (hW : ED W) :
    ED fun q => twoQ a b (W q) := by
  intro x y
  by_cases h : ∀ i, i ∉ ({a, b} : Finset (Fin n)) → x i = y i
  · have : (fun q => twoQ a b (W q) x y) = fun q => W q (x a, x b) (y a, y b) := by
      funext q; exact twoQ_of h
    rw [this]; exact hW _ _
  · have : (fun q => twoQ a b (W q) x y) = fun _ => (0 : ℂ) := by
      funext q; exact twoQ_not h
    rw [this]; exact differentiable_const _

theorem ED_gM (j : Option (Fin n × Fin n)) : ED fun p : Fin 9 → ℝ => gM j p := by
  cases j with
  | none => exact ED.const 1
  | some ab => exact ED_twoQ ab.1 ab.2 ED_N9

theorem ED_layer {V : E → Fin n → Matrix Bool Bool ℂ} (h : ∀ i, ED fun q => V q i) :
    ED fun q => layer (V q) := fun x y =>
  diff_prod Finset.univ fun i _ => h i _ _

end Diff

/-! ### `KnillParametrization` and the exact `L119` -/

section Final

variable (n k : ℕ)

/-- The parameters of gate `i`. -/
def blk9 (p : Fin (9 * k + 3 * n + 1) → ℝ) (i : Fin k) : Fin 9 → ℝ :=
  fun r => p ⟨9 * i.val + r.val, by have := i.2; have := r.2; omega⟩

/-- The parameters of the final single-qubit matrix on qubit `i`. -/
def blk3 (p : Fin (9 * k + 3 * n + 1) → ℝ) (i : Fin n) : Fin 3 → ℝ :=
  fun r => p ⟨9 * k + 3 * i.val + r.val, by have := i.2; have := r.2; omega⟩

/-- The global phase. -/
def lastp (p : Fin (9 * k + 3 * n + 1) → ℝ) : ℝ := p ⟨9 * k + 3 * n, by omega⟩

/-- Index set: the number of gates, and for each position nothing or a pair of qubits. -/
abbrev IdxK : Type := Fin (k + 1) × (Fin k → Option (Fin n × Fin n))

/-- A global phase, the parametrised gates of the index `j`, and one layer. -/
noncomputable def prodK (j : IdxK n k) (p : Fin (9 * k + 3 * n + 1) → ℝ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Complex.exp ((lastp n k p : ℝ) * Complex.I) •
    ((List.ofFn fun i : Fin j.1.val =>
      gM (j.2 (pos k j.1 i)) (blk9 n k p (pos k j.1 i))).prod *
      layer fun i => C3 (blk3 n k p i))

theorem ED_prodK (j : IdxK n k) : ED (prodK n k j) := by
  unfold prodK
  refine ED.smul_fun ?_ (ED.mul (ED.ofFn_prod _ fun i => ?_) (ED_layer fun i => ?_))
  · exact (Complex.differentiable_exp (𝕜 := ℝ)).comp
      ((Complex.ofRealCLM.differentiable.comp (differentiable_apply _)).mul_const _)
  · exact ED.comp (ED_gM _) (differentiable_pi.2 fun a => differentiable_apply _)
  · exact ED.comp ED_C3 (differentiable_pi.2 fun a => differentiable_apply _)

/-- Knill's parametrization: countably many everywhere differentiable maps from
`ℝ^(9 k + 3 n + 1)` cover the products of at most `k` two-qubit gates. -/
theorem knillParametrization : KnillParametrization := by
  intro n k
  refine ⟨IdxK n k, inferInstance, fun j p => prodK n k j p, ?_, ?_⟩
  · intro j
    exact differentiable_pi.2 fun x => differentiable_pi.2 fun y => ED_prodK n k j x y
  · intro U hU
    obtain ⟨l, hl, hS, hprod⟩ := hU
    obtain ⟨ms, α, V', hlen, hV', e⟩ := list_absorb (l.map Subtype.val) (by
      intro G hG
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hG
      exact ⟨Matrix.mem_unitaryGroup_iff.1 u.2, hS u hu⟩) (fun _ => 1) uy_one
    rw [layer_one, Matrix.one_mul] at e
    choose β q3 hq3 using fun i => unitary_C3 (V' i) (hV' i)
    have hL : layer V' = Complex.exp ((∑ i, β i : ℝ) * Complex.I) • layer fun i => C3 (q3 i) := by
      have : V' = fun i => Complex.exp (β i * Complex.I) • C3 (q3 i) := funext hq3
      rw [this, layer_smul, ← Complex.exp_sum]
      congr 2
      push_cast; rw [Finset.sum_mul]
    have hlen' : ms.length ≤ k := by rw [hlen, List.length_map]; exact hl
    have hℓ : ms.length < k + 1 := Nat.lt_succ_of_le hlen'
    let q9 : Fin k → Fin 9 → ℝ := fun i => if h : i.val < ms.length then (ms.get ⟨i, h⟩).2 else 0
    let tm : Fin k → Option (Fin n × Fin n) := fun i =>
      if h : i.val < ms.length then (ms.get ⟨i, h⟩).1 else none
    let pp : Fin (9 * k + 3 * n + 1) → ℝ := fun t =>
      if h : t.val < 9 * k then q9 ⟨t.val / 9, by omega⟩ ⟨t.val % 9, by omega⟩
      else if h2 : t.val < 9 * k + 3 * n then
        q3 ⟨(t.val - 9 * k) / 3, by omega⟩ ⟨(t.val - 9 * k) % 3, by omega⟩
      else α + ∑ i, β i
    refine ⟨(⟨ms.length, hℓ⟩, tm), pp, ?_⟩
    have hblk9 : ∀ i, blk9 n k pp i = q9 i := by
      intro i; funext r
      have h1 := i.2
      have h2 := r.2
      simp only [blk9, pp]
      rw [dif_pos (by omega)]
      exact congrArg₂ q9 (Fin.ext (by show (9 * i.val + r.val) / 9 = i.val; omega))
        (Fin.ext (by show (9 * i.val + r.val) % 9 = r.val; omega))
    have hblk3 : ∀ i, blk3 n k pp i = q3 i := by
      intro i; funext r
      have h1 := i.2
      have h2 := r.2
      simp only [blk3, pp]
      rw [dif_neg (by omega), dif_pos (by omega)]
      exact congrArg₂ q3 (Fin.ext (by show (9 * k + 3 * i.val + r.val - 9 * k) / 3 = i.val; omega))
        (Fin.ext (by show (9 * k + 3 * i.val + r.val - 9 * k) % 3 = r.val; omega))
    have hlast : lastp n k pp = α + ∑ i, β i := by
      simp only [lastp, pp]
      rw [dif_neg (by omega), dif_neg (by omega)]
    have hlist : (List.ofFn fun i : Fin ms.length =>
        gM (tm (pos k ⟨ms.length, hℓ⟩ i)) (blk9 n k pp (pos k ⟨ms.length, hℓ⟩ i))) =
        ms.map fun m => gM m.1 m.2 := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        have hi : i < ms.length := by simpa using h2
        rw [List.getElem_ofFn, List.getElem_map, hblk9]
        have hpos : (pos k ⟨ms.length, hℓ⟩ ⟨i, by simpa using h1⟩).val = i := rfl
        have e1 : tm (pos k ⟨ms.length, hℓ⟩ ⟨i, by simpa using h1⟩) = (ms.get ⟨i, hi⟩).1 := by
          simp only [tm, hpos, dif_pos hi]
        have e2 : q9 (pos k ⟨ms.length, hℓ⟩ ⟨i, by simpa using h1⟩) = (ms.get ⟨i, hi⟩).2 := by
          simp only [q9, hpos, dif_pos hi]
        rw [e1, e2]
        rfl
    have hmain : prodK n k (⟨ms.length, hℓ⟩, tm) pp =
        ((l.prod : qubitUnitaryGroup n) : Matrix (Qubits n) (Qubits n) ℂ) := by
      rw [Submonoid.coe_list_prod, e, hL]
      unfold prodK
      simp only [hlist, hlast, hblk3, Matrix.mul_smul, smul_smul, ← Complex.exp_add]
      congr 2
      push_cast; ring
    rw [hprod] at hmain
    exact hmain

end Final

/-- L-qg-119 in its exact form: if `9 k + 3 n + 1 < 4^n`, the products of at most `k` two-qubit
gates form a Haar-null set of the unitary group. -/
theorem L119 : Gap.L119 := L119_of_knillParametrization knillParametrization

end PEqualNP.QuantumGravity.Open.KAKParam

/-! Axiom check: `#print axioms PEqualNP.QuantumGravity.Open.KAKParam.L119` gives
`propext`, `Classical.choice`, `Quot.sound`. -/
