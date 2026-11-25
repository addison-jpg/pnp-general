import PEqualNP.QuantumGravity.Open.KnillParam15
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Seat F2: the Cartan (KAK) form of a two-qubit gate, in the shape needed for Knill's count.

`kak : W * star W = 1 → ∃ c A₁ A₂ B₁ B₂ δ, W = (A₁ ⊗ₖ A₂) * (Qm * diagonal δ * Qd) * (B₁ ⊗ₖ B₂)`
for every `4 × 4` unitary `W` (rows and columns indexed by `Bool × Bool`), with `A₁ A₂ B₁ B₂`
unitary `2 × 2` matrices and `δ` unit complex numbers. `Qm` is the magic basis (unnormalised;
`Qd` is its inverse): its columns are the quaternion units `1, i, j, k` as `2 × 2` matrices.

Route (no Lie theory):
* quaternions: left and right multiplication by a unit quaternion are local in the magic basis
  (`loc_Lq`, `loc_Rq`), and every real orthogonal `4 × 4` matrix is a product of such maps and a
  sign diagonal (`orth_loc`: move the first column to `1`, the second to `i`, then a rotation
  about `i`);
* a symmetric unitary matrix is `O diag(d) Oᵀ` with `O` real orthogonal (`symm_unitary_diag`:
  the Cayley chart of a symmetric unitary is `i` times a real symmetric matrix; real spectral
  theorem);
* for a unitary `V`, `VᵀV` is symmetric unitary, so `V = R diag(δ) Oᵀ` with `R`, `O` real
  orthogonal (`unitary_orth_diag_orth`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PEqualNP.QuantumGravity.Open.KAK

open Matrix Kronecker

/-! ### Quaternions as real `4 × 4` and complex `2 × 2` matrices -/

/-- The quaternion `p 0 + p 1 i + p 2 j + p 3 k` as a complex `2 × 2` matrix. -/
def qM (p : Fin 4 → ℝ) : Matrix Bool Bool ℂ := Matrix.of fun a b =>
  match a, b with
  | false, false => (p 0 : ℂ) + p 1 * Complex.I
  | false, true => (p 2 : ℂ) + p 3 * Complex.I
  | true, false => -(p 2 : ℂ) + p 3 * Complex.I
  | true, true => (p 0 : ℂ) - p 1 * Complex.I

/-- Left multiplication by the quaternion `p`, on coordinates. -/
def Lq (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![p 0, -p 1, -p 2, -p 3; p 1, p 0, -p 3, p 2; p 2, p 3, p 0, -p 1; p 3, -p 2, p 1, p 0]

/-- Right multiplication by the quaternion `p`, on coordinates. -/
def Rq (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![p 0, -p 1, -p 2, -p 3; p 1, p 0, p 3, -p 2; p 2, -p 3, p 0, p 1; p 3, p 2, -p 1, p 0]

/-- The squared norm of a quaternion. -/
def nsq (p : Fin 4 → ℝ) : ℝ := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2

/-- The magic basis, unnormalised: column `t` is the `t`-th quaternion unit as a `2 × 2` matrix. -/
def Qm : Matrix (Bool × Bool) (Fin 4) ℂ := Matrix.of fun ab t => qM (Pi.single t 1) ab.1 ab.2

/-- The inverse of `Qm`. -/
noncomputable def Qd : Matrix (Fin 4) (Bool × Bool) ℂ := (1 / 2 : ℂ) • Qmᴴ

theorem Qd_mul_Qm : Qd * Qm = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qd, Qm, qM, Matrix.mul_apply, Fintype.sum_prod_type, Pi.single_apply] <;> ring_nf <;>
    simp

theorem Qm_mul_Qd : Qm * Qd = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [Qd, Qm, qM, Matrix.mul_apply, Fin.sum_univ_four, Pi.single_apply] <;> ring_nf <;>
    simp <;> norm_num

theorem Lq_tr_mul (p : Fin 4 → ℝ) : (Lq p)ᵀ * Lq p = nsq p • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lq, nsq, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem Lq_mul_tr (p : Fin 4 → ℝ) : Lq p * (Lq p)ᵀ = nsq p • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lq, nsq, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem Rq_tr_mul (p : Fin 4 → ℝ) : (Rq p)ᵀ * Rq p = nsq p • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rq, nsq, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem Rq_mul_tr (p : Fin 4 → ℝ) : Rq p * (Rq p)ᵀ = nsq p • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rq, nsq, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem qM_unitary (p : Fin 4 → ℝ) (hp : nsq p = 1) : qM p * star (qM p) = 1 := by
  have h : ((p 0 : ℂ)) ^ 2 + (p 1 : ℂ) ^ 2 + (p 2 : ℂ) ^ 2 + (p 3 : ℂ) ^ 2 = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hp
    simpa [nsq] using this
  ext a b
  cases a <;> cases b <;>
    simp [qM, Matrix.mul_apply, Matrix.star_apply] <;> ring_nf <;>
    simp only [Complex.I_sq] <;> linear_combination h

theorem qM_tr_unitary (p : Fin 4 → ℝ) (hp : nsq p = 1) : (qM p)ᵀ * star (qM p)ᵀ = 1 := by
  have h : ((p 0 : ℂ)) ^ 2 + (p 1 : ℂ) ^ 2 + (p 2 : ℂ) ^ 2 + (p 3 : ℂ) ^ 2 = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hp
    simpa [nsq] using this
  ext a b
  cases a <;> cases b <;>
    simp [qM, Matrix.mul_apply, Matrix.star_apply] <;> ring_nf <;>
    simp only [Complex.I_sq] <;> linear_combination h

/-- Left multiplication by a quaternion acts on the first tensor factor. -/
theorem Qm_mul_Lq (p : Fin 4 → ℝ) :
    Qm * (Lq p).map (algebraMap ℝ ℂ) = (qM p ⊗ₖ (1 : Matrix Bool Bool ℂ)) * Qm := by
  ext ⟨a, b⟩ t
  cases a <;> cases b <;> fin_cases t <;>
    simp [Qm, qM, Lq, Matrix.mul_apply, Fin.sum_univ_four, Fintype.sum_prod_type,
      Pi.single_apply, Matrix.one_apply] <;> ring_nf <;> simp

/-- Right multiplication by a quaternion acts on the second tensor factor. -/
theorem Qm_mul_Rq (p : Fin 4 → ℝ) :
    Qm * (Rq p).map (algebraMap ℝ ℂ) = ((1 : Matrix Bool Bool ℂ) ⊗ₖ (qM p)ᵀ) * Qm := by
  ext ⟨a, b⟩ t
  cases a <;> cases b <;> fin_cases t <;>
    simp [Qm, qM, Rq, Matrix.mul_apply, Fin.sum_univ_four, Fintype.sum_prod_type,
      Pi.single_apply, Matrix.one_apply] <;> ring_nf <;> simp

/-! ### Real orthogonal matrices are local in the magic basis, up to a sign diagonal -/

/-- `O` is local in the magic basis: it is a tensor product of two unitaries there. -/
def Loc (O : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃ A B : Matrix Bool Bool ℂ, A * star A = 1 ∧ B * star B = 1 ∧
    Qm * O.map (algebraMap ℝ ℂ) = (A ⊗ₖ B) * Qm

theorem Loc.mul {O O' : Matrix (Fin 4) (Fin 4) ℝ} (h : Loc O) (h' : Loc O') : Loc (O * O') := by
  obtain ⟨A, B, hA, hB, e⟩ := h
  obtain ⟨A', B', hA', hB', e'⟩ := h'
  refine ⟨A * A', B * B', ?_, ?_, ?_⟩
  · rw [star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc A', hA', Matrix.one_mul, hA]
  · rw [star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B', hB', Matrix.one_mul, hB]
  · rw [Matrix.map_mul, ← Matrix.mul_assoc, e, Matrix.mul_assoc, e', ← Matrix.mul_assoc,
      ← Matrix.mul_kronecker_mul]

theorem loc_Lq (p : Fin 4 → ℝ) (hp : nsq p = 1) : Loc (Lq p) :=
  ⟨qM p, 1, qM_unitary p hp, by simp, Qm_mul_Lq p⟩

theorem loc_Rq (p : Fin 4 → ℝ) (hp : nsq p = 1) : Loc (Rq p) :=
  ⟨1, (qM p)ᵀ, by simp, qM_tr_unitary p hp, Qm_mul_Rq p⟩

/-- The conjugate quaternion. -/
def conjq (p : Fin 4 → ℝ) : Fin 4 → ℝ := ![p 0, -p 1, -p 2, -p 3]

theorem nsq_conjq (p : Fin 4 → ℝ) : nsq (conjq p) = nsq p := by simp [nsq, conjq]

theorem Rq_tr (p : Fin 4 → ℝ) : (Rq p)ᵀ = Rq (conjq p) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rq, conjq]

/-- Conjugation `x ↦ q x q⁻¹` by a unit quaternion. -/
def Cq (q : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := Lq q * (Rq q)ᵀ

theorem loc_Cq (q : Fin 4 → ℝ) (hq : nsq q = 1) : Loc (Cq q) := by
  unfold Cq
  rw [Rq_tr]
  exact (loc_Lq q hq).mul (loc_Rq _ (by rw [nsq_conjq, hq]))

theorem Cq_tr_mul (q : Fin 4 → ℝ) (hq : nsq q = 1) : (Cq q)ᵀ * Cq q = 1 := by
  unfold Cq
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (Lq q)ᵀ, Lq_tr_mul, hq, one_smul, Matrix.one_mul, Rq_mul_tr, hq, one_smul]

theorem Cq_mul_tr (q : Fin 4 → ℝ) (hq : nsq q = 1) : Cq q * (Cq q)ᵀ = 1 :=
  mul_eq_one_comm.1 (Cq_tr_mul q hq)

theorem Cq_col0 (q : Fin 4 → ℝ) (hq : nsq q = 1) (i : Fin 4) :
    Cq q i 0 = if i = 0 then 1 else 0 := by
  unfold nsq at hq
  fin_cases i <;> simp [Cq, Lq, Rq, Matrix.mul_apply, Fin.sum_univ_four] <;> first
    | linear_combination hq | ring

theorem Cq_col1 (q : Fin 4 → ℝ) (i : Fin 4) :
    Cq q i 1 = ![0, q 0 ^ 2 + q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2, 2 * (q 1 * q 2 + q 0 * q 3),
      2 * (q 1 * q 3 - q 0 * q 2)] i := by
  fin_cases i <;> simp [Cq, Lq, Rq, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- A unit imaginary quaternion `u` is `q i q⁻¹` for a unit quaternion `q`. -/
theorem exists_conj (u : Fin 4 → ℝ) (hu0 : u 0 = 0) (hu : nsq u = 1) :
    ∃ q : Fin 4 → ℝ, nsq q = 1 ∧ ∀ i, Cq q i 1 = u i := by
  have hu' : u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = 1 := by
    unfold nsq at hu; rw [hu0] at hu; linarith
  by_cases h1 : u 1 = -1
  · have h23 : u 2 ^ 2 + u 3 ^ 2 = 0 := by rw [h1] at hu'; linarith
    have h2 : u 2 = 0 := by nlinarith [sq_nonneg (u 2), sq_nonneg (u 3)]
    have h3 : u 3 = 0 := by nlinarith [sq_nonneg (u 2), sq_nonneg (u 3)]
    refine ⟨![0, 0, 1, 0], by simp [nsq], fun i => ?_⟩
    rw [Cq_col1]
    fin_cases i <;> simp [hu0, h1, h2, h3]
  · have hpos : 0 < 1 + u 1 := by
      have : -1 ≤ u 1 := by nlinarith [sq_nonneg (u 2), sq_nonneg (u 3)]
      rcases this.lt_or_eq with h | h
      · linarith
      · exact absurd h.symm h1
    set r : ℝ := (Real.sqrt (2 * (1 + u 1)))⁻¹ with hr
    have hr2 : r ^ 2 * (2 * (1 + u 1)) = 1 := by
      rw [hr, inv_pow, Real.sq_sqrt (by linarith)]
      exact inv_mul_cancel₀ (by linarith)
    refine ⟨![(1 + u 1) * r, 0, -u 3 * r, u 2 * r], ?_, fun i => ?_⟩
    · simp only [nsq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      linear_combination hr2 + r ^ 2 * hu'
    · rw [Cq_col1]
      fin_cases i
      · simp [hu0]
      · simp
        linear_combination u 1 * hr2 - r ^ 2 * hu'
      · simp
        linear_combination u 2 * hr2
      · simp
        linear_combination u 3 * hr2

/-- Rotation about the `i` axis by a unit quaternion `w + x i`. -/
theorem Cq_axis (w x : ℝ) :
    Cq ![w, x, 0, 0] = !![w ^ 2 + x ^ 2, 0, 0, 0; 0, w ^ 2 + x ^ 2, 0, 0;
      0, 0, w ^ 2 - x ^ 2, -(2 * w * x); 0, 0, 2 * w * x, w ^ 2 - x ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Cq, Lq, Rq, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem axis_mul (w x t a b c d : ℝ) (hwx : w ^ 2 + x ^ 2 = 1) (ha : a = w ^ 2 - x ^ 2)
    (hc : c = 2 * w * x) (hb : b = -c * t) (hd : d = a * t) :
    (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) ℝ) =
      !![w ^ 2 + x ^ 2, 0, 0, 0; 0, w ^ 2 + x ^ 2, 0, 0;
        0, 0, w ^ 2 - x ^ 2, -(2 * w * x); 0, 0, 2 * w * x, w ^ 2 - x ^ 2] *
        diagonal ![1, 1, 1, t] := by
  subst ha hc hb hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, hwx]

theorem col_of_orth {O : Matrix (Fin 4) (Fin 4) ℝ} (hO : Oᵀ * O = 1) (i j : Fin 4) :
    ∑ k, O k i * O k j = if i = j then 1 else 0 := by
  have := congrFun (congrFun hO i) j
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

/-- Every real orthogonal `4 × 4` matrix is local in the magic basis, up to one sign. -/
theorem orth_loc (O : Matrix (Fin 4) (Fin 4) ℝ) (hO : Oᵀ * O = 1) :
    ∃ (h : Matrix (Fin 4) (Fin 4) ℝ) (s : Fin 4 → ℝ), Loc h ∧ (∀ i, s i ^ 2 = 1) ∧
      O = h * diagonal s := by
  -- first column to `1`
  set p : Fin 4 → ℝ := fun i => O i 0 with hp
  have hp1 : nsq p = 1 := by
    have := col_of_orth hO 0 0
    simp only [Fin.sum_univ_four, ite_true] at this
    simp only [nsq, hp]; linarith
  set O₁ := (Lq p)ᵀ * O with hO₁
  have hOeq : O = Lq p * O₁ := by
    rw [hO₁, ← Matrix.mul_assoc, Lq_mul_tr, hp1, one_smul, Matrix.one_mul]
  have hO₁o : O₁ᵀ * O₁ = 1 := by
    rw [hO₁, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Lq p), Lq_mul_tr, hp1, one_smul, Matrix.one_mul, hO]
  have hc0 : ∀ i, O₁ i 0 = if i = 0 then 1 else 0 := by
    intro i
    unfold nsq at hp1
    fin_cases i <;> simp [hO₁, Lq, Matrix.mul_apply, Fin.sum_univ_four] <;>
      simp only [hp] at hp1 ⊢ <;> first | linear_combination hp1 | ring
  -- second column to `i`
  set u : Fin 4 → ℝ := fun i => O₁ i 1 with hu
  have hu0 : u 0 = 0 := by
    have := col_of_orth hO₁o 0 1
    simpa [Fin.sum_univ_four, hc0] using this
  have hu1 : nsq u = 1 := by
    have := col_of_orth hO₁o 1 1
    simp only [Fin.sum_univ_four, ite_true] at this
    simp only [nsq, hu]; linarith
  obtain ⟨q, hq, hqu⟩ := exists_conj u hu0 hu1
  set O₂ := (Cq q)ᵀ * O₁ with hO₂
  have hO₁eq : O₁ = Cq q * O₂ := by
    rw [hO₂, ← Matrix.mul_assoc, Cq_mul_tr q hq, Matrix.one_mul]
  have hO₂o : O₂ᵀ * O₂ = 1 := by
    rw [hO₂, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Cq q), Cq_mul_tr q hq, Matrix.one_mul, hO₁o]
  have hd0 : ∀ i, O₂ i 0 = if i = 0 then 1 else 0 := by
    intro i
    have h1 : O₂ i 0 = ∑ k, (Cq q) k i * (Cq q) k 0 := by
      simp only [hO₂, Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun k _ => by rw [hc0, Cq_col0 q hq]
    rw [h1, col_of_orth (Cq_tr_mul q hq)]
  have hd1 : ∀ i, O₂ i 1 = if i = 1 then 1 else 0 := by
    intro i
    have h1 : O₂ i 1 = ∑ k, (Cq q) k i * (Cq q) k 1 := by
      simp only [hO₂, Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun k _ => by rw [hqu]
    rw [h1, col_of_orth (Cq_tr_mul q hq)]
  -- the rest is a rotation or a reflection of the last two coordinates
  have r0 : ∀ j, O₂ 0 j = if 0 = j then 1 else 0 := by
    intro j
    have := col_of_orth hO₂o 0 j
    simpa [Fin.sum_univ_four, hd0] using this
  have r1 : ∀ j, O₂ 1 j = if 1 = j then 1 else 0 := by
    intro j
    have := col_of_orth hO₂o 1 j
    simpa [Fin.sum_univ_four, hd1] using this
  have e22 := col_of_orth hO₂o 2 2
  have e33 := col_of_orth hO₂o 3 3
  have e23 := col_of_orth hO₂o 2 3
  simp [Fin.sum_univ_four, r0, r1] at e22 e33 e23
  set a := O₂ 2 2
  set b := O₂ 2 3
  set c := O₂ 3 2
  set d := O₂ 3 3
  set t := a * d - b * c with ht
  have hb : b = -c * t := by rw [ht]; linear_combination (-b) * e22 + a * e23
  have hd : d = a * t := by rw [ht]; linear_combination (-d) * e22 + c * e23
  have ht2 : t ^ 2 = 1 := by
    have : b * b + d * d = t ^ 2 * (a * a + c * c) := by rw [hb, hd]; ring
    rw [e33, e22, mul_one] at this; exact this.symm
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((a : ℂ) + c * Complex.I) (n := 2) (by norm_num)
  have h1 := congrArg Complex.re hz
  have h2 := congrArg Complex.im hz
  simp [pow_two] at h1 h2
  set w := z.re
  set x := z.im
  have hwx : w ^ 2 + x ^ 2 = 1 := by
    have h4 : (w ^ 2 + x ^ 2) ^ 2 = 1 := by
      have : (w ^ 2 + x ^ 2) ^ 2 = a * a + c * c := by rw [← h1, ← h2]; ring
      rw [this, e22]
    have h5 : 0 ≤ w ^ 2 + x ^ 2 := by positivity
    nlinarith
  refine ⟨Lq p * (Cq q * Cq ![w, x, 0, 0]), ![1, 1, 1, t], ?_, ?_, ?_⟩
  · exact (loc_Lq p hp1).mul ((loc_Cq q hq).mul (loc_Cq _ (by simpa [nsq] using hwx)))
  · intro i; fin_cases i <;> simp [ht2]
  · have hform : O₂ = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, a, b; 0, 0, c, d] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [r0, r1, hd0, hd1] <;> rfl
    have hO₂f : O₂ = Cq ![w, x, 0, 0] * diagonal ![1, 1, 1, t] := by
      rw [hform, Cq_axis]
      exact axis_mul w x t a b c d hwx (by rw [← h1]; ring) (by rw [← h2]; ring) hb hd
    calc O = Lq p * O₁ := hOeq
      _ = Lq p * (Cq q * O₂) := by rw [← hO₁eq]
      _ = Lq p * (Cq q * (Cq ![w, x, 0, 0] * diagonal ![1, 1, 1, t])) := by rw [← hO₂f]
      _ = _ := by simp only [Matrix.mul_assoc]

/-! ### A symmetric unitary matrix is diagonalised by a real orthogonal matrix -/

section Takagi

open PEqualNP.QuantumGravity.Open.L119 PEqualNP.QuantumGravity.Open.KnillParam
  PEqualNP.QuantumGravity.Open.KnillParam15

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A real matrix as a complex matrix. -/
noncomputable abbrev cx (O : Matrix ι ι ℝ) : Matrix ι ι ℂ := O.map (algebraMap ℝ ℂ)

theorem cx_mul (A B : Matrix ι ι ℝ) : cx (A * B) = cx A * cx B := Matrix.map_mul

theorem cx_one : cx (1 : Matrix ι ι ℝ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [cx, Matrix.one_apply, h]

theorem cx_transpose (A : Matrix ι ι ℝ) : cx Aᵀ = (cx A)ᵀ := rfl

theorem star_cx (A : Matrix ι ι ℝ) : star (cx A) = (cx A)ᵀ := by
  ext i j; simp [cx, Matrix.star_apply]

theorem cx_diagonal (s : ι → ℝ) : cx (diagonal s) = diagonal fun i => (s i : ℂ) := by
  ext i j; by_cases h : i = j <;> simp [cx, h]

theorem cx_injective : Function.Injective (cx (ι := ι)) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h i) j
  simpa [cx] using this

theorem symm_unitary_diag (S : Matrix ι ι ℂ) (hS : S * star S = 1) (hsym : Sᵀ = S) :
    ∃ (O : Matrix ι ι ℝ) (d : ι → ℂ), Oᵀ * O = 1 ∧ (∀ i, d i * star (d i) = 1) ∧
      S = cx O * diagonal d * (cx O)ᵀ := by
  obtain ⟨m, A, hA⟩ := unitary_chart hS
  set X := skewOf A with hXdef
  have hX : Xᴴ = -X := skewOf_conjTranspose A
  set C := cayley X with hC
  have hCS : C = star (phase m) • S := by
    rw [hA, smul_smul, star_phase_mul, one_smul]
  have hCsym : Cᵀ = C := by rw [hCS, Matrix.transpose_smul, hsym]
  obtain ⟨hunit, hinv⟩ := cayley_inv hX
  have hdet : IsUnit (C + 1).det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  have hcomm : (C + 1) * (C - 1) = (C - 1) * (C + 1) := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one]
    abel
  have hinv' : (C - 1) * (C + 1)⁻¹ = X := by
    rw [← hinv]
    calc (C - 1) * (C + 1)⁻¹ = (C + 1)⁻¹ * ((C + 1) * (C - 1)) * (C + 1)⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul]
      _ = (C + 1)⁻¹ * (C - 1) * ((C + 1) * (C + 1)⁻¹) := by
          rw [hcomm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [mul_nonsing_inv _ hdet, Matrix.mul_one]
  have hXsym : Xᵀ = X := by
    conv_lhs => rw [← hinv]
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
      Matrix.transpose_add, Matrix.transpose_one, hCsym, hinv']
  -- `X` is `i` times a real symmetric matrix
  set H : Matrix ι ι ℝ := Matrix.of fun i j => (X i j).im with hH
  have hre : ∀ i j, (X i j).re = 0 := by
    intro i j
    have h1 := congrFun (congrFun hX i) j
    have h2 := congrFun (congrFun hXsym i) j
    simp only [conjTranspose_apply, Matrix.neg_apply, Matrix.transpose_apply] at h1 h2
    rw [h2] at h1
    have := congrArg Complex.re h1
    simp at this
    linarith
  have hXH : X = Complex.I • cx H := by
    ext i j
    apply Complex.ext <;> simp [cx, hH, hre]
  have hHh : H.IsHermitian := by
    ext i j
    have h2 := congrFun (congrFun hXsym i) j
    simp only [Matrix.transpose_apply] at h2
    simp [hH, Matrix.conjTranspose_apply, h2]
  set O : Matrix ι ι ℝ := (hHh.eigenvectorUnitary : Matrix ι ι ℝ) with hO
  have hOO : Oᵀ * O = 1 := by
    have := mem_unitaryGroup_iff'.1 hHh.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hOO' : O * Oᵀ = 1 := mul_eq_one_comm.1 hOO
  have hspec : H = O * diagonal hHh.eigenvalues * Oᵀ := by
    refine hHh.spectral_theorem.trans ?_
    simp [Unitary.conjStarAlgAut_apply, hO, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  have hU : star (cx O) * cx O = 1 := by
    rw [star_cx, ← cx_transpose, ← cx_mul, hOO, cx_one]
  have hXcj : X = cj (cx O) fun j => Complex.I * (hHh.eigenvalues j : ℂ) := by
    rw [hXH]
    conv_lhs => rw [hspec]
    rw [cx_mul, cx_mul, cx_diagonal, cx_transpose, ← star_cx]
    exact cj_smul (cx O) Complex.I fun j => (hHh.eigenvalues j : ℂ)
  have hcay : C = cj (cx O) fun j => (1 + Complex.I * (hHh.eigenvalues j : ℂ)) /
      (1 - Complex.I * (hHh.eigenvalues j : ℂ)) := by
    rw [hC, hXcj]; exact cayley_cj hU _
  set d : ι → ℂ := fun j => phase m * ((1 + Complex.I * (hHh.eigenvalues j : ℂ)) /
      (1 - Complex.I * (hHh.eigenvalues j : ℂ))) with hd
  have hSd : S = cj (cx O) d := by rw [hA, hcay, cj_smul]
  refine ⟨O, d, hOO, ?_, ?_⟩
  · have h : cj (cx O) d * cj (cx O) (fun j => star (d j)) = 1 := by
      rw [← cj_conjTranspose hU, ← hSd]; exact hS
    rw [cj_mul hU, ← cj_one hU] at h
    intro j
    exact congrFun (cj_inj hU h) j
  · rw [hSd, cj, star_cx]

/-- Every unitary is `R diag(δ) Oᵀ` with `R`, `O` real orthogonal. -/
theorem unitary_orth_diag_orth (V : Matrix ι ι ℂ) (hV : V * star V = 1) :
    ∃ (R O : Matrix ι ι ℝ) (δ : ι → ℂ), Rᵀ * R = 1 ∧ Oᵀ * O = 1 ∧
      (∀ i, δ i * star (δ i) = 1) ∧ V = cx R * diagonal δ * (cx O)ᵀ := by
  have hV' : star V * V = 1 := mul_eq_one_comm.1 hV
  obtain ⟨O, d, hOO, hd, hS⟩ := symm_unitary_diag (Vᵀ * V) (by
    rw [star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V, hV, Matrix.one_mul]
    have : Vᵀ * star Vᵀ = (star V * V)ᵀ := by
      ext i j; simp [Matrix.mul_apply, Matrix.star_apply, mul_comm]
    rw [this, hV', Matrix.transpose_one])
    (by rw [Matrix.transpose_mul, Matrix.transpose_transpose])
  have hOc : (cx O)ᵀ * cx O = 1 := by rw [← cx_transpose, ← cx_mul, hOO, cx_one]
  have hOc' : cx O * (cx O)ᵀ = 1 := mul_eq_one_comm.1 hOc
  have hex : ∀ i, ∃ z : ℂ, z ^ 2 = d i := fun i =>
    IsAlgClosed.exists_pow_nat_eq (d i) (n := 2) (by norm_num)
  choose δ hδ using hex
  have hδ1 : ∀ i, δ i * star (δ i) = 1 := by
    intro i
    have h1 : Complex.normSq (d i) = 1 := by
      have := hd i
      rw [Complex.star_def, Complex.mul_conj] at this
      exact_mod_cast this
    have h2 : Complex.normSq (δ i) ^ 2 = 1 := by rw [← map_pow, hδ, h1]
    have h3 : Complex.normSq (δ i) = 1 := by
      have := Complex.normSq_nonneg (δ i); nlinarith
    rw [Complex.star_def, Complex.mul_conj, h3]; simp
  set R' : Matrix ι ι ℂ := V * cx O * diagonal (fun i => star (δ i)) with hR'
  have hdd : diagonal (fun i => star (δ i)) * diagonal δ = (1 : Matrix ι ι ℂ) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
    rw [mul_comm]; exact hδ1 i
  have hVeq : V = R' * diagonal δ * (cx O)ᵀ := by
    rw [hR', Matrix.mul_assoc (V * cx O), hdd, Matrix.mul_one, Matrix.mul_assoc, hOc',
      Matrix.mul_one]
  have hRt : R'ᵀ * R' = 1 := by
    have : R'ᵀ * R' = diagonal (fun i => star (δ i)) * ((cx O)ᵀ * (Vᵀ * V) * cx O) *
        diagonal (fun i => star (δ i)) := by
      rw [hR']; simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [this, hS]
    have : (cx O)ᵀ * (cx O * diagonal d * (cx O)ᵀ) * cx O = diagonal d := by
      calc (cx O)ᵀ * (cx O * diagonal d * (cx O)ᵀ) * cx O
          = ((cx O)ᵀ * cx O) * diagonal d * ((cx O)ᵀ * cx O) := by simp only [Matrix.mul_assoc]
        _ = diagonal d := by rw [hOc, Matrix.one_mul, Matrix.mul_one]
    rw [this, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
    rw [← hδ i]
    have := hδ1 i
    linear_combination (δ i * star (δ i) + 1) * this
  have hRs : R' * star R' = 1 := by
    have : star R' = diagonal δ * (cx O)ᵀ * star V := by
      rw [hR', star_mul, star_mul, star_cx, Matrix.star_eq_conjTranspose (diagonal _),
        diagonal_conjTranspose, Matrix.mul_assoc]
      congr 2; funext i; simp
    rw [this, hR']
    calc V * cx O * diagonal (fun i => star (δ i)) * (diagonal δ * (cx O)ᵀ * star V)
        = V * (cx O * (diagonal (fun i => star (δ i)) * diagonal δ) * (cx O)ᵀ) * star V := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hdd, Matrix.mul_one, hOc', Matrix.mul_one, hV]
  have hreal : R'ᵀ = star R' := by
    calc R'ᵀ = R'ᵀ * (R' * star R') := by rw [hRs, Matrix.mul_one]
      _ = star R' := by rw [← Matrix.mul_assoc, hRt, Matrix.one_mul]
  set R : Matrix ι ι ℝ := Matrix.of fun i j => (R' i j).re with hR
  have hRR' : cx R = R' := by
    ext i j
    have := congrFun (congrFun hreal j) i
    simp only [Matrix.transpose_apply, Matrix.star_apply] at this
    have him : (R' i j).im = 0 := by
      have h := congrArg Complex.im this
      simp at h; linarith
    apply Complex.ext <;> simp [cx, hR, him]
  refine ⟨R, O, δ, ?_, hOO, hδ1, by rw [hRR']; exact hVeq⟩
  apply cx_injective
  rw [cx_mul, cx_transpose, hRR', hRt, cx_one]

end Takagi

/-! ### The Cartan form of a `4 × 4` unitary -/

theorem Qm_conjTranspose : Qmᴴ = (2 : ℂ) • Qd := by
  rw [Qd, smul_smul]; norm_num

/-- KAK: every `4 × 4` unitary is `(A₁ ⊗ A₂) (Qm diag(δ) Qd) (B₁ ⊗ B₂)` with unitary `2 × 2`
factors and unit `δ`. -/
theorem kak (W : Matrix (Bool × Bool) (Bool × Bool) ℂ) (hW : W * star W = 1) :
    ∃ (A₁ A₂ B₁ B₂ : Matrix Bool Bool ℂ) (δ : Fin 4 → ℂ),
      A₁ * star A₁ = 1 ∧ A₂ * star A₂ = 1 ∧ B₁ * star B₁ = 1 ∧ B₂ * star B₂ = 1 ∧
      (∀ i, δ i * star (δ i) = 1) ∧
      W = (A₁ ⊗ₖ A₂) * (Qm * diagonal δ * Qd) * (B₁ ⊗ₖ B₂) := by
  set V := Qd * W * Qm with hVdef
  have hVV : V * star V = 1 := by
    have : star V = Qd * star W * Qm := by
      rw [hVdef, Matrix.star_eq_conjTranspose, conjTranspose_mul, conjTranspose_mul,
        Qm_conjTranspose, Qd, conjTranspose_smul, conjTranspose_conjTranspose,
        Matrix.star_eq_conjTranspose]
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
      norm_num
    rw [this, hVdef]
    calc Qd * W * Qm * (Qd * star W * Qm) = Qd * (W * (Qm * Qd) * star W) * Qm := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Qm_mul_Qd, Matrix.mul_one, hW, Matrix.mul_one, Qd_mul_Qm]
  have hWV : W = Qm * V * Qd := by
    rw [hVdef]
    calc W = (Qm * Qd) * W * (Qm * Qd) := by rw [Qm_mul_Qd, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  obtain ⟨R, O, δ, hR, hO, hδ, hV⟩ := unitary_orth_diag_orth V hVV
  obtain ⟨h₁, s₁, ⟨A₁, A₂, hA₁, hA₂, e₁⟩, hs₁, hR'⟩ := orth_loc R hR
  obtain ⟨h₂, s₂, ⟨B₁, B₂, hB₁, hB₂, e₂⟩, hs₂, hO'⟩ := orth_loc O hO
  have E1 : Qm * cx R = (A₁ ⊗ₖ A₂) * Qm * diagonal (fun i => (s₁ i : ℂ)) := by
    rw [hR', cx_mul, cx_diagonal, ← Matrix.mul_assoc]
    exact congrArg (· * _) e₁
  have E2' : Qm * cx O = (B₁ ⊗ₖ B₂) * Qm * diagonal (fun i => (s₂ i : ℂ)) := by
    rw [hO', cx_mul, cx_diagonal, ← Matrix.mul_assoc]
    exact congrArg (· * _) e₂
  have E2 : (cx O)ᵀ * Qd = diagonal (fun i => (s₂ i : ℂ)) * Qd * (star B₁ ⊗ₖ star B₂) := by
    have e := congrArg conjTranspose E2'
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose,
      conjTranspose_kronecker, ← Matrix.star_eq_conjTranspose (cx O), star_cx] at e
    have hs : (star fun i => (s₂ i : ℂ)) = fun i => (s₂ i : ℂ) := by
      funext i; simp
    rw [hs] at e
    rw [Qd, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, e]
    simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
  have hs₁' : ∀ i, (s₁ i : ℂ) ^ 2 = 1 := fun i => by exact_mod_cast hs₁ i
  have hs₂' : ∀ i, (s₂ i : ℂ) ^ 2 = 1 := fun i => by exact_mod_cast hs₂ i
  refine ⟨A₁, A₂, star B₁, star B₂, fun i => s₁ i * δ i * s₂ i, hA₁, hA₂, ?_, ?_, ?_, ?_⟩
  · rw [star_star]; exact mul_eq_one_comm.1 hB₁
  · rw [star_star]; exact mul_eq_one_comm.1 hB₂
  · intro i
    have : star ((s₁ i : ℂ) * δ i * s₂ i) = s₁ i * star (δ i) * s₂ i := by simp
    rw [this]
    linear_combination ((s₁ i : ℂ) ^ 2 * (s₂ i : ℂ) ^ 2) * hδ i + (s₂ i : ℂ) ^ 2 * hs₁' i + hs₂' i
  · rw [hWV, hV]
    calc Qm * (cx R * diagonal δ * (cx O)ᵀ) * Qd
        = (Qm * cx R) * diagonal δ * ((cx O)ᵀ * Qd) := by simp only [Matrix.mul_assoc]
      _ = (A₁ ⊗ₖ A₂) * Qm * diagonal (fun i => (s₁ i : ℂ)) * diagonal δ *
            (diagonal (fun i => (s₂ i : ℂ)) * Qd * (star B₁ ⊗ₖ star B₂)) := by rw [E1, E2]
      _ = (A₁ ⊗ₖ A₂) * (Qm * (diagonal (fun i => (s₁ i : ℂ)) * diagonal δ *
            diagonal (fun i => (s₂ i : ℂ))) * Qd) * (star B₁ ⊗ₖ star B₂) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [diagonal_mul_diagonal, diagonal_mul_diagonal]

end PEqualNP.QuantumGravity.Open.KAK
