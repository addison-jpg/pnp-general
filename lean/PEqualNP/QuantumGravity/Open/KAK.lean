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
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply, hwx]

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

end PEqualNP.QuantumGravity.Open.KAK
