import PEqualNP.QuantumGravity.Open.L119

/-!
Seat C5 of `open-qg`: L-qg-115, the Haar measure of an operator norm ball, with `C = 4`.

The proof averages over the Cayley chart of seat C2 (`Open/L119.lean`),
`A ↦ cayley (skewOf A) = (1 + X)(1 - X)⁻¹` with `X = skewOf A` skew-Hermitian, restricted to
the body `K = {A | ‖skewOf A‖ ≤ 1}` of real matrices (operator norm). Write `m` for the measure
of a ball of radius `ε`; by left invariance it does not depend on the centre.

* The chart expands distances by at most a factor `2` on `K` (`norm_sub_le_cayley`): from
  `(1 - X)(c X - c Y)(1 - Y) = 2 (X - Y)` and `‖1 - X‖ ≤ 2`.
* Fubini on `{(h, A) | ‖c A - h‖ ≤ ε}` for `μ × vol|K`: one order gives `m · vol K`; in the
  other, each slice `{A ∈ K | ‖c A - h‖ ≤ ε}` lies in a translate of `{B | ‖skewOf B‖ ≤ 4 ε}
  = 4 ε • K`, of volume `(4 ε)^d vol K` with `d = (card ι)^2`.
* So `m ≤ (4 ε)^d`, and `d = 4^n` on `n` qubits. No packing and no density are needed, and
  the constant does not depend on the dimension because the comparison body is the operator
  norm ball itself.
-/

namespace PEqualNP.QuantumGravity.Open.L115

open MeasureTheory Module Matrix PEqualNP.QuantumGravity.Open.L119
open scoped Matrix.Norms.L2Operator Pointwise

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem skewOf_sub (A B : ι → ι → ℝ) : skewOf (A - B) = skewOf A - skewOf B := by
  ext i j; apply Complex.ext <;> simp [skewOf] <;> ring

theorem skewOf_smul (r : ℝ) (A : ι → ι → ℝ) : skewOf (r • A) = (r : ℂ) • skewOf A := by
  ext i j; apply Complex.ext <;> simp [skewOf] <;> ring

theorem skewOf_zero : skewOf (0 : ι → ι → ℝ) = 0 := by
  ext i j; simp [skewOf]

/-- The left form of `cayley_mul_one_sub`. -/
theorem one_sub_mul_cayley {X : Matrix ι ι ℂ} (hX : Xᴴ = -X) :
    (1 - X) * cayley X = 1 + X := by
  have hcomm : (1 - X) * (1 + X) = (1 + X) * (1 - X) := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]; abel
  rw [cayley, ← Matrix.mul_assoc, hcomm, Matrix.mul_assoc,
    mul_nonsing_inv _ (isUnit_det_one_sub hX), Matrix.mul_one]

/-- The identity behind the Lipschitz bound of the inverse chart. -/
theorem cayley_sub_identity {X Y : Matrix ι ι ℂ} (hX : Xᴴ = -X) (hY : Yᴴ = -Y) :
    (1 - X) * (cayley X - cayley Y) * (1 - Y) = (2 : ℂ) • (X - Y) := by
  have h1 := one_sub_mul_cayley hX
  have h2 := cayley_mul_one_sub hY
  have e1 : (1 - X) * (cayley X - cayley Y) * (1 - Y) =
      ((1 - X) * cayley X) * (1 - Y) - (1 - X) * (cayley Y * (1 - Y)) := by
    noncomm_ring
  rw [e1, h1, h2, two_smul]
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one]
  abel

/-- On the body `‖X‖, ‖Y‖ ≤ 1`, the inverse Cayley chart is `2`-Lipschitz. -/
theorem norm_sub_le_cayley [Nonempty ι] {X Y : Matrix ι ι ℂ} (hX : Xᴴ = -X) (hY : Yᴴ = -Y)
    (hXn : ‖X‖ ≤ 1) (hYn : ‖Y‖ ≤ 1) : ‖X - Y‖ ≤ 2 * ‖cayley X - cayley Y‖ := by
  have key := cayley_sub_identity hX hY
  have hn : ‖(2 : ℂ) • (X - Y)‖ = 2 * ‖X - Y‖ := by rw [norm_smul]; norm_num
  have hX1 : ‖1 - X‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hY1 : ‖1 - Y‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have : 2 * ‖X - Y‖ ≤ 2 * ‖cayley X - cayley Y‖ * 2 := by
    rw [← hn, ← key]
    calc ‖(1 - X) * (cayley X - cayley Y) * (1 - Y)‖
        ≤ ‖1 - X‖ * ‖cayley X - cayley Y‖ * ‖1 - Y‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 2 * ‖cayley X - cayley Y‖ * 2 := by gcongr
  nlinarith [norm_nonneg (cayley X - cayley Y)]

/-- The comparison body: real matrices whose skew-Hermitian matrix has operator norm `≤ 1`. -/
def body : Set (ι → ι → ℝ) := {A | ‖skewOf A‖ ≤ 1}

theorem continuous_norm_skewOf : Continuous fun A : ι → ι → ℝ => ‖skewOf A‖ :=
  continuous_norm.comp continuous_skewOf

theorem isClosed_body : IsClosed (body (ι := ι)) :=
  isClosed_le continuous_norm_skewOf continuous_const

theorem zero_mem_body : (0 : ι → ι → ℝ) ∈ body := by
  simp [body, skewOf_zero]

theorem volume_body_pos : 0 < (volume : Measure (ι → ι → ℝ)) body := by
  have hO : IsOpen {A : ι → ι → ℝ | ‖skewOf A‖ < 1} :=
    isOpen_lt continuous_norm_skewOf continuous_const
  refine lt_of_lt_of_le (hO.measure_pos volume ⟨0, by simp [skewOf_zero]⟩) ?_
  exact measure_mono fun A (hA : ‖skewOf A‖ < 1) => show ‖skewOf A‖ ≤ 1 from hA.le

theorem continuous_realOf : Continuous (realOf (ι := ι)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [realOf, LinearMap.coe_mk, AddHom.coe_mk]
  exact (Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply i))).add
    (Complex.continuous_im.comp ((continuous_apply j).comp (continuous_apply i)))

theorem volume_body_lt_top : (volume : Measure (ι → ι → ℝ)) body < ⊤ := by
  have : ProperSpace (Matrix ι ι ℂ) := FiniteDimensional.proper ℂ _
  have hc : IsCompact (realOf '' Metric.closedBall (0 : Matrix ι ι ℂ) 1) :=
    (isCompact_closedBall _ _).image continuous_realOf
  refine lt_of_le_of_lt (measure_mono ?_) hc.measure_lt_top
  intro A hA
  exact ⟨skewOf A, by simpa [body] using hA, realOf_skewOf A⟩

/-- Scaled bodies: `{B | ‖skewOf B‖ ≤ t} ⊆ t • body` for `t ≥ 0`. -/
theorem sublevel_subset_smul {t : ℝ} (ht : 0 ≤ t) :
    {B : ι → ι → ℝ | ‖skewOf B‖ ≤ t} ⊆ t • body (ι := ι) := by
  intro B hB
  rcases ht.eq_or_lt with rfl | ht
  · have h0 : skewOf B = 0 := norm_le_zero_iff.1 hB
    have : B = 0 := by rw [← realOf_skewOf B, h0, map_zero]
    exact ⟨0, zero_mem_body, by simp [this]⟩
  · refine ⟨t⁻¹ • B, ?_, by simp only; rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]⟩
    simp only [body, Set.mem_ofPred_eq, skewOf_smul, norm_smul]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    calc t⁻¹ * ‖skewOf B‖ ≤ t⁻¹ * t := by gcongr; exact hB
      _ = 1 := inv_mul_cancel₀ ht.ne'

theorem finrank_eq : finrank ℝ (ι → ι → ℝ) = Fintype.card ι * Fintype.card ι := by
  simp [Module.finrank_pi_fintype]

theorem volume_sublevel_le {t : ℝ} (ht : 0 ≤ t) :
    (volume : Measure (ι → ι → ℝ)) {B | ‖skewOf B‖ ≤ t} ≤
      ENNReal.ofReal (t ^ (Fintype.card ι * Fintype.card ι)) * volume (body (ι := ι)) := by
  refine (measure_mono (sublevel_subset_smul ht)).trans ?_
  rw [Measure.addHaar_smul, finrank_eq, abs_of_nonneg (pow_nonneg ht _)]

/-- Left invariance moves the centre of a ball. -/
theorem ball_eq_preimage (g V : Matrix.unitaryGroup ι ℂ) (ε : ℝ) :
    {h : Matrix.unitaryGroup ι ℂ | ‖((g * V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) - h‖ ≤ ε} =
      (fun h => g⁻¹ * h) ⁻¹' {h | ‖(V : Matrix ι ι ℂ) - h‖ ≤ ε} := by
  ext h
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  have : ((g * V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) - h =
      (g : Matrix ι ι ℂ) * ((V : Matrix ι ι ℂ) - ((g⁻¹ * h : Matrix.unitaryGroup ι ℂ) :
        Matrix ι ι ℂ)) := by
    rw [Matrix.mul_sub, ← Submonoid.coe_mul, ← Submonoid.coe_mul, mul_inv_cancel_left]
  rw [this, CStarRing.norm_coe_unitary_mul]

theorem ball_measure_eq (μ : Measure (Matrix.unitaryGroup ι ℂ)) [μ.IsMulLeftInvariant]
    (g V : Matrix.unitaryGroup ι ℂ) (ε : ℝ) :
    μ {h | ‖(g : Matrix ι ι ℂ) - h‖ ≤ ε} = μ {h | ‖(V : Matrix ι ι ℂ) - h‖ ≤ ε} := by
  have := ball_eq_preimage (g * V⁻¹) V ε
  rw [inv_mul_cancel_right] at this
  rw [this, measure_preimage_mul]

/-- The Haar small-ball bound on `U(ι)`: radius `ε` balls have measure at most
`(4 ε)^((card ι)^2)`. -/
theorem ball_le [Nonempty ι] (μ : Measure (Matrix.unitaryGroup ι ℂ)) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] (V : Matrix.unitaryGroup ι ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ {h | ‖(V : Matrix ι ι ℂ) - h‖ ≤ ε} ≤
      ENNReal.ofReal ((4 * ε) ^ (Fintype.card ι * Fintype.card ι)) := by
  set d := Fintype.card ι * Fintype.card ι
  set m := μ {h | ‖(V : Matrix ι ι ℂ) - h‖ ≤ ε}
  set ν : Measure (ι → ι → ℝ) := volume.restrict body
  set S : Set (Matrix.unitaryGroup ι ℂ × (ι → ι → ℝ)) :=
    {p | ‖((cayleyU p.2 : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) - p.1‖ ≤ ε}
  have hSm : MeasurableSet S := by
    have hc : Continuous fun p : Matrix.unitaryGroup ι ℂ × (ι → ι → ℝ) =>
        ‖((cayleyU p.2 : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) - p.1‖ :=
      continuous_norm.comp ((continuous_subtype_val.comp (continuous_cayleyU.comp continuous_snd)).sub
        (continuous_subtype_val.comp continuous_fst))
    exact (isClosed_le hc continuous_const).measurableSet
  have hbodym : MeasurableSet (body (ι := ι)) := isClosed_body.measurableSet
  have hνuniv : ν Set.univ = volume (body (ι := ι)) := Measure.restrict_apply_univ _
  -- first order: every slice over `A` is a ball, of measure `m`
  have h1 : μ.prod ν S = m * volume (body (ι := ι)) := by
    rw [Measure.prod_apply_symm hSm]
    have : ∀ A : ι → ι → ℝ, μ ((fun x => (x, A)) ⁻¹' S) = m := fun A =>
      ball_measure_eq μ (cayleyU A) V ε
    simp only [this, lintegral_const, hνuniv]
  -- second order: every slice over `h` lies in a translate of `4 ε • body`
  have hslice : ∀ h : Matrix.unitaryGroup ι ℂ, ν (Prod.mk h ⁻¹' S) ≤
      ENNReal.ofReal ((4 * ε) ^ d) * volume (body (ι := ι)) := by
    intro h
    rw [Measure.restrict_apply' hbodym]
    rcases (Prod.mk h ⁻¹' S ∩ body).eq_empty_or_nonempty with he | ⟨A₀, hA₀S, hA₀K⟩
    · rw [he, measure_empty]; exact zero_le
    refine (measure_mono (t := (fun A => A + -A₀) ⁻¹' {B | ‖skewOf B‖ ≤ 4 * ε}) ?_).trans ?_
    · rintro A ⟨hAS, hAK⟩
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← sub_eq_add_neg, skewOf_sub]
      simp only [Set.mem_preimage, S, Set.mem_ofPred_eq, cayleyU] at hAS hA₀S
      have hlip := norm_sub_le_cayley (skewOf_conjTranspose A) (skewOf_conjTranspose A₀) hAK hA₀K
      have htri : ‖cayley (skewOf A) - cayley (skewOf A₀)‖ ≤ 2 * ε := by
        have := norm_sub_le (cayley (skewOf A) - (h : Matrix ι ι ℂ))
          (cayley (skewOf A₀) - (h : Matrix ι ι ℂ))
        rw [sub_sub_sub_cancel_right] at this
        linarith
      linarith
    · rw [measure_preimage_add_right]
      exact volume_sublevel_le (by positivity)
  have h2 : μ.prod ν S ≤ ENNReal.ofReal ((4 * ε) ^ d) * volume (body (ι := ι)) := by
    rw [Measure.prod_apply hSm]
    calc ∫⁻ h, ν (Prod.mk h ⁻¹' S) ∂μ ≤ ∫⁻ _h, ENNReal.ofReal ((4 * ε) ^ d) * volume (body (ι := ι)) ∂μ :=
          lintegral_mono hslice
      _ = ENNReal.ofReal ((4 * ε) ^ d) * volume (body (ι := ι)) := by simp
  rw [h1] at h2
  exact (ENNReal.mul_le_mul_iff_left volume_body_pos.ne' volume_body_lt_top.ne).1 h2

/-- L-qg-115, with `C = 4`. -/
theorem haar_small_ball : Gap.L115 := by
  refine ⟨4, by norm_num, fun n μ _ _ V ε hε => ?_⟩
  have hcard : Fintype.card (Qubits n) * Fintype.card (Qubits n) = 4 ^ n := by
    simp [Qubits, ← mul_pow]
  have := ball_le μ V hε
  rw [hcard] at this
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) this

end PEqualNP.QuantumGravity.Open.L115
