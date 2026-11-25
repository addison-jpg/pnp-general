import Mathlib

/-!
# Hairy ball theorem: Milnor's analytic proof, the two elementary pieces

J. Milnor, "Analytic proofs of the 'hairy ball theorem' and the Brouwer fixed
point theorem", Amer. Math. Monthly 85 (1978) 521–524.

Milnor: extend a smooth unit tangent field `v` on `S^{n-1}` homogeneously, so
`⟪v x, x⟫ = 0` and `‖v x‖ = ‖x‖`. Then `f_t x = x + t • v x` maps the sphere of
radius `r` into the sphere of radius `r √(1+t²)` (`norm_add_smul_of_tangent`,
checked below). For small `t`, `f_t` is a bijection of an annulus onto the
scaled annulus (the step NOT formalized here), so by change of variables the
volume `(1+t²)^{n/2} · vol(A)` is a polynomial in `t`. For `n` odd this is
impossible (`not_polynomial_sqrt_pow_of_odd`, checked below): that is the
contradiction giving the hairy ball theorem on even-dimensional spheres.
-/

open Polynomial

namespace HairyBall

/-- Milnor's norm identity: a tangent vector of the same length rotates the
sphere of radius `‖x‖` onto the sphere of radius `‖x‖ √(1+t²)`. -/
theorem norm_add_smul_of_tangent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x w : E) (t : ℝ) (horth : inner ℝ x w = 0) (hnorm : ‖w‖ = ‖x‖) :
    ‖x + t • w‖ = ‖x‖ * Real.sqrt (1 + t ^ 2) := by
  have hsq : ‖x + t • w‖ ^ 2 = (‖x‖ * Real.sqrt (1 + t ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), @norm_add_sq_real, inner_smul_right, horth,
      norm_smul, mul_pow, hnorm, Real.norm_eq_abs, sq_abs]
    ring
  have h1 : 0 ≤ ‖x‖ * Real.sqrt (1 + t ^ 2) := by positivity
  exact (sq_eq_sq₀ (norm_nonneg _) h1).mp hsq

/-- Polynomial core: for `n` odd, `(1+X²)^n` is not the square of a real polynomial. -/
theorem sq_ne_one_add_X_sq_pow_of_odd (n : ℕ) (hn : Odd n) (p : ℝ[X]) :
    p ^ 2 ≠ (1 + X ^ 2) ^ n := by
  intro h
  have hC : (p.map (algebraMap ℝ ℂ)) ^ 2 = (X - C Complex.I) ^ n * (X - C (-Complex.I)) ^ n := by
    have := congrArg (Polynomial.map (algebraMap ℝ ℂ)) h
    simp only [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X] at this
    rw [this, ← mul_pow]
    congr 1
    have : (X - C Complex.I) * (X - C (-Complex.I)) = X ^ 2 - C (Complex.I ^ 2) := by
      simp only [C_neg, sub_neg_eq_add, C_pow]; ring
    rw [this, Complex.I_sq, C_neg, C_1]; ring
  have hne : (X - C Complex.I) ^ n * (X - C (-Complex.I)) ^ n ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) (pow_ne_zero _ (X_sub_C_ne_zero _))
  have hq : p.map (algebraMap ℝ ℂ) ≠ 0 := by
    intro h0; rw [h0, zero_pow two_ne_zero] at hC; exact hne hC.symm
  have hL : rootMultiplicity Complex.I ((p.map (algebraMap ℝ ℂ)) ^ 2)
      = 2 * rootMultiplicity Complex.I (p.map (algebraMap ℝ ℂ)) := by
    rw [sq, rootMultiplicity_mul (mul_ne_zero hq hq)]; ring
  have hR : rootMultiplicity Complex.I ((X - C Complex.I) ^ n * (X - C (-Complex.I)) ^ n) = n := by
    rw [rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_pow,
      rootMultiplicity_eq_zero]
    · simp
    · intro hr
      have := (Polynomial.IsRoot.def.mp hr)
      simp only [eval_pow, eval_sub, eval_X, eval_C, sub_neg_eq_add] at this
      have h2 : Complex.I + Complex.I ≠ 0 := by
        rw [← two_mul]; exact mul_ne_zero two_ne_zero Complex.I_ne_zero
      exact h2 (pow_eq_zero_iff (by rintro rfl; simp at hn) |>.mp this)
  rw [hC, hR] at hL
  obtain ⟨k, hk⟩ := hn
  omega

/-- Milnor's contradiction: for `n` odd, `(√(1+t²))^n = (1+t²)^{n/2}` agrees with no
real polynomial on any interval `(-ε, ε)`. -/
theorem not_polynomial_sqrt_pow_of_odd (n : ℕ) (hn : Odd n) (ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ p : ℝ[X], ∀ t : ℝ, |t| < ε → p.eval t = Real.sqrt (1 + t ^ 2) ^ n := by
  rintro ⟨p, hp⟩
  apply sq_ne_one_add_X_sq_pow_of_odd n hn p
  rw [← sub_eq_zero]
  apply eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono _ (Set.Ioo_infinite (neg_lt_self hε))
  intro t ht
  have ht' : |t| < ε := abs_lt.mpr ht
  simp only [Set.mem_ofPred_eq, IsRoot.def, eval_sub, eval_pow, eval_add, eval_one, eval_X,
    hp t ht']
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by positivity), sub_self]

/-- The case of `S²` (`n = 3`): `(1+t²)^{3/2}` is not a polynomial near `0`. -/
theorem not_polynomial_sqrt_pow_three (ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ p : ℝ[X], ∀ t : ℝ, |t| < ε → p.eval t = Real.sqrt (1 + t ^ 2) ^ 3 :=
  not_polynomial_sqrt_pow_of_odd 3 ⟨1, rfl⟩ ε hε

end HairyBall
