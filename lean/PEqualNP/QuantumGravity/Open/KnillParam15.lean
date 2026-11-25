import PEqualNP.QuantumGravity.Open.KnillParam
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Seat Q4 of `qg-frontier`: `L119_fifteen`, the `15 k + 1` form of `L119`.

`KnillParam.L119_weak` uses `16` real parameters per gate. Here each gate is a global-phase
multiple of a trace-zero Cayley chart gate with `15` parameters, so one global phase (one real
parameter) replaces one phase per gate, and

`L119_fifteen : 15 * k + 1 < 4 ^ n → μ (ReachableIn (twoQubitGates n) k) = 0`.

The cover lemma is `exists_trace_chart`: every unitary `W` is `exp (α i) • cayley (skewOf A)` with
`∑ A i i = 0`. Proof: spectral theorem for the Hermitian matrix of a Cayley chart of `W`, so
`W = U diag(exp (2 i ψ_j)) U⋆`; shifting the phase by `s` turns the Cayley parameters into
`tan (ψ_j - s)`, and `∑ tan (ψ_j - s) = ∑ cot (s - t_j)` has a zero between consecutive poles
(intermediate value theorem; the poles are finitely many).
-/

set_option linter.unusedSectionVars false

namespace PEqualNP.QuantumGravity.Open.KnillParam15

open Filter Topology Set

/-- `cot x = cos x / sin x`. -/
noncomputable def cotR (x : ℝ) : ℝ := Real.cos x / Real.sin x

theorem cotR_eq_tan (x : ℝ) : cotR x = Real.tan (Real.pi / 2 - x) := by
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, cotR]

theorem cotR_sub_pi (x : ℝ) : cotR (x - Real.pi) = cotR x := by
  simp [cotR, Real.cos_sub_pi, Real.sin_sub_pi, neg_div_neg_eq]

theorem cotR_neg (x : ℝ) : cotR (-x) = -cotR x := by
  simp [cotR, Real.cos_neg, Real.sin_neg, div_neg]

theorem tendsto_cotR_nhdsGT : Tendsto cotR (𝓝[>] 0) atTop := by
  have h : Tendsto (fun x : ℝ => Real.pi / 2 - x) (𝓝[>] 0) (𝓝[<] (Real.pi / 2)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Continuous fun x : ℝ => Real.pi / 2 - x := continuous_const.sub continuous_id
      simpa using this.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0:ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
  have := Real.tendsto_tan_pi_div_two.comp h
  refine this.congr fun x => ?_
  simp [cotR_eq_tan]

theorem tendsto_cotR_nhdsLT : Tendsto cotR (𝓝[<] 0) atBot := by
  have h : Tendsto (fun x : ℝ => -x) (𝓝[<] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (continuous_neg (G := ℝ)).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (0:ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
  have := (tendsto_cotR_nhdsGT.comp h)
  have h2 := (tendsto_neg_atTop_atBot.comp this)
  refine h2.congr fun x => ?_
  simp [cotR_neg]

theorem tendsto_sum_atTop {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (l : Filter ℝ)
    (h : ∀ j ∈ s, Tendsto (f j) l atTop ∨ ∃ c, Tendsto (f j) l (𝓝 c))
    (h2 : ∃ j ∈ s, Tendsto (f j) l atTop) :
    Tendsto (fun x => ∑ j ∈ s, f j x) l atTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at h2
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    by_cases hs : ∃ j ∈ s, Tendsto (f j) l atTop
    · have h1 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) hs
      rcases h a (Finset.mem_insert_self _ _) with ha' | ⟨c, hc⟩
      · exact tendsto_atTop_mono' l ((h1.eventually_ge_atTop 0).mono fun x hx => by
          simpa using hx) ha'
      · exact h1.atTop_add hc |>.congr (fun x => add_comm _ _)
    · have hfin : ∀ j ∈ s, ∃ c, Tendsto (f j) l (𝓝 c) := by
        intro j hj
        rcases h j (Finset.mem_insert_of_mem hj) with h' | h'
        · exact absurd ⟨j, hj, h'⟩ hs
        · exact h'
      choose! c hc using hfin
      have hsum : Tendsto (fun x => ∑ j ∈ s, f j x) l (𝓝 (∑ j ∈ s, c j)) :=
        tendsto_finsetSum _ hc
      obtain ⟨j, hj, hj'⟩ := h2
      have hja : j = a := by
        rcases Finset.mem_insert.1 hj with h' | h'
        · exact h'
        · exact absurd ⟨j, h', hj'⟩ hs
      subst hja
      exact hj'.atTop_add hsum


theorem sin_ne_of_mem {x : ℝ} (h1 : -Real.pi < x) (h2 : x < 0) : Real.sin x ≠ 0 :=
  (Real.sin_neg_of_neg_of_neg_pi_lt h2 h1).ne

theorem continuousAt_cotR {x : ℝ} (h : Real.sin x ≠ 0) : ContinuousAt cotR x :=
  Real.continuous_cos.continuousAt.div Real.continuous_sin.continuousAt h

theorem continuousAt_cot_sub {s c : ℝ} (h : Real.sin (s - c) ≠ 0) :
    ContinuousAt (fun x : ℝ => cotR (x - c)) s :=
  (continuousAt_cotR h).comp (f := fun x : ℝ => x - c) (by fun_prop)

theorem tendsto_sub_nhdsGT (a : ℝ) : Tendsto (fun s : ℝ => s - a) (𝓝[>] a) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h := (Continuous.tendsto (f := fun s : ℝ => s - a) (by fun_prop) a)
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx

theorem tendsto_sub_nhdsLT (b : ℝ) : Tendsto (fun s : ℝ => b - s) (𝓝[<] b) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h := (Continuous.tendsto (f := fun s : ℝ => b - s) (by fun_prop) b)
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx

/-- Between consecutive poles, a sum of cotangents has a zero. -/
theorem exists_cot_sum_zero {ι : Type*} [Fintype ι] [Nonempty ι] (t : ι → ℝ) (a : ℝ)
    (ht : ∀ j, t j ∈ Ioc a (a + Real.pi)) (hex : ∃ j, t j = a + Real.pi) :
    ∃ s, (∀ j, Real.sin (s - t j) ≠ 0) ∧ ∑ j, cotR (s - t j) = 0 := by
  classical
  obtain ⟨jb, -, hb⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι)) t
  set b := Finset.univ.inf' Finset.univ_nonempty t with hbdef
  have hjb : t jb = b := hb.symm
  have hle : ∀ j, b ≤ t j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  have hab : a < b := hjb ▸ (ht jb).1
  have hsin : ∀ s ∈ Ioo a b, ∀ j, Real.sin (s - t j) ≠ 0 := by
    intro s hs j
    refine sin_ne_of_mem ?_ ?_
    · linarith [(ht j).2, hs.1]
    · linarith [hle j, hs.2]
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = (fun s : ℝ => ∑ j, cotR (s - t j)) := ⟨_, rfl⟩
  have hcont : ContinuousOn g (Ioo a b) := by
    subst hg
    refine continuousOn_finsetSum (f := fun j s => cotR (s - t j)) Finset.univ fun j _ => ?_
    intro s hs
    exact (continuousAt_cot_sub (hsin s hs j)).continuousWithinAt
  have hA : Tendsto g (𝓝[>] a) atTop := by
    subst hg
    refine tendsto_sum_atTop Finset.univ (fun j s => cotR (s - t j)) _ ?_ ?_
    · intro j _
      by_cases hj : t j = a + Real.pi
      · left
        refine (tendsto_cotR_nhdsGT.comp (tendsto_sub_nhdsGT a)).congr fun s => ?_
        simp only [Function.comp, hj]
        rw [← cotR_sub_pi]; congr 1; ring
      · right
        have hs : Real.sin (a - t j) ≠ 0 :=
          sin_ne_of_mem (by linarith [(ht j).2, lt_of_le_of_ne (ht j).2 hj]) (by linarith [(ht j).1])
        refine ⟨cotR (a - t j), ?_⟩
        exact (continuousAt_cot_sub hs).tendsto.mono_left nhdsWithin_le_nhds
    · obtain ⟨j, hj⟩ := hex
      refine ⟨j, Finset.mem_univ _, ?_⟩
      refine (tendsto_cotR_nhdsGT.comp (tendsto_sub_nhdsGT a)).congr fun s => ?_
      simp only [Function.comp, hj]
      rw [← cotR_sub_pi]; congr 1; ring
  have hB : Tendsto g (𝓝[<] b) atBot := by
    subst hg
    have h : Tendsto (fun s : ℝ => -∑ j, cotR (s - t j)) (𝓝[<] b) atTop := by
      have : (fun s : ℝ => -∑ j, cotR (s - t j)) = fun s => ∑ j, (-cotR (s - t j)) := by
        funext s; simp [Finset.sum_neg_distrib]
      rw [this]
      refine tendsto_sum_atTop Finset.univ (fun j s => -cotR (s - t j)) _ ?_ ?_
      · intro j _
        by_cases hj : t j = b
        · left
          refine (tendsto_cotR_nhdsGT.comp (tendsto_sub_nhdsLT b)).congr fun s => ?_
          simp only [Function.comp, hj]
          rw [← cotR_neg]; congr 1; ring
        · right
          have hlt : b < t j := lt_of_le_of_ne (hle j) (Ne.symm hj)
          have hs : Real.sin (b - t j) ≠ 0 :=
            sin_ne_of_mem (by linarith [(ht j).2, (ht jb).2]) (by linarith)
          refine ⟨-cotR (b - t j), ?_⟩
          exact ((continuousAt_cot_sub hs).neg).tendsto.mono_left nhdsWithin_le_nhds
      · refine ⟨jb, Finset.mem_univ _, ?_⟩
        refine (tendsto_cotR_nhdsGT.comp (tendsto_sub_nhdsLT b)).congr fun s => ?_
        simp only [Function.comp, hjb]
        rw [← cotR_neg]; congr 1; ring
    exact (tendsto_neg_atTop_atBot.comp h).congr fun s => by simp
  have hev1 : ∀ᶠ s in 𝓝[>] a, 0 < g s := hA.eventually_gt_atTop 0
  have hev2 : ∀ᶠ s in 𝓝[<] b, g s < 0 := hB.eventually_lt_atBot 0
  have hm1 : ∀ᶠ s in 𝓝[>] a, s ∈ Ioo a b := Ioo_mem_nhdsGT hab
  have hm2 : ∀ᶠ s in 𝓝[<] b, s ∈ Ioo a b := Ioo_mem_nhdsLT hab
  obtain ⟨s1, hs1, hs1m⟩ := ((hev1.and hm1).exists)
  obtain ⟨s2, hs2, hs2m⟩ := ((hev2.and hm2).exists)
  have hsub : uIcc s1 s2 ⊆ Ioo a b := (ordConnected_Ioo).uIcc_subset hs1m hs2m
  have h0 : (0 : ℝ) ∈ uIcc (g s1) (g s2) := mem_uIcc.2 (Or.inr ⟨hs2.le, hs1.le⟩)
  obtain ⟨s, hs, hs0⟩ := intermediate_value_uIcc (hcont.mono hsub) h0
  subst hg
  exact ⟨s, hsin s (hsub hs), hs0⟩


/-! ### Conjugated diagonal matrices -/

section CJ

open Matrix PEqualNP.QuantumGravity.Open.L119 PEqualNP.QuantumGravity.Open.KnillParam

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `U D U⋆` for a diagonal `D`. -/
noncomputable def cj (U : Matrix ι ι ℂ) (f : ι → ℂ) : Matrix ι ι ℂ := U * diagonal f * star U

section
variable {U : Matrix ι ι ℂ} (hU : star U * U = 1)
include hU

theorem cj_mul (f g : ι → ℂ) : cj U f * cj U g = cj U (f * g) := by
  unfold cj
  calc U * diagonal f * star U * (U * diagonal g * star U)
      = U * diagonal f * (star U * U) * diagonal g * star U := by simp only [Matrix.mul_assoc]
    _ = U * diagonal (f * g) * star U := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]
        rfl

theorem cj_one : cj U (fun _ => 1) = 1 := by
  have h2 : U * star U = 1 := mul_eq_one_comm.1 hU
  unfold cj
  rw [show (diagonal fun _ : ι => (1 : ℂ)) = 1 from diagonal_one, Matrix.mul_one, h2]

theorem cj_add (f g : ι → ℂ) : cj U f + cj U g = cj U (f + g) := by
  unfold cj
  rw [← Matrix.add_mul, ← Matrix.mul_add]; congr 2; funext i j; by_cases h : i = j <;> simp [h]

theorem cj_sub (f g : ι → ℂ) : cj U f - cj U g = cj U (f - g) := by
  unfold cj
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]; congr 2; funext i j; by_cases h : i = j <;> simp [h]

theorem cj_conjTranspose (f : ι → ℂ) : (cj U f)ᴴ = cj U (fun j => star (f j)) := by
  unfold cj
  rw [conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
    diagonal_conjTranspose, Matrix.mul_assoc]
  rfl

theorem cj_trace (f : ι → ℂ) : (cj U f).trace = ∑ j, f j := by
  unfold cj
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, trace_diagonal]

theorem cayley_cj (y : ι → ℝ) :
    cayley (cj U fun j => Complex.I * (y j : ℂ)) =
      cj U fun j => (1 + Complex.I * (y j : ℂ)) / (1 - Complex.I * (y j : ℂ)) := by
  set X := cj U fun j => Complex.I * (y j : ℂ) with hX
  have hskew : Xᴴ = -X := by
    rw [hX, cj_conjTranspose hU]
    have : cj U (fun j => -(Complex.I * (y j : ℂ))) = -cj U fun j => Complex.I * (y j : ℂ) := by
      have h := cj_add hU (fun j => Complex.I * (y j : ℂ)) (fun j => -(Complex.I * (y j : ℂ)))
      have h0 : cj U ((fun j => Complex.I * (y j : ℂ)) + fun j => -(Complex.I * (y j : ℂ))) = 0 := by
        unfold cj
        have : ((fun j => Complex.I * (y j : ℂ)) + fun j => -(Complex.I * (y j : ℂ))) = 0 := by
          funext j; simp
        rw [this]; simp
      rw [h0] at h
      exact eq_neg_of_add_eq_zero_right h
    rw [← this]
    congr 1
    funext j
    simp [Complex.conj_ofReal]
  have h1 : (1 : Matrix ι ι ℂ) - X = cj U fun j => 1 - Complex.I * (y j : ℂ) := by
    rw [← cj_one hU, hX, cj_sub hU]; rfl
  have h2 : (1 : Matrix ι ι ℂ) + X = cj U fun j => 1 + Complex.I * (y j : ℂ) := by
    rw [← cj_one hU, hX, cj_add hU]; rfl
  have hne : ∀ j, (1 - Complex.I * (y j : ℂ)) ≠ 0 := by
    intro j h
    have := congrArg Complex.re h
    simp at this
  have hR : (cj U fun j => (1 + Complex.I * (y j : ℂ)) / (1 - Complex.I * (y j : ℂ))) *
      (1 - X) = 1 + X := by
    rw [h1, h2, cj_mul hU]
    congr 1
    funext j
    simp only [Pi.mul_apply]
    exact div_mul_cancel₀ _ (hne j)
  have hu := isUnit_det_one_sub hskew
  have key := cayley_mul_one_sub hskew
  calc cayley X = cayley X * ((1 - X) * (1 - X)⁻¹) := by
        rw [mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = (cayley X * (1 - X)) * (1 - X)⁻¹ := by rw [Matrix.mul_assoc]
    _ = _ := by
        rw [key, ← hR, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]

end

theorem cj_smul (U : Matrix ι ι ℂ) (c : ℂ) (f : ι → ℂ) :
    c • cj U f = cj U (fun j => c * f j) := by
  unfold cj
  have hd : (Matrix.diagonal fun j => c * f j) = c • Matrix.diagonal f := by
    ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h]
  rw [hd, Matrix.mul_smul, Matrix.smul_mul]

theorem cj_inj {U : Matrix ι ι ℂ} (hU : star U * U = 1) {f g : ι → ℂ} (h : cj U f = cj U g) :
    f = g := by
  have key : ∀ f : ι → ℂ, star U * cj U f * U = diagonal f := by
    intro f
    unfold cj
    calc star U * (U * diagonal f * star U) * U
        = (star U * U) * diagonal f * (star U * U) := by simp only [Matrix.mul_assoc]
      _ = diagonal f := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  have := congrArg (fun M => star U * M * U) h
  simp only [key] at this
  funext j
  have := congrFun (congrFun this j) j
  simpa using this

end CJ

/-! ### Angles -/

section Angles

theorem cayley_tan (θ : ℝ) (h : Real.cos θ ≠ 0) :
    (1 + Complex.I * (Real.tan θ : ℂ)) / (1 - Complex.I * (Real.tan θ : ℂ)) =
      Complex.exp ((2 * θ : ℝ) * Complex.I) := by
  have hc : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast h
  have e1 : Complex.exp ((θ : ℝ) * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I]; norm_cast
  have e2 : Complex.exp ((2 * θ : ℝ) * Complex.I) =
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ^ 2 := by
    rw [← e1, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hpy : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq θ
  have hP : ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I) *
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) = 1 := by
    linear_combination hpy - (Real.sin θ : ℂ) ^ 2 * Complex.I_sq
  have hd : (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hP
    exact zero_ne_one hP
  rw [e2, Real.tan_eq_sin_div_cos, Complex.ofReal_div]
  have h1 : (1 : ℂ) - Complex.I * ((Real.sin θ : ℂ) / (Real.cos θ : ℂ)) =
      ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I) / (Real.cos θ : ℂ) := by
    field_simp
  have h2 : (1 : ℂ) + Complex.I * ((Real.sin θ : ℂ) / (Real.cos θ : ℂ)) =
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) / (Real.cos θ : ℂ) := by
    field_simp
  rw [h1, h2, div_div_div_cancel_right₀ hc, div_eq_iff hd]
  linear_combination (-((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)) * hP

theorem tan_cot (ψ t s : ℝ) (k : ℤ) (h : ψ - Real.pi / 2 = t + k * Real.pi)
    (hs : Real.sin (s - t) ≠ 0) :
    Real.cos (ψ - s) ≠ 0 ∧ Real.tan (ψ - s) = cotR (s - t) := by
  have hx : ψ - s = ((t - s) + Real.pi / 2) + k * Real.pi := by linarith
  have hst : s - t = -(t - s) := by ring
  rw [hst] at hs ⊢
  rw [Real.sin_neg] at hs
  have hd : Real.sin (t - s) ≠ 0 := fun h0 => hs (by rw [h0, neg_zero])
  rw [hx]
  refine ⟨?_, ?_⟩
  · rw [Real.cos_add_int_mul_pi, Real.cos_add_pi_div_two]
    exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) (neg_ne_zero.2 hd)
  · rw [Real.tan_add_int_mul_pi, Real.tan_eq_sin_div_cos, Real.sin_add_pi_div_two,
      Real.cos_add_pi_div_two, cotR, Real.cos_neg, Real.sin_neg, div_neg]

end Angles

/-! ### A trace-zero chart up to a phase -/

section Main

open Matrix PEqualNP.QuantumGravity.Open.L119 PEqualNP.QuantumGravity.Open.KnillParam

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem trace_skewOf (A : ι → ι → ℝ) :
    (skewOf A).trace = Complex.I * ((∑ i, A i i : ℝ) : ℂ) := by
  simp only [Matrix.trace, diag_apply, skewOf, of_apply, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

/-- A spectral form of a unitary matrix. -/
theorem unitary_spectral (W : Matrix ι ι ℂ) (hW : W * star W = 1) :
    ∃ (U : Matrix ι ι ℂ) (lam : ι → ℂ), star U * U = 1 ∧ W = cj U lam := by
  obtain ⟨m, A0, hA0⟩ := unitary_chart hW
  have hX0s : (skewOf A0)ᴴ = -skewOf A0 := skewOf_conjTranspose A0
  set H : Matrix ι ι ℂ := (-Complex.I) • skewOf A0 with hH
  have hHh : H.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hH, conjTranspose_smul, hX0s]
    simp
  have hU : star (hHh.eigenvectorUnitary : Matrix ι ι ℂ) * (hHh.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    mem_unitaryGroup_iff'.1 hHh.eigenvectorUnitary.2
  have hspec := hHh.spectral_theorem
  set U : Matrix ι ι ℂ := (hHh.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  have hX0 : skewOf A0 = cj U (fun j => Complex.I * (hHh.eigenvalues j : ℂ)) := by
    have h1 : skewOf A0 = Complex.I • H := by rw [hH, smul_smul]; simp
    have hH2 : H = U * diagonal (fun j => (hHh.eigenvalues j : ℂ)) * star U := by
      refine hspec.trans ?_
      simp [Unitary.conjStarAlgAut_apply, hUdef]
      rfl
    rw [h1]
    conv_lhs => rw [hH2]
    unfold cj
    have hd : (Matrix.diagonal fun j => Complex.I * (hHh.eigenvalues j : ℂ)) =
        Complex.I • Matrix.diagonal (fun j => (hHh.eigenvalues j : ℂ)) := by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h]
    rw [hd, Matrix.mul_smul, Matrix.smul_mul]
  have hcay : cayley (skewOf A0) = cj U (fun j => (1 + Complex.I * (hHh.eigenvalues j : ℂ)) /
      (1 - Complex.I * (hHh.eigenvalues j : ℂ))) := by
    rw [hX0]; exact cayley_cj hU _
  refine ⟨U, fun j => phase m * ((1 + Complex.I * (hHh.eigenvalues j : ℂ)) /
      (1 - Complex.I * (hHh.eigenvalues j : ℂ))), hU, ?_⟩
  rw [hA0, hcay, cj_smul]

theorem cj_skew {U : Matrix ι ι ℂ} (hU : star U * U = 1) (y : ι → ℝ) :
    (cj U fun j => Complex.I * (y j : ℂ))ᴴ = -cj U fun j => Complex.I * (y j : ℂ) := by
  rw [cj_conjTranspose hU]
  have h := cj_add hU (fun j => Complex.I * (y j : ℂ)) (fun j => -(Complex.I * (y j : ℂ)))
  have h0 : cj U ((fun j => Complex.I * (y j : ℂ)) + fun j => -(Complex.I * (y j : ℂ))) = 0 := by
    unfold cj
    have : ((fun j => Complex.I * (y j : ℂ)) + fun j => -(Complex.I * (y j : ℂ))) = 0 := by
      funext j; simp
    rw [this]; simp
  rw [h0] at h
  rw [← eq_neg_of_add_eq_zero_right h]
  congr 1
  funext j
  simp [Complex.conj_ofReal]

theorem exists_trace_chart (W : Matrix ι ι ℂ) (hW : W * star W = 1) :
    ∃ (α : ℝ) (A : ι → ι → ℝ), (∑ i, A i i = 0) ∧
      W = Complex.exp ((α : ℝ) * Complex.I) • cayley (skewOf A) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun _ _ => 0, by simp, Subsingleton.elim _ _⟩
  obtain ⟨U, lam, hU, hWc⟩ := unitary_spectral W hW
  have hlam : ∀ j, lam j * star (lam j) = 1 := by
    have h : cj U lam * cj U (fun j => star (lam j)) = 1 := by
      rw [← cj_conjTranspose hU]; rw [hWc] at hW; exact hW
    rw [cj_mul hU, ← cj_one hU] at h
    intro j
    exact congrFun (cj_inj hU h) j
  have hnorm : ∀ j, ‖lam j‖ = 1 := by
    intro j
    have h1 := hlam j
    rw [Complex.star_def, Complex.mul_conj] at h1
    have h2 : Complex.normSq (lam j) = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg (lam j)]
  set ψ : ι → ℝ := fun j => Complex.arg (lam j) / 2 with hψ
  have hexp : ∀ j, lam j = Complex.exp ((2 * ψ j : ℝ) * Complex.I) := by
    intro j
    have := Complex.norm_mul_exp_arg_mul_I (lam j)
    rw [hnorm j, Complex.ofReal_one, one_mul] at this
    rw [← this]; congr 2; simp only [hψ]; push_cast; ring
  have j0 : ι := Classical.choice hι
  set a : ℝ := ψ j0 - Real.pi / 2 with ha
  set t : ι → ℝ := fun j => toIocMod Real.pi_pos a (ψ j - Real.pi / 2) with ht
  have hmem : ∀ j, t j ∈ Set.Ioc a (a + Real.pi) := fun j => toIocMod_mem_Ioc Real.pi_pos a _
  have hex : ∃ j, t j = a + Real.pi := ⟨j0, by simp only [ht, ← ha]; exact toIocMod_apply_left Real.pi_pos a⟩
  obtain ⟨s, hsin, hsum⟩ := exists_cot_sum_zero t a hmem hex
  have hk : ∀ j, ψ j - Real.pi / 2 = t j + (toIocDiv Real.pi_pos a (ψ j - Real.pi / 2) : ℤ) * Real.pi := by
    intro j
    have := self_sub_toIocMod Real.pi_pos a (ψ j - Real.pi / 2)
    rw [zsmul_eq_mul] at this
    simp only [ht]
    linarith
  have hTC := fun j => tan_cot (ψ j) (t j) s _ (hk j) (hsin j)
  set y : ι → ℝ := fun j => Real.tan (ψ j - s) with hy
  have hysum : ∑ j, y j = 0 := by
    rw [← hsum]; exact Finset.sum_congr rfl fun j _ => (hTC j).2
  have hskew := cj_skew hU y
  refine ⟨2 * s, realOf (cj U fun j => Complex.I * (y j : ℂ)), ?_, ?_⟩
  · have h1 := trace_skewOf (realOf (cj U fun j => Complex.I * (y j : ℂ)))
    rw [skewOf_realOf hskew, cj_trace hU, ← Finset.mul_sum, ← Complex.ofReal_sum, hysum] at h1
    simp at h1
    exact_mod_cast h1
  · rw [skewOf_realOf hskew, cayley_cj hU y, hWc, cj_smul]
    have : (fun j => Complex.exp (((2 * s : ℝ) : ℂ) * Complex.I) *
        ((1 + Complex.I * (y j : ℂ)) / (1 - Complex.I * (y j : ℂ)))) = lam := by
      funext j
      rw [hy, cayley_tan _ (hTC j).1, hexp j, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [this]

end Main

/-! ### The 15-parameter block -/

section Gates15

open Matrix PEqualNP.QuantumGravity PEqualNP.QuantumGravity.Open.L119
  PEqualNP.QuantumGravity.Open.KnillParam

variable {n : ℕ}

/-- The matrix positions of a block, except the corner `(0, 0)`. -/
abbrev Pos (T : TT n) : Type :=
  {p : (T.1 → Bool) × (T.1 → Bool) // p ≠ ((fun _ => false), (fun _ => false))}

theorem card_Pos_le (T : TT n) : Fintype.card (Pos T) ≤ Fintype.card (Fin 15) := by
  have h1 := card_le_sixteen T
  have h2 : Fintype.card (Pos T) < Fintype.card ((T.1 → Bool) × (T.1 → Bool)) :=
    Fintype.card_subtype_lt (p := fun x => x ≠ ((fun _ => false), (fun _ => false)))
      (x := ((fun _ => false), (fun _ => false))) (by simp)
  simp only [Fintype.card_fin] at h1 ⊢
  omega

noncomputable def eT15 (T : TT n) : Pos T ↪ Fin 15 :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (card_Pos_le T))

/-- The coordinates of a block: `0` at the corner, the parameter elsewhere. -/
noncomputable def gcoord (T : TT n) (a : Fin 15 → ℝ) (p : (T.1 → Bool) × (T.1 → Bool)) : ℝ :=
  if h : p = ((fun _ => false), (fun _ => false)) then 0 else a (eT15 T ⟨p, h⟩)

/-- The real matrix of a block with trace zero, from 15 parameters. -/
noncomputable def A15 (T : TT n) (a : Fin 15 → ℝ) : (T.1 → Bool) → (T.1 → Bool) → ℝ :=
  fun s t => gcoord T a (s, t) +
    (if s = (fun _ => false) ∧ t = (fun _ => false) then -∑ u, gcoord T a (u, u) else 0)

theorem A15_trace (T : TT n) (a : Fin 15 → ℝ) : ∑ i, A15 T a i i = 0 := by
  have h0 : gcoord T a ((fun _ => false), (fun _ => false)) = 0 := by simp [gcoord]
  simp [A15, Finset.sum_add_distrib, Finset.sum_ite_eq']

theorem A15_surj (T : TT n) (A : (T.1 → Bool) → (T.1 → Bool) → ℝ) (hA : ∑ i, A i i = 0) :
    ∃ a : Fin 15 → ℝ, A15 T a = A := by
  set a : Fin 15 → ℝ := Function.extend (eT15 T) (fun q => A q.1.1 q.1.2) 0 with ha
  refine ⟨a, ?_⟩
  have hg : ∀ p, gcoord T a p =
      if p = ((fun _ => false), (fun _ => false)) then 0 else A p.1 p.2 := by
    intro p
    unfold gcoord
    split_ifs with h
    · rfl
    · exact (eT15 T).injective.extend_apply (fun q => A q.1.1 q.1.2) 0 ⟨p, h⟩
  have hu : ∀ u : T.1 → Bool, gcoord T a (u, u) =
      A u u - if u = (fun _ => false) then A (fun _ => false) (fun _ => false) else 0 := by
    intro u
    rw [hg]
    by_cases h : u = (fun _ => false)
    · subst h; simp
    · simp [h]
  have hG : ∑ u, gcoord T a (u, u) = - A (fun _ => false) (fun _ => false) := by
    simp only [hu, Finset.sum_sub_distrib, hA]
    simp [Finset.sum_ite_eq']
  ext s t
  simp only [A15]
  rw [hG, hg]
  by_cases h : s = (fun _ => false) ∧ t = (fun _ => false)
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2; simp
  · have h' : ¬ (s, t) = ((fun _ => false), (fun _ => false)) := fun e => h (Prod.mk.inj e)
    simp [h, h']

theorem diff_gcoord (T : TT n) (p) : Differentiable ℝ fun a : Fin 15 → ℝ => gcoord T a p := by
  unfold gcoord
  by_cases h : p = ((fun _ => false), (fun _ => false))
  · simp only [h, dite_true]; exact differentiable_const _
  · simp only [h, dite_false]; exact differentiable_apply _

theorem diff_A15 (T : TT n) (s t) : Differentiable ℝ fun a : Fin 15 → ℝ => A15 T a s t := by
  unfold A15
  refine (diff_gcoord T _).add ?_
  by_cases h : s = (fun _ => false) ∧ t = (fun _ => false)
  · simp only [h, and_self, ite_true]
    have h' := Differentiable.sum (u := Finset.univ) fun u _ => diff_gcoord T (u, u)
    convert h'.neg using 1
    funext a; simp
  · simp only [h, ite_false]; exact differentiable_const _

theorem ED_skewOf' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : E → ι → ι → ℝ) (h : ∀ i j, Differentiable ℝ fun q => A q i j) :
    ED fun q => skewOf (A q) := by
  intro i j
  simp only [skewOf, of_apply]
  have hr : ∀ f : E → ℝ, Differentiable ℝ f → Differentiable ℝ fun a => (f a : ℂ) :=
    fun f hf => Complex.ofRealCLM.differentiable.comp hf
  have hh : ∀ f : E → ℝ, Differentiable ℝ f → Differentiable ℝ fun a => f a / 2 :=
    fun f hf => by
      have h : Differentiable ℝ fun a => f a * 2⁻¹ := hf.mul (differentiable_const (2⁻¹ : ℝ))
      simpa [div_eq_mul_inv] using h
  exact (hr _ (hh _ ((h i j).sub (h j i)))).add ((hr _ (hh _ ((h i j).add (h j i)))).mul
    (differentiable_const _))

/-- The gate with trace-zero chart parameters `a` on the qubits `T`. -/
noncomputable def gateF15 (T : TT n) (a : Fin 15 → ℝ) : Matrix (Qubits n) (Qubits n) ℂ :=
  gateMat T.1 (cayley (skewOf (A15 T a)))

theorem ED_gateF15 (T : TT n) : ED fun a : Fin 15 → ℝ => gateF15 T a :=
  ed_gateMat _ (ED.cayley (ED_skewOf' _ (diff_A15 T)) fun a => skewOf_conjTranspose _)

theorem gateMat_smul (T : Finset (Fin n)) (c : ℂ) (W : Matrix (T → Bool) (T → Bool) ℂ) :
    gateMat T (c • W) = c • gateMat T W := by
  ext x y
  by_cases h : ∀ i, i ∉ T → x i = y i <;> simp [gateMat, h]

/-- Every two-qubit gate is a phase times a 15-parameter gate. -/
theorem gate_cover15 {U : Matrix (Qubits n) (Qubits n) ℂ} (hU : U * star U = 1)
    (hT : ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ActsOnQubits T U) :
    ∃ (T : TT n) (α : ℝ) (a : Fin 15 → ℝ),
      U = Complex.exp ((α : ℝ) * Complex.I) • gateF15 T a := by
  obtain ⟨T, hT, W, hW⟩ := hT
  have hWu := block_unitary hU hW
  obtain ⟨α, A, hA, hWA⟩ := exists_trace_chart W hWu
  obtain ⟨a, ha⟩ := A15_surj ⟨T, hT⟩ A hA
  refine ⟨⟨T, hT⟩, α, a, ?_⟩
  have h1 : gateF15 ⟨T, hT⟩ a = gateMat T (cayley (skewOf A)) := by
    simp only [gateF15, ha]
  rw [h1, ← gateMat_smul, ← hWA]
  ext x y
  rw [hW x y]
  rfl

end Gates15

/-! ### The `15 k + 1` parametrization and `L119_fifteen` -/

section Fifteen

open MeasureTheory Matrix PEqualNP.QuantumGravity PEqualNP.QuantumGravity.Open.L119
  PEqualNP.QuantumGravity.Open.KnillParam

theorem ED.smul_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type} [Fintype ι]
    [DecidableEq ι] {c : E → ℂ} (hc : Differentiable ℝ c) {M : E → Matrix ι ι ℂ} (hM : ED M) :
    ED fun q => c q • M q := fun i j x => (hc x).mul (hM i j x)

theorem list_prod_exp_smul {α : Type*} {ι : Type} [Fintype ι] [DecidableEq ι] (l : List α)
    (r : α → ℝ) (M : α → Matrix ι ι ℂ) :
    (l.map fun u => Complex.exp ((r u : ℝ) * Complex.I) • M u).prod =
      Complex.exp (((l.map r).sum : ℝ) * Complex.I) • (l.map M).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    congr 1
    rw [← Complex.exp_add]; congr 1; push_cast; ring

variable (n k : ℕ)

/-- Index set: the number of gates, and for each position the qubit pair. -/
abbrev Idx15 : Type := Fin (k + 1) × (Fin k → TT n)

/-- Block `i` of the parameter vector. -/
def blk15 (p : Fin (k * 15 + 1) → ℝ) (i : Fin k) : Fin 15 → ℝ :=
  fun a => p (Fin.castSucc (finProdFinEquiv (i, a)))

/-- One global phase times the product of the trace-zero gates of the index `j`. -/
noncomputable def prodM15 (j : Idx15 n k) (p : Fin (k * 15 + 1) → ℝ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Complex.exp ((p (Fin.last _) : ℝ) * Complex.I) •
    (List.ofFn fun i : Fin j.1.val =>
      gateF15 (j.2 (pos k j.1 i)) (blk15 k p (pos k j.1 i))).prod

theorem ED_prodM15 (j : Idx15 n k) : ED (prodM15 n k j) := by
  unfold prodM15
  refine ED.smul_fun ?_ (ED.ofFn_prod _ fun i => ?_)
  · exact (((Complex.differentiable_exp (𝕜 := ℝ))).comp
      ((Complex.ofRealCLM.differentiable.comp (differentiable_apply _)).mul_const _))
  · refine ED.comp (ED_gateF15 _) ?_
    exact differentiable_pi.2 fun a => differentiable_apply _

theorem knillParametrization15 :
    ∃ (J : Type) (_ : Countable J)
      (φ : J → (Fin (k * 15 + 1) → ℝ) → (Qubits n → Qubits n → ℂ)),
      (∀ j, Differentiable ℝ (φ j)) ∧
        ∀ U ∈ ReachableIn (twoQubitGates n) k,
          ∃ j p, φ j p = (U : Matrix (Qubits n) (Qubits n) ℂ) := by
  refine ⟨Idx15 n k, inferInstance, fun j p => prodM15 n k j p, ?_, ?_⟩
  · intro j
    exact differentiable_pi.2 fun x => differentiable_pi.2 fun y => ED_prodM15 n k j x y
  · intro U hU
    obtain ⟨l, hl, hS, hprod⟩ := hU
    have hc : ∀ u : qubitUnitaryGroup n, u ∈ twoQubitGates n →
        ∃ (T : TT n) (α : ℝ) (a : Fin 15 → ℝ), (u : Matrix (Qubits n) (Qubits n) ℂ) =
          Complex.exp ((α : ℝ) * Complex.I) • gateF15 T a :=
      fun u hu => gate_cover15 (Matrix.mem_unitaryGroup_iff.1 u.2) hu
    choose! Tf αf af hcov using hc
    have hℓ : l.length < k + 1 := Nat.lt_succ_of_le hl
    let q : Fin k → Fin 15 → ℝ := fun i => if h : i.val < l.length then af (l.get ⟨i, h⟩) else 0
    let tm : Fin k → TT n := fun i =>
      if h : i.val < l.length then Tf (l.get ⟨i, h⟩) else default
    let θ : ℝ := (l.map αf).sum
    let pp : Fin (k * 15 + 1) → ℝ := Fin.lastCases θ
      (fun t => q (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)
    refine ⟨(⟨l.length, hℓ⟩, tm), pp, ?_⟩
    have hblk : ∀ i, blk15 k pp i = q i := by
      intro i; funext a; simp only [blk15, pp, Fin.lastCases_castSucc, Equiv.symm_apply_apply]
    have hlist : (List.ofFn fun i : Fin l.length =>
        gateF15 (tm (pos k ⟨l.length, hℓ⟩ i)) (blk15 k pp (pos k ⟨l.length, hℓ⟩ i))) =
        l.map fun u => gateF15 (Tf u) (af u) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        have hi : i < l.length := by simpa using h2
        rw [List.getElem_ofFn, List.getElem_map, hblk]
        have hpos : (pos k ⟨l.length, hℓ⟩ ⟨i, by simpa using h1⟩).val = i := rfl
        have e1 : tm (pos k ⟨l.length, hℓ⟩ ⟨i, by simpa using h1⟩) = Tf (l.get ⟨i, hi⟩) := by
          simp only [tm, hpos, dif_pos hi]
        have e2 : q (pos k ⟨l.length, hℓ⟩ ⟨i, by simpa using h1⟩) = af (l.get ⟨i, hi⟩) := by
          simp only [q, hpos, dif_pos hi]
        rw [e1, e2]
        rfl
    have hmain : prodM15 n k (⟨l.length, hℓ⟩, tm) pp =
        ((l.prod : qubitUnitaryGroup n) : Matrix (Qubits n) (Qubits n) ℂ) := by
      rw [Submonoid.coe_list_prod]
      have hmap : l.map Subtype.val = l.map fun u =>
          Complex.exp ((αf u : ℝ) * Complex.I) • gateF15 (Tf u) (af u) :=
        List.map_congr_left fun u hu => hcov _ (hS _ hu)
      rw [hmap, list_prod_exp_smul, ← hlist]
      unfold prodM15
      simp [pp, θ]
    rw [hprod] at hmain
    exact hmain

end Fifteen

/-- The `15 k + 1` form of L-qg-119: if `15 k + 1 < 4^n`, the products of at most `k`
two-qubit gates form a Haar-null set of the unitary group. -/
theorem L119_fifteen (n k : ℕ) (μ : MeasureTheory.Measure (qubitUnitaryGroup n))
    [MeasureTheory.IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (hlt : 15 * k + 1 < 4 ^ n) :
    μ (ReachableIn (twoQubitGates n) k) = 0 := by
  obtain ⟨J, hJ, φ, hφ, hcov⟩ := knillParametrization15 n k
  refine PEqualNP.QuantumGravity.Open.L119.haar_null_of_cover ?_ μ φ hφ _ hcov
  have : Fintype.card (Qubits n) * Fintype.card (Qubits n) = 4 ^ n := by
    simp [Qubits, ← mul_pow]
  rw [this]; omega

end PEqualNP.QuantumGravity.Open.KnillParam15
