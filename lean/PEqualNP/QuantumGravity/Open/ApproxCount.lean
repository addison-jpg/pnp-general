import PEqualNP.QuantumGravity.Open.GateNet

/-!
Seat Q2 of `qg-frontier`, rank 1c: Knill's count for the continuous two-qubit gate set. The
unitaries within `ε` of a product of `k` two-qubit gates have Haar measure at most
`((n+1)^2 (C (k+1) / ε)^32 + 1)^k (c ε)^(4^n)`. A finite net of the two-qubit gates at scale
`δ = ε / (k+1)` (`GateNet.twoQubitGates_net`) compiles the gates with total error at most `ε`
(L-qg-113), and the finite-gate-set count (L-qg-116, from the Haar small ball L-qg-115) finishes.
-/

namespace PEqualNP.QuantumGravity.Open.ApproxCount

open PEqualNP.QuantumGravity MeasureTheory

theorem approx_count_twoQubit : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (n k : ℕ) (μ : Measure (qubitUnitaryGroup n)) [IsProbabilityMeasure μ]
      [μ.IsMulLeftInvariant] (ε : ℝ), 0 < ε → ε ≤ 1 →
      μ.real (ApproxReachableIn (twoQubitGates n) k ε) ≤
        (((n : ℝ) + 1) ^ 2 * (C * ((k : ℝ) + 1) / ε) ^ 32 + 1) ^ k * (c * ε) ^ (4 ^ n) := by
  obtain ⟨C1, hC1, hnet⟩ := GateNet.twoQubitGates_net
  obtain ⟨C2, hC2, hL116⟩ := Helpers.knill_of_ball Open.L115.haar_small_ball
  refine ⟨C1, 2 * C2, by linarith, by positivity, fun n k μ _ _ ε hε hε1 => ?_⟩
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / ((k : ℝ) + 1) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδε : δ ≤ ε := by
    rw [hδdef, div_le_iff₀ hk]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  obtain ⟨N, hNsub, hNcard, hNcov⟩ := hnet n δ hδ (hδε.trans hε1)
  have hT : ∀ g ∈ twoQubitGates n,
      g ∈ ApproxReachableIn (↑N : Set (qubitUnitaryGroup n)) 1 δ := by
    intro g hg
    obtain ⟨h, hh, hd⟩ := hNcov g hg
    refine ⟨h, ?_, hd⟩
    simpa using Helpers.word_mem_reachableIn (S := (↑N : Set (qubitUnitaryGroup n)))
      (l := [h]) (by simpa using hh)
  have hsub : ApproxReachableIn (twoQubitGates n) k ε ⊆
      ApproxReachableIn (↑N : Set (qubitUnitaryGroup n)) k (2 * ε) := by
    refine (Helpers.approx_compile hδ.le hT).trans ?_
    refine Helpers.approx_mono (by simp) ?_
    have : (k : ℝ) * δ ≤ ε := by
      rw [hδdef, mul_div_assoc', div_le_iff₀ hk]; nlinarith
    linarith
  have h1 := hL116 n μ N k (2 * ε) (by positivity)
  have hCd : C1 / δ = C1 * ((k : ℝ) + 1) / ε := by
    rw [hδdef]; field_simp
  rw [hCd] at hNcard
  calc μ.real (ApproxReachableIn (twoQubitGates n) k ε)
      ≤ μ.real (ApproxReachableIn (↑N : Set (qubitUnitaryGroup n)) k (2 * ε)) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ((N.card : ℝ) + 1) ^ k * (C2 * (2 * ε)) ^ (4 ^ n) := h1
    _ ≤ _ := by
        have e : C2 * (2 * ε) = 2 * C2 * ε := by ring
        rw [e]
        gcongr
