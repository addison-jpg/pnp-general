import PEqualNP.QuantumGravity.Gaps
import PEqualNP.QuantumGravity.Helpers.GateWords
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix

/-!
Helpers for L-qg-110 to L-qg-118: the operator norm of unitaries, errors that add along a
circuit, the countability of gate words, the compactness of the unitary group and its Haar
probability measure, and the union bound behind the quantum counting bound.
-/

namespace PEqualNP.QuantumGravity.Helpers

open PEqualNP.QuantumGravity MeasureTheory
open scoped Matrix.Norms.L2Operator

section Norm

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem opDist_eq (A B : Matrix ι ι ℂ) : opDist A B = ‖A - B‖ := rfl

/-- A unitary has operator norm at most `1` (exactly `1`, unless there are no basis states). -/
theorem norm_unitary_le (U : Matrix.unitaryGroup ι ℂ) : ‖(U : Matrix ι ι ℂ)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty ι with h | h
  · rw [Subsingleton.elim (U : Matrix ι ι ℂ) 0, norm_zero]
    exact zero_le_one
  · rw [CStarRing.norm_of_mem_unitary U.2]

end Norm

section Approx

variable {ι : Type} [Fintype ι] [DecidableEq ι]

local notation "M" => Matrix ι ι ℂ

theorem reachableIn_subset_approx (S : Set (Matrix.unitaryGroup ι ℂ)) (k : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) : ReachableIn S k ⊆ ApproxReachableIn S k ε :=
  fun V hV => ⟨V, hV, by rw [opDist_eq, sub_self, norm_zero]; exact hε⟩

theorem approx_mono {S : Set (Matrix.unitaryGroup ι ℂ)} {k k' : ℕ} {ε ε' : ℝ} (hk : k ≤ k')
    (hε : ε ≤ ε') : ApproxReachableIn S k ε ⊆ ApproxReachableIn S k' ε' := by
  rintro U ⟨V, hV, hUV⟩
  exact ⟨V, reachableIn_mono hk hV, hUV.trans hε⟩

/-- Errors add: the approximate form of `mul_mem_reachableIn`. -/
theorem mul_mem_approx {S : Set (Matrix.unitaryGroup ι ℂ)} {k m : ℕ} {ε δ : ℝ}
    {U W : Matrix.unitaryGroup ι ℂ} (hU : U ∈ ApproxReachableIn S k ε)
    (hW : W ∈ ApproxReachableIn S m δ) : U * W ∈ ApproxReachableIn S (k + m) (ε + δ) := by
  obtain ⟨V, hV, hUV⟩ := hU
  obtain ⟨X, hX, hWX⟩ := hW
  refine ⟨V * X, mul_mem_reachableIn hV hX, ?_⟩
  rw [opDist_eq] at hUV hWX ⊢
  have key : ((V * X : Matrix.unitaryGroup ι ℂ) : M) - ((U * W : Matrix.unitaryGroup ι ℂ) : M) =
      (V : M) * ((X : M) - W) + ((V : M) - U) * W := by
    simp only [Submonoid.coe_mul]
    noncomm_ring
  rw [key]
  calc ‖(V : M) * ((X : M) - W) + ((V : M) - U) * W‖
      ≤ ‖(V : M)‖ * ‖(X : M) - W‖ + ‖(V : M) - U‖ * ‖(W : M)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ 1 * δ + ε * 1 :=
        add_le_add (mul_le_mul (norm_unitary_le V) hWX (norm_nonneg _) zero_le_one)
          (mul_le_mul hUV (norm_unitary_le W) (norm_nonneg _) ((norm_nonneg _).trans hUV))
    _ = ε + δ := by ring

theorem one_mem_approx (S : Set (Matrix.unitaryGroup ι ℂ)) :
    (1 : Matrix.unitaryGroup ι ℂ) ∈ ApproxReachableIn S 0 0 :=
  reachableIn_subset_approx S 0 le_rfl (one_mem_reachableIn S 0)

/-- Approximate complexity grows at most linearly in time. -/
theorem pow_mem_approx {S : Set (Matrix.unitaryGroup ι ℂ)} {k : ℕ} {ε : ℝ}
    {U : Matrix.unitaryGroup ι ℂ} (hU : U ∈ ApproxReachableIn S k ε) (t : ℕ) :
    U ^ t ∈ ApproxReachableIn S (t * k) (t * ε) := by
  induction t with
  | zero => simpa using one_mem_approx S
  | succ t ih =>
    rw [pow_succ, Nat.succ_mul, Nat.cast_succ, add_one_mul]
    exact mul_mem_approx ih hU

/-- A word of gates, each within `δ` of a product of at most `m` gates of `S`, is within
`length * δ` of a product of at most `length * m` gates of `S`. -/
theorem list_prod_mem_approx {S T : Set (Matrix.unitaryGroup ι ℂ)} {m : ℕ} {δ : ℝ}
    (hT : ∀ g ∈ T, g ∈ ApproxReachableIn S m δ) :
    ∀ l : List (Matrix.unitaryGroup ι ℂ), (∀ x ∈ l, x ∈ T) →
      l.prod ∈ ApproxReachableIn S (l.length * m) (l.length * δ)
  | [], _ => by simpa using one_mem_approx S
  | a :: l, hl => by
    have h := mul_mem_approx (hT a (hl a (by simp)))
      (list_prod_mem_approx hT l fun x hx => hl x (List.mem_cons_of_mem a hx))
    rw [List.prod_cons, List.length_cons, Nat.succ_mul, Nat.cast_succ, add_one_mul]
    rw [add_comm (l.length * m), add_comm ((l.length : ℝ) * δ)]
    exact h

/-- Compiling a gate set `T` into a gate set `S`. -/
theorem approx_compile {S T : Set (Matrix.unitaryGroup ι ℂ)} {k m : ℕ} {ε δ : ℝ} (hδ : 0 ≤ δ)
    (hT : ∀ g ∈ T, g ∈ ApproxReachableIn S m δ) :
    ApproxReachableIn T k ε ⊆ ApproxReachableIn S (k * m) (ε + k * δ) := by
  rintro U ⟨V, ⟨l, hl, hlT, rfl⟩, hUV⟩
  obtain ⟨X, hX, hVX⟩ := approx_mono (Nat.mul_le_mul_right m hl)
    (mul_le_mul_of_nonneg_right (show (l.length : ℝ) ≤ k by exact_mod_cast hl) hδ)
    (list_prod_mem_approx hT l hlT)
  refine ⟨X, hX, ?_⟩
  rw [opDist_eq] at hUV hVX ⊢
  calc ‖(X : M) - U‖ = ‖((X : M) - l.prod) + ((l.prod : M) - U)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖(X : M) - l.prod‖ + ‖(l.prod : M) - U‖ := norm_add_le _ _
    _ ≤ k * δ + ε := add_le_add hVX hUV
    _ = ε + k * δ := add_comm _ _

end Approx

section Perm

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem coe_permUnitary (σ : Equiv.Perm ι) :
    (permUnitary σ : Matrix ι ι ℂ) = (σ⁻¹).permMatrix ℂ := rfl

theorem permUnitary_injective : Function.Injective (permUnitary (ι := ι)) := by
  intro σ τ h
  have h' := congrArg (fun U : Matrix.unitaryGroup ι ℂ => (U : Matrix ι ι ℂ)) h
  simp only [coe_permUnitary] at h'
  rw [← inv_inj]
  ext x
  have hx := congrFun (congrFun h' x) (σ⁻¹ x)
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq] at hx
  split_ifs at hx with h1 h2 <;> simp_all

/-- The products of gates from the image of `S` under a monoid hom are the images of the products
of gates from `S`. -/
theorem reachableIn_image {G H : Type} [Monoid G] [Monoid H] (f : G →* H) (S : Set G) (k : ℕ) :
    ReachableIn (f '' S) k = f '' ReachableIn S k := by
  ext h
  constructor
  · rintro ⟨l, hl, hS, rfl⟩
    have lift : ∀ l : List H, (∀ x ∈ l, x ∈ f '' S) →
        ∃ l₀ : List G, l₀.length = l.length ∧ (∀ x ∈ l₀, x ∈ S) ∧ f l₀.prod = l.prod := by
      intro l
      induction l with
      | nil => exact fun _ => ⟨[], rfl, by simp, by simp⟩
      | cons a l ih =>
        intro hal
        obtain ⟨s, hs, rfl⟩ := hal a (by simp)
        obtain ⟨l₀, hlen, hl₀, hprod⟩ := ih fun x hx => hal x (List.mem_cons_of_mem _ hx)
        refine ⟨s :: l₀, by simp [hlen], ?_, by simp [hprod]⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hs
        · exact hl₀ x hx
    obtain ⟨l₀, hlen, hl₀, hprod⟩ := lift l hS
    exact ⟨l₀.prod, ⟨l₀, hlen ▸ hl, hl₀, rfl⟩, hprod⟩
  · rintro ⟨g, ⟨l, hl, hS, rfl⟩, rfl⟩
    refine ⟨l.map f, by simpa using hl, ?_, by simp [map_list_prod]⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ⟨y, hS y hy, rfl⟩

theorem mem_reachableIn_permUnitary_iff (S : Set (Equiv.Perm ι)) (k : ℕ) (g : Equiv.Perm ι) :
    g ∈ ReachableIn S k ↔ permUnitary g ∈ ReachableIn (permUnitary '' S) k := by
  rw [reachableIn_image, permUnitary_injective.mem_set_image]

end Perm

section Countable

/-- The products of finite words of gates from a countable gate set form a countable set. -/
theorem countable_iUnion_reachableIn {G : Type} [Monoid G] {S : Set G} (hS : S.Countable) :
    (⋃ k, ReachableIn S k).Countable := by
  have := hS.to_subtype
  refine (Set.countable_range fun l : List S => (l.map Subtype.val).prod).mono ?_
  intro g hg
  obtain ⟨k, l, -, hl, rfl⟩ := Set.mem_iUnion.1 hg
  lift l to List S using hl
  exact ⟨l, rfl⟩

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exp_mul_I_mem_unitary (θ : ℝ) : Complex.exp (θ * Complex.I) ∈ unitary ℂ := by
  rw [Unitary.mem_iff, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add,
    ← Complex.exp_add]
  simp [Complex.conj_ofReal]

/-- The phase `exp (i θ)` times the identity, as a unitary. -/
noncomputable def phaseUnitary [Nonempty ι] (θ : ℝ) : Matrix.unitaryGroup ι ℂ :=
  ⟨Matrix.diagonal fun _ => Complex.exp (θ * Complex.I),
    Matrix.diagonal_mem_unitary.2 (Pi.const_mem_unitary_iff.2 (exp_mul_I_mem_unitary θ))⟩

/-- The unitary group of a nonempty set of basis states is uncountable. -/
theorem not_countable_unitaryGroup [Nonempty ι] :
    ¬ (Set.univ : Set (Matrix.unitaryGroup ι ℂ)).Countable := by
  intro hc
  have : Countable (Matrix.unitaryGroup ι ℂ) := Set.countable_univ_iff.1 hc
  apply Cardinal.not_countable_real
  have hcover : (Set.univ : Set ℝ) ⊆ ⋃ U : Matrix.unitaryGroup ι ℂ, phaseUnitary ⁻¹' {U} :=
    fun θ _ => Set.mem_iUnion.2 ⟨phaseUnitary θ, rfl⟩
  refine Set.Countable.mono hcover (Set.countable_iUnion fun U => ?_)
  rcases (phaseUnitary (ι := ι) ⁻¹' {U}).eq_empty_or_nonempty with he | ⟨θ₀, hθ₀⟩
  · rw [he]
    exact Set.countable_empty
  · refine (Set.countable_range fun m : ℤ => θ₀ + m * (2 * Real.pi)).mono ?_
    intro θ hθ
    have heq : phaseUnitary (ι := ι) θ = phaseUnitary θ₀ :=
      (Set.mem_preimage.1 hθ).trans (Set.mem_preimage.1 hθ₀).symm
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hii := congrArg (fun V : Matrix.unitaryGroup ι ℂ => (V : Matrix ι ι ℂ) i i) heq
    simp only [phaseUnitary, Matrix.diagonal_apply_eq] at hii
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 hii
    refine ⟨m, ?_⟩
    have him := congrArg Complex.im hm
    simp at him
    change θ₀ + m * (2 * Real.pi) = θ
    linarith

/-- No countable gate set reaches every unitary exactly. -/
theorem exists_not_mem_iUnion_reachableIn [Nonempty ι] {S : Set (Matrix.unitaryGroup ι ℂ)}
    (hS : S.Countable) : ∃ U : Matrix.unitaryGroup ι ℂ, ∀ k, U ∉ ReachableIn S k := by
  by_contra hall
  push Not at hall
  apply not_countable_unitaryGroup (ι := ι)
  refine (countable_iUnion_reachableIn hS).mono fun U _ => ?_
  obtain ⟨k, hk⟩ := hall U
  exact Set.mem_iUnion.2 ⟨k, hk⟩

end Countable

section Haar

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The unitary group is compact: it is closed, and its entries have modulus at most `1`. -/
theorem isCompact_unitaryGroup : IsCompact (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
  have hc : IsCompact (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι =>
      Metric.closedBall (0 : ℂ) 1 : Set (ι → ι → ℂ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine (show IsCompact (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι =>
      Metric.closedBall (0 : ℂ) 1 : Set (Matrix ι ι ℂ)) from hc).of_isClosed_subset
    (isClosed_unitary (R := Matrix ι ι ℂ)) ?_
  intro U hU
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => entry_norm_bound_of_unitary hU i j

theorem compactSpace_unitaryGroup : CompactSpace (Matrix.unitaryGroup ι ℂ) :=
  isCompact_iff_compactSpace.mp isCompact_unitaryGroup

/-- The Haar probability measure on the unitary group exists. -/
theorem exists_haar_probability :
    ∃ μ : Measure (Matrix.unitaryGroup ι ℂ), IsProbabilityMeasure μ ∧ μ.IsMulLeftInvariant := by
  have := compactSpace_unitaryGroup (ι := ι)
  refine ⟨Measure.haarMeasure ⊤, ⟨?_⟩, inferInstance⟩
  have h1 := Measure.haarMeasure_self
    (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup ι ℂ)))
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at h1

end Haar

section Counting

open PEqualNP.QuantumGravity.Gap

/-- The union bound: L-qg-115 implies L-qg-116 with the same constant. -/
theorem knill_of_ball (h : L115) : L116 := by
  obtain ⟨C, hC, hball⟩ := h
  refine ⟨C, hC, fun n μ _ _ S k ε hε => ?_⟩
  classical
  have hsub : ApproxReachableIn (S : Set (qubitUnitaryGroup n)) k ε ⊆
      ⋃ V ∈ ball S k, {U : qubitUnitaryGroup n |
        opDist (V : Matrix (Qubits n) (Qubits n) ℂ) (U : Matrix (Qubits n) (Qubits n) ℂ) ≤ ε} := by
    rintro U ⟨V, hV, hUV⟩
    exact Set.mem_biUnion (reachableIn_subset_ball S k hV) hUV
  calc μ.real (ApproxReachableIn (S : Set (qubitUnitaryGroup n)) k ε)
      ≤ μ.real (⋃ V ∈ ball S k, {U : qubitUnitaryGroup n |
        opDist (V : Matrix (Qubits n) (Qubits n) ℂ) (U : Matrix (Qubits n) (Qubits n) ℂ) ≤ ε}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ V ∈ ball S k, μ.real {U : qubitUnitaryGroup n |
        opDist (V : Matrix (Qubits n) (Qubits n) ℂ) (U : Matrix (Qubits n) (Qubits n) ℂ) ≤ ε} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _V ∈ ball S k, (C * ε) ^ (4 ^ n) := Finset.sum_le_sum fun V _ => hball n μ V ε hε
    _ = (ball S k).card * (C * ε) ^ (4 ^ n) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((S.card : ℝ) + 1) ^ k * (C * ε) ^ (4 ^ n) := by
        gcongr
        exact_mod_cast card_ball_le S k

/-- L-qg-116 gives a unitary that no short circuit approximates. -/
theorem hard_of_knill (h : L116) : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (S : Finset (qubitUnitaryGroup n)) (k : ℕ) (ε : ℝ), 0 < ε →
      ((S.card : ℝ) + 1) ^ k < (c / ε) ^ (4 ^ n) →
        ∃ U : qubitUnitaryGroup n, U ∉ ApproxReachableIn (S : Set (qubitUnitaryGroup n)) k ε := by
  obtain ⟨C, hC, hknill⟩ := h
  refine ⟨1 / C, by positivity, fun n S k ε hε hlt => ?_⟩
  obtain ⟨μ, hμ₁, hμ₂⟩ := exists_haar_probability (ι := Qubits n)
  by_contra hall
  push Not at hall
  have hbound := hknill n μ S k ε hε.le
  rw [Set.eq_univ_of_forall hall, probReal_univ] at hbound
  have hpos : 0 < (C * ε) ^ (4 ^ n) := by positivity
  have hlt' : ((S.card : ℝ) + 1) ^ k * (C * ε) ^ (4 ^ n) < 1 := by
    calc ((S.card : ℝ) + 1) ^ k * (C * ε) ^ (4 ^ n)
        < (1 / C / ε) ^ (4 ^ n) * (C * ε) ^ (4 ^ n) := mul_lt_mul_of_pos_right hlt hpos
      _ = 1 := by
        rw [← mul_pow]
        field_simp
        simp
  linarith

end Counting

end PEqualNP.QuantumGravity.Helpers
