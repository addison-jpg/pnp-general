import PEqualNP.Defs.QuantumGravityCodes
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Ring

/-!
Helpers for L-qg-140 to L-qg-149: the symplectic description of the five-qubit code and of the
six-qubit perfect state. The general part: the symplectic product is bilinear, so a vector
commutes with a span exactly when it commutes with the generators, and a span is isotropic
exactly when its generators commute pairwise; a code of distance `d` corrects the erasure of
fewer than `d` qubits. The concrete part: finitely many bit computations, each checked by the
kernel (`decide +kernel`) after the vectors are written out bit by bit.
-/

namespace PEqualNP.QuantumGravity.Helpers

open PEqualNP.QuantumGravity

section General

variable {n : ℕ}

theorem symp_comm (a b : PauliVec n) : symp a b = symp b a := by
  unfold symp
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symp_add_left (a a' b : PauliVec n) : symp (a + a') b = symp a b + symp a' b := by
  unfold symp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring

theorem symp_smul_left (c : ZMod 2) (a b : PauliVec n) : symp (c • a) b = c * symp a b := by
  unfold symp
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; ring

/-- The symplectic product with `b` on the right, as a linear form. -/
def sympRight (b : PauliVec n) : PauliVec n →ₗ[ZMod 2] ZMod 2 where
  toFun a := symp a b
  map_add' a a' := symp_add_left a a' b
  map_smul' c a := symp_smul_left c a b

/-- A vector commutes with the span of a family exactly when it commutes with each member. -/
theorem mem_pauliNormalizer_span_iff {k : ℕ} (g : Fin k → PauliVec n) (b : PauliVec n) :
    b ∈ pauliNormalizer (Submodule.span (ZMod 2) (Set.range g)) ↔ ∀ i, symp (g i) b = 0 := by
  constructor
  · intro h i
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h a ha
    have hle : Submodule.span (ZMod 2) (Set.range g) ≤ LinearMap.ker (sympRight b) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact h i
    exact hle ha

/-- The span of a family is isotropic exactly when its members commute pairwise. -/
theorem isIsotropic_span_iff {k : ℕ} (g : Fin k → PauliVec n) :
    IsIsotropic (Submodule.span (ZMod 2) (Set.range g)) ↔ ∀ i j, symp (g i) (g j) = 0 := by
  constructor
  · intro h i j
    exact h _ (Submodule.subset_span ⟨i, rfl⟩) _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro h a ha b hb
    have hgi : ∀ i, g i ∈ pauliNormalizer (Submodule.span (ZMod 2) (Set.range g)) :=
      fun i => (mem_pauliNormalizer_span_iff g (g i)).2 fun j => h j i
    have hb' : ∀ i, symp (g i) b = 0 := fun i => by
      rw [symp_comm]
      exact hgi i b hb
    exact (mem_pauliNormalizer_span_iff g b).2 hb' a ha

theorem isIsotropic_le_pauliNormalizer {S : Submodule (ZMod 2) (PauliVec n)}
    (hS : IsIsotropic S) : (S : Set (PauliVec n)) ⊆ pauliNormalizer S :=
  fun b hb a ha => hS a ha b hb

theorem pauliWeight_le_of_support_subset {b : PauliVec n} {E : Finset (Fin n)}
    (h : pauliSupport b ⊆ E) : pauliWeight b ≤ E.card :=
  Finset.card_le_card h

/-- A code of distance `d` corrects the erasure of every set of fewer than `d` qubits. -/
theorem correctsErasure_of_hasDistance {S : Submodule (ZMod 2) (PauliVec n)} {d : ℕ}
    (hS : HasDistance S d) {E : Finset (Fin n)} (hE : E.card < d) : CorrectsErasure S E := by
  intro b hb hbS hsub
  have h1 := hS b hb hbS
  have h2 := pauliWeight_le_of_support_subset hsub
  omega

end General

/-! ### The five-qubit code -/

theorem fiveQubitCode_isIsotropic : IsIsotropic fiveQubitCode :=
  (isIsotropic_span_iff fiveQubitGens).2 (by decide)

/-- The bit check behind the distance: a Pauli operator on five qubits that commutes with the
four generators and has weight at most two is the identity. -/
theorem eq_zero_of_comm_fiveQubitGens_of_weight_lt :
    ∀ b : PauliVec 5, (∀ i, symp (fiveQubitGens i) b = 0) → pauliWeight b < 3 → b = 0 := by
  rintro ⟨x, z⟩
  revert x z
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

theorem fiveQubitCode_hasDistance : HasDistance fiveQubitCode 3 := by
  intro b hb hbS
  rw [fiveQubitCode, mem_pauliNormalizer_span_iff] at hb
  by_contra hlt
  apply hbS
  rw [eq_zero_of_comm_fiveQubitGens_of_weight_lt b hb (by omega)]
  exact Submodule.zero_mem _

theorem fiveQubitCode_correctsErasure {E : Finset (Fin 5)} (hE : E.card ≤ 2) :
    CorrectsErasure fiveQubitCode E :=
  correctsErasure_of_hasDistance fiveQubitCode_hasDistance (by omega)

open PauliLetter in
/-- The distance of the five-qubit code is exactly three: `IYYIX` (the logical `XXXXX` times the
stabilizer `XZZXI`) commutes with the code, is not in it, and acts on three qubits. -/
theorem not_hasDistance_fiveQubitCode_four : ¬ HasDistance fiveQubitCode 4 := by
  intro h
  have hw : pauliString ![I, Y, Y, I, X] ∈ pauliNormalizer fiveQubitCode := by
    rw [fiveQubitCode, mem_pauliNormalizer_span_iff]
    decide
  have hwS : pauliString ![I, Y, Y, I, X] ∉ fiveQubitCode := by
    intro hm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hm
    revert c
    simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
    decide +kernel
  have h3 : pauliWeight (pauliString ![I, Y, Y, I, X]) = 3 := by decide
  have := h _ hw hwS
  omega

/-! ### The six-qubit perfect state -/

theorem sixQubitPerfect_isIsotropic : IsIsotropic sixQubitPerfect :=
  (isIsotropic_span_iff sixQubitGens).2 (by decide)

/-- The bit check behind the weight bound: each of the 64 combinations of the six generators is
zero or has weight at least four. -/
theorem four_le_pauliWeight_combo :
    ∀ c : Fin 6 → ZMod 2, (∑ i, c i • sixQubitGens i) ≠ 0 →
      4 ≤ pauliWeight (∑ i, c i • sixQubitGens i) := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

theorem four_le_pauliWeight_of_mem_sixQubitPerfect {a : PauliVec 6} (ha : a ∈ sixQubitPerfect)
    (h0 : a ≠ 0) : 4 ≤ pauliWeight a := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 ha
  exact four_le_pauliWeight_combo c h0

/-- The bit check behind the Lagrangian property: a Pauli operator on six qubits that commutes
with the six generators is the combination of them with the coefficients written here. -/
theorem combo_eq_of_comm_sixQubitGens :
    ∀ b : PauliVec 6, (∀ i, symp (sixQubitGens i) b = 0) →
      (∑ i, ![b.1 0 + b.1 2, b.1 4 + b.1 5, b.1 2 + b.1 5, b.1 1 + b.1 4, b.1 5, b.2 5] i •
        sixQubitGens i) = b := by
  rintro ⟨x, z⟩
  revert x z
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

theorem pauliNormalizer_sixQubitPerfect :
    pauliNormalizer sixQubitPerfect = (sixQubitPerfect : Set (PauliVec 6)) := by
  apply Set.Subset.antisymm
  · intro b hb
    rw [sixQubitPerfect, mem_pauliNormalizer_span_iff] at hb
    rw [← combo_eq_of_comm_sixQubitGens b hb]
    exact (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).2 ⟨_, rfl⟩
  · exact isIsotropic_le_pauliNormalizer sixQubitPerfect_isIsotropic

/-! ### The five-qubit code inside the perfect state -/

/-- The first five qubits of a Pauli operator on six qubits. -/
def restrictFive (s : PauliVec 6) : PauliVec 5 :=
  (fun i => s.1 (Fin.castSucc i), fun i => s.2 (Fin.castSucc i))

theorem combo_mem_sixQubitPerfect (c : Fin 6 → ZMod 2) :
    (∑ i, c i • sixQubitGens i) ∈ sixQubitPerfect :=
  (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).2 ⟨c, rfl⟩

theorem combo_mem_fiveQubitCode (c : Fin 4 → ZMod 2) :
    (∑ i, c i • fiveQubitGens i) ∈ fiveQubitCode :=
  (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).2 ⟨c, rfl⟩

/-- Bit check: each combination of the five-qubit generators is the first five qubits of the
same combination of the first four six-qubit generators, which is the identity on qubit six. -/
theorem combo_five_eq_restrict :
    ∀ c : Fin 4 → ZMod 2,
      (∑ i, ![c 0, c 1, c 2, c 3, 0, 0] i • sixQubitGens i).1 (Fin.last 5) = 0 ∧
      (∑ i, ![c 0, c 1, c 2, c 3, 0, 0] i • sixQubitGens i).2 (Fin.last 5) = 0 ∧
      ∑ i, c i • fiveQubitGens i =
        restrictFive (∑ i, ![c 0, c 1, c 2, c 3, 0, 0] i • sixQubitGens i) := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

/-- Bit check: a combination of the six generators that is the identity on qubit six is, on the
first five qubits, the combination of the five-qubit generators with the first four
coefficients. -/
theorem restrict_combo_of_last_eq_zero :
    ∀ c : Fin 6 → ZMod 2, (∑ i, c i • sixQubitGens i).1 (Fin.last 5) = 0 →
      (∑ i, c i • sixQubitGens i).2 (Fin.last 5) = 0 →
      restrictFive (∑ i, c i • sixQubitGens i) = ∑ i, ![c 0, c 1, c 2, c 3] i • fiveQubitGens i := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

theorem mem_fiveQubitCode_iff_restrict (a : PauliVec 5) :
    a ∈ fiveQubitCode ↔ ∃ s ∈ sixQubitPerfect, s.1 (Fin.last 5) = 0 ∧ s.2 (Fin.last 5) = 0 ∧
      a = (fun i => s.1 (Fin.castSucc i), fun i => s.2 (Fin.castSucc i)) := by
  constructor
  · intro ha
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 ha
    obtain ⟨h1, h2, h3⟩ := combo_five_eq_restrict c
    exact ⟨_, combo_mem_sixQubitPerfect _, h1, h2, h3⟩
  · rintro ⟨s, hs, h1, h2, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hs
    change restrictFive _ ∈ fiveQubitCode
    rw [restrict_combo_of_last_eq_zero c h1 h2]
    exact combo_mem_fiveQubitCode _

/-- Bit check: the first five qubits of every combination of the six generators commute with
the five-qubit generators. -/
theorem comm_restrict_combo :
    ∀ c : Fin 6 → ZMod 2, ∀ j,
      symp (fiveQubitGens j) (restrictFive (∑ i, c i • sixQubitGens i)) = 0 := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

/-- The coefficients of a logical operator `b` of the five-qubit code in the six generators: the
last two read off the logical class of `b` (`XXXXX` and `ZZZZZ` on the first five qubits). -/
def logicalCoeffs (b : PauliVec 5) : Fin 6 → ZMod 2 :=
  let xs := b.1 0 + b.1 1 + b.1 2 + b.1 3 + b.1 4
  let zs := b.2 0 + b.2 1 + b.2 2 + b.2 3 + b.2 4
  ![b.1 0 + b.1 2, b.1 4 + xs, b.1 2 + xs, b.1 1 + b.1 4, xs, zs]

/-- Bit check: a Pauli operator on five qubits that commutes with the five-qubit generators is
the first five qubits of the combination of the six generators with coefficients
`logicalCoeffs b`. -/
theorem restrict_combo_logicalCoeffs :
    ∀ b : PauliVec 5, (∀ j, symp (fiveQubitGens j) b = 0) →
      restrictFive (∑ i, logicalCoeffs b i • sixQubitGens i) = b := by
  rintro ⟨x, z⟩
  revert x z
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

theorem mem_pauliNormalizer_fiveQubitCode_iff (b : PauliVec 5) :
    b ∈ pauliNormalizer fiveQubitCode ↔
      ∃ s ∈ sixQubitPerfect, b = (fun i => s.1 (Fin.castSucc i), fun i => s.2 (Fin.castSucc i)) := by
  rw [fiveQubitCode, mem_pauliNormalizer_span_iff]
  constructor
  · intro hb
    exact ⟨_, combo_mem_sixQubitPerfect _, (restrict_combo_logicalCoeffs b hb).symm⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hs
    exact comm_restrict_combo c

/-! ### Operator pushing through the perfect tensor -/

/-- Bit check: the six generators are linearly independent. -/
theorem combo_six_eq_zero : ∀ c : Fin 6 → ZMod 2, (∑ i, c i • sixQubitGens i) = 0 → c = 0 := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

/-- An element of the six-qubit perfect stabilizer group that is the identity on three qubits is
the identity: otherwise it would have weight at most three. -/
theorem eq_zero_of_mem_sixQubitPerfect_of_vanish {d : PauliVec 6} (hd : d ∈ sixQubitPerfect)
    {A : Finset (Fin 6)} (hA : A.card = 3) (h : ∀ i ∈ A, d.1 i = 0 ∧ d.2 i = 0) : d = 0 := by
  by_contra h0
  have h4 := four_le_pauliWeight_of_mem_sixQubitPerfect hd h0
  have hsub : pauliSupport d ⊆ Aᶜ := by
    intro i hi
    simp only [pauliSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [Finset.mem_compl]
    intro hiA
    obtain ⟨h1, h2⟩ := h i hiA
    rcases hi with hi | hi
    · exact hi h1
    · exact hi h2
  have h3 := pauliWeight_le_of_support_subset hsub
  rw [Finset.card_compl, hA, Fintype.card_fin] at h3
  omega

/-- Operator pushing: for every set `A` of three of the six qubits, every Pauli operator on `A`
is the restriction to `A` of exactly one element of the perfect stabilizer group. -/
theorem existsUnique_sixQubitPerfect_restrict (A : Finset (Fin 6)) (hA : A.card = 3)
    (p : PauliVec 6) :
    ∃! s, s ∈ sixQubitPerfect ∧ ∀ i ∈ A, s.1 i = p.1 i ∧ s.2 i = p.2 i := by
  let φ : (Fin 6 → ZMod 2) → (A → ZMod 2) × (A → ZMod 2) := fun c =>
    (fun i => (∑ j, c j • sixQubitGens j).1 i, fun i => (∑ j, c j • sixQubitGens j).2 i)
  have hsub : ∀ c c' : Fin 6 → ZMod 2,
      (∑ j, (c - c') j • sixQubitGens j) =
        (∑ j, c j • sixQubitGens j) - ∑ j, c' j • sixQubitGens j := by
    intro c c'
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have hinj : Function.Injective φ := by
    intro c c' h
    have hz : (∑ j, (c - c') j • sixQubitGens j) = 0 := by
      refine eq_zero_of_mem_sixQubitPerfect_of_vanish (combo_mem_sixQubitPerfect _) hA ?_
      intro i hi
      have h1 := congrFun (congrArg Prod.fst h) ⟨i, hi⟩
      have h2 := congrFun (congrArg Prod.snd h) ⟨i, hi⟩
      simp only [φ] at h1 h2
      rw [hsub]
      simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, h1, h2, sub_self, and_self]
    exact sub_eq_zero.1 (combo_six_eq_zero _ hz)
  have hcard : Fintype.card (Fin 6 → ZMod 2) = Fintype.card ((A → ZMod 2) × (A → ZMod 2)) := by
    simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_coe, hA,
      Fintype.card_fin]
    norm_num
  obtain ⟨c, hc⟩ := ((Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩).2
    (fun i => p.1 i, fun i => p.2 i)
  refine ⟨∑ j, c j • sixQubitGens j, ⟨combo_mem_sixQubitPerfect c, fun i hi => ?_⟩, ?_⟩
  · exact ⟨congrFun (congrArg Prod.fst hc) ⟨i, hi⟩, congrFun (congrArg Prod.snd hc) ⟨i, hi⟩⟩
  · rintro s ⟨hs, hsA⟩
    refine sub_eq_zero.1 (eq_zero_of_mem_sixQubitPerfect_of_vanish
      (sub_mem hs (combo_mem_sixQubitPerfect c)) hA fun i hi => ?_)
    have h1 := congrFun (congrArg Prod.fst hc) ⟨i, hi⟩
    have h2 := congrFun (congrArg Prod.snd hc) ⟨i, hi⟩
    simp only [φ] at h1 h2
    obtain ⟨a1, a2⟩ := hsA i hi
    simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, a1, a2, h1, h2, sub_self, and_self]

/-! ### Counting stabilizers and logical operators -/

/-- The range of an injective linear map out of `k` bits has `2^k` elements. -/
theorem ncard_range_linear {k : ℕ} {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (f : (Fin k → ZMod 2) →ₗ[ZMod 2] M) (hf : ∀ c, f c = 0 → c = 0) :
    (Set.range f).ncard = 2 ^ k := by
  rw [Set.ncard_range_of_injective ((injective_iff_map_eq_zero f).2 hf),
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem span_range_eq_range {k n : ℕ} (g : Fin k → PauliVec n) :
    (Submodule.span (ZMod 2) (Set.range g) : Set (PauliVec n)) =
      Set.range (Fintype.linearCombination (ZMod 2) g) := by
  ext a
  simp only [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun, Set.mem_range,
    Fintype.linearCombination_apply]

/-- Bit check: the four five-qubit generators are linearly independent. -/
theorem combo_five_eq_zero : ∀ c : Fin 4 → ZMod 2, (∑ i, c i • fiveQubitGens i) = 0 → c = 0 := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

/-- Bit check: no nonzero combination of the six generators is the identity on the first five
qubits. -/
theorem restrict_combo_six_eq_zero :
    ∀ c : Fin 6 → ZMod 2, restrictFive (∑ i, c i • sixQubitGens i) = 0 → c = 0 := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

/-- The first five qubits, as a linear map. -/
def restrictFiveL : PauliVec 6 →ₗ[ZMod 2] PauliVec 5 where
  toFun := restrictFive
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ncard_fiveQubitCode : (fiveQubitCode : Set (PauliVec 5)).ncard = 16 := by
  rw [fiveQubitCode, span_range_eq_range, ncard_range_linear]
  · norm_num
  intro c hc
  rw [Fintype.linearCombination_apply] at hc
  exact combo_five_eq_zero c hc

theorem ncard_sixQubitPerfect : (sixQubitPerfect : Set (PauliVec 6)).ncard = 64 := by
  rw [sixQubitPerfect, span_range_eq_range, ncard_range_linear]
  · norm_num
  intro c hc
  rw [Fintype.linearCombination_apply] at hc
  exact combo_six_eq_zero c hc

theorem ncard_pauliNormalizer_fiveQubitCode : (pauliNormalizer fiveQubitCode).ncard = 64 := by
  have h : pauliNormalizer fiveQubitCode =
      Set.range (restrictFiveL ∘ₗ Fintype.linearCombination (ZMod 2) sixQubitGens) := by
    ext b
    rw [mem_pauliNormalizer_fiveQubitCode_iff, Set.mem_range]
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hs
      exact ⟨c, by simp only [LinearMap.coe_comp, Function.comp_apply,
        Fintype.linearCombination_apply]; rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨_, combo_mem_sixQubitPerfect c, by simp only [LinearMap.coe_comp,
        Function.comp_apply, Fintype.linearCombination_apply]; rfl⟩
  rw [h, ncard_range_linear]
  · norm_num
  intro c hc
  simp only [LinearMap.coe_comp, Function.comp_apply, Fintype.linearCombination_apply] at hc
  exact restrict_combo_six_eq_zero c hc

end PEqualNP.QuantumGravity.Helpers
