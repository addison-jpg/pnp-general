import PEqualNP.Library.L067
import PEqualNP.Library.L073
import PEqualNP.Library.L004
import PEqualNP.MetaComplexity.L019
import PEqualNP.MetaComplexity.Helpers.Hardwire
import PEqualNP.General.Gaps
import Mathlib.Analysis.Real.OfDigits

/-!
# Two access rules for a real-number oracle (scratch draft)

* Random access: the oracle is the set of strings `w` whose binary index points at a `1` bit.
  Every language is in P relative to such an oracle (`random_access_trivial`, from L-lib-067).
* Precision-bounded access: the machine sees only the first `q (n)` bits, `q` a polynomial.
  One inclusion of "PrefixRealP = P/poly" is proved (`prefixSub`, from L-lib-004, L-lib-073,
  L-meta-019 and the hardwiring helper); the other (`PrefixSup`) is a gap. The link to L-gen-101
  is proved in one direction outright and in the other from `PrefixSup`.
-/

namespace RealOracle

open PEqualNP.Library PEqualNP.CircuitLowerBounds

/-! ## 1. Random access -/

/-- Bijective binary index of a string (little-endian, digits `1` and `2`): a bijection
`List Bool → ℕ`. -/
def binIdx : List Bool → ℕ
  | [] => 0
  | a :: w => 2 * binIdx w + (if a then 2 else 1)

theorem binIdx_injective : Function.Injective binIdx := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons a w => cases a <;> simp [binIdx] at h
  | cons a u ih =>
    intro v h
    cases v with
    | nil => cases a <;> simp [binIdx] at h
    | cons c w =>
      cases a <;> cases c <;> simp only [binIdx, ↓reduceIte, Bool.false_eq_true] at h <;>
        first | omega | rw [@ih w (by omega)]

/-- The random-access oracle of a bit sequence `b`: `w` is in it when bit number `binIdx w`
of `b` is `1`. -/
def bitOracle (b : ℕ → Bool) : Language Bool := {w : List Bool | b (binIdx w) = true}

open Classical in
/-- PROVED. Random access is the trivial world: every language is in P relative to the
random-access oracle of some bit sequence. -/
theorem random_access_trivial :
    ∀ L : Language Bool, ∃ b : ℕ → Bool, L ∈ OracleP (bitOracle b) := by
  intro L
  refine ⟨fun n => decide (∃ w ∈ L, binIdx w = n), ?_⟩
  have h : bitOracle (fun n => decide (∃ w ∈ L, binIdx w = n)) = L := by
    ext w
    show decide (∃ w' ∈ L, binIdx w' = binIdx w) = true ↔ w ∈ L
    rw [decide_eq_true_iff]
    constructor
    · rintro ⟨w', hw', he⟩
      rwa [← binIdx_injective he]
    · intro hw
      exact ⟨w, hw, rfl⟩
  rw [h]
  exact L067 L

/-- Bit `i` (from `0`) after the binary point of `r`, via Mathlib's `Real.digits`. -/
noncomputable def realBit (r : ℝ) (i : ℕ) : Bool := decide ((Real.digits r 2 i : ℕ) = 1)

/-- The random-access oracle of a real `r`: `w` is in it when bit `2 * binIdx w` of `r` is
`1` (odd bits unused, so the bit pattern never has to end in all ones). -/
noncomputable def realOracle (r : ℝ) : Language Bool :=
  bitOracle fun i => realBit r (2 * i)

/-- GAP (real analysis only): a bit sequence with infinitely many zeros is the binary expansion
of some `r ∈ [0, 1)`. Pinned Mathlib has `Real.ofDigits_digits` but not this converse. -/
def DigitsSurj : Prop :=
  ∀ d : ℕ → Bool, (∀ N, ∃ n ≥ N, d n = false) →
    ∃ r ∈ Set.Ico (0 : ℝ) 1, ∀ i, realBit r i = d i

/-- PROVED from `DigitsSurj`: every language is in P relative to the oracle of some real. -/
theorem random_access_real (h : DigitsSurj) :
    ∀ L : Language Bool, ∃ r ∈ Set.Ico (0 : ℝ) 1, L ∈ OracleP (realOracle r) := by
  intro L
  obtain ⟨b, hb⟩ := random_access_trivial L
  obtain ⟨r, hr, hd⟩ := h (fun n => if n % 2 = 0 then b (n / 2) else false)
    (fun N => ⟨2 * N + 1, by omega, by split <;> first | rfl | omega⟩)
  refine ⟨r, hr, ?_⟩
  have e : (fun i => realBit r (2 * i)) = b := by
    funext i
    rw [hd]
    split <;> (congr 1; omega)
  simp only [realOracle, e]
  exact hb

/-! ## 2. Precision-bounded access -/

/-- The first `k` bits of `b`. -/
def pre (b : ℕ → Bool) (k : ℕ) : List Bool := List.ofFn fun i : Fin k => b i

/-- Precision-bounded access to `b`: `L` is decided by a polynomial-time machine (`R ∈ P`, this
repo's machines) that receives, after the input `x`, the first `q (|x|)` bits of `b`. -/
def PrefixRealP (b : ℕ → Bool) : Set (Language Bool) :=
  {L | ∃ (R : Language Bool) (q : Polynomial ℕ), R ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔ x ++ pre b (q.eval x.length) ∈ R}

/-- The precision-bounded world: some bit sequence works for `L`. -/
def PrefixRealWorld : Set (Language Bool) := {L | ∃ b, L ∈ PrefixRealP b}

/-- Inclusion 1 of "PrefixRealP = P/poly" (PROVED below, `prefixSub`). -/
def PrefixSub : Prop := ∀ b : ℕ → Bool, PrefixRealP b ⊆ PPoly

/-- Inclusion 2 of "PrefixRealP = P/poly" (GAP). -/
def PrefixSup : Prop := PPoly ⊆ PrefixRealWorld

/-- NP lies in the precision-bounded world, one sequence per language. -/
def NPPrefixWorld : Prop := NP ⊆ PrefixRealWorld

/-- NP lies in the precision-bounded world of one fixed sequence. -/
def NPPrefixUniform : Prop := ∃ b : ℕ → Bool, NP ⊆ PrefixRealP b

/-- Corollary, per-language form (PROVED from `PrefixSup`, `corollaryWorld_of`). -/
def CorollaryWorld : Prop := NPPrefixWorld ↔ ¬ PEqualNP.General.Gap.L101

/-- Corollary, uniform form (GAP; direction → PROVED, `uniform_imp`). -/
def CorollaryUniform : Prop := NPPrefixUniform ↔ ¬ PEqualNP.General.Gap.L101

/-- PROVED: precision-bounded access gives only polynomial-size circuits. -/
theorem prefixSub : PrefixSub := by
  rintro b L ⟨R, q, hR, hL⟩
  obtain ⟨k, hk⟩ := (L004 R).1 hR
  obtain ⟨c, hc⟩ := L073 _ R hk
  have hc' := (PEqualNP.MetaComplexity.L019 _ R).1 hc
  refine ⟨Polynomial.C c * ((Polynomial.X + q) ^ k + Polynomial.C k + (Polynomial.X + q) + 1) ^ 3
    + 1, ?_⟩
  refine (PEqualNP.MetaComplexity.L019 _ L).2 fun n => ?_
  obtain ⟨f, hf, hsz⟩ := hc' (n + q.eval n)
  refine ⟨fun y => f (Fin.append y fun i : Fin (q.eval n) => b i), fun y => ?_, ?_⟩
  · rw [hf, List.ofFn_fin_append, hL, List.length_ofFn]
    rfl
  · refine PEqualNP.MetaComplexity.Helpers.hasCircuitSize_mono (le_of_eq ?_)
      (PEqualNP.MetaComplexity.Helpers.hardwire n _ f _ _ hsz)
    simp

theorem not_L101_iff : ¬ PEqualNP.General.Gap.L101 ↔ NP ⊆ PPoly := by
  unfold PEqualNP.General.Gap.L101
  simp only [not_exists, not_and, not_not]
  exact Iff.rfl

/-- PROVED: if NP is in the precision-bounded world (per language), L-gen-101 fails. -/
theorem world_imp : NPPrefixWorld → ¬ PEqualNP.General.Gap.L101 := fun h =>
  not_L101_iff.2 fun L hL => by
    obtain ⟨b, hb⟩ := h hL
    exact prefixSub b hb

/-- PROVED: direction → of the uniform corollary. -/
theorem uniform_imp : NPPrefixUniform → ¬ PEqualNP.General.Gap.L101 := fun ⟨b, hb⟩ =>
  not_L101_iff.2 fun _ hL => prefixSub b (hb hL)

/-- PROVED from `PrefixSup`: the precision-bounded world is exactly P/poly. -/
theorem world_eq (h : PrefixSup) : PrefixRealWorld = PPoly :=
  Set.Subset.antisymm (fun _ ⟨b, hb⟩ => prefixSub b hb) h

/-- PROVED from `PrefixSup`: the per-language corollary. -/
theorem corollaryWorld_of (h : PrefixSup) : CorollaryWorld := by
  unfold CorollaryWorld NPPrefixWorld
  rw [world_eq h, not_L101_iff]

/-! ## The same access rule as an oracle (unary addressing) -/

/-- Tally oracle of `b`: `1^i` is in it when `b i = 1`. A machine running in time `p (n)` can
only write queries `1^i` with `i ≤ p (n)`, so it reads a polynomial prefix of `b`. -/
def tallyOracle (b : ℕ → Bool) : Language Bool :=
  {w : List Bool | w = List.replicate w.length true ∧ b w.length = true}

/-- Precision-bounded access as oracle access. -/
def TallyRealP (b : ℕ → Bool) : Set (Language Bool) := OracleP (tallyOracle b)

/-- GAP: tally-oracle P is inside P/poly. -/
def TallySub : Prop := ∀ b : ℕ → Bool, TallyRealP b ⊆ PPoly

/-- GAP: P/poly is inside the union of tally-oracle P. -/
def TallySup : Prop := PPoly ⊆ {L | ∃ b, L ∈ TallyRealP b}

end RealOracle

#print axioms RealOracle.random_access_trivial
#print axioms RealOracle.random_access_real
#print axioms RealOracle.prefixSub
#print axioms RealOracle.world_imp
#print axioms RealOracle.uniform_imp
#print axioms RealOracle.corollaryWorld_of
