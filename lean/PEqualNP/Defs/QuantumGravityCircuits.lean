import PEqualNP.Defs.QuantumGravity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Quantum circuits, for the quantum gravity program

The definitions of board card D-qg-1. The ruling behind them is `QuantumGravity/README.md`.

* `Qubits n`: the basis index of `n` qubits, the bit strings `Fin n → Bool` (the standard basis
  `|x⟩`).
* `qubitUnitaryGroup n`: the unitary group of `n` qubits, `Matrix.unitaryGroup (Qubits n) ℂ`,
  the `2^n × 2^n` complex unitary matrices.
* Gate sets are sets of unitaries, `S : Set (Matrix.unitaryGroup ι ℂ)`, finite gate sets are
  `Finset`s. Exact reachability is `ReachableIn S k` of `Defs/QuantumGravity.lean`, which works
  in every monoid: the unitaries that are products of at most `k` gates from `S`.
* `opDist A B`: the operator norm of `A - B`, acting on `ℂ^ι` with the Euclidean norm.
* `ApproxReachableIn S k ε`: the unitaries `U` within `ε` of a product `V` of at most `k` gates
  from `S`, `opDist V U ≤ ε`.
* `ActsOnQubits T U` and `twoQubitGates n`: the unitary `U` of `n` qubits is `W ⊗ 1` for a
  unitary `W` of the qubits in `T`; the two-qubit gates act on at most two qubits.
* `permUnitary`: a reversible map `σ` of the basis states, as the unitary `|x⟩ ↦ |σ x⟩`.

## The norm

The distance between unitaries is the operator norm of their difference, for the Euclidean
norm on `ℂ^ι`: `opDist A B = sup {‖(A - B) x‖ : ‖x‖ ≤ 1}`, the largest singular value of
`A - B`. In the pinned Mathlib it is the norm of `Matrix.toEuclideanCLM (A - B)`, the
continuous linear map of `EuclideanSpace ℂ ι` that `A - B` defines; the scoped instance
`Matrix.Norms.L2Operator` puts the same norm on matrices and makes them a C⋆-algebra
(`Matrix.cstar_norm_def`). The choice:

1. It is the norm of the literature this card follows: Knill's "two-norm" `‖A‖₂` (Knill 1995),
   the distance `E(U, V)` of Nielsen and Chuang, and the distance in the Solovay-Kitaev theorem.
2. It is unitarily invariant and submultiplicative, and a unitary has norm at most `1`, so
   errors add along a circuit: the error of a product of gates is at most the sum of the errors
   of the gates (L-qg-111).
3. It bounds every measurement: `‖U x - V x‖ ≤ opDist U V` for every state `x`, so the sum
   over the outcomes `b` of `|Prob(b | U x) - Prob(b | V x)|` is at most `2 opDist U V`
   (Knill 1995, Lemma 2.1).
4. It does not grow with the dimension: `opDist 1 0 = 1` on every number of qubits, while the
   Frobenius norm of the identity of `n` qubits is `2^(n/2)`.

## The Haar measure

Statements about "the fraction of unitaries" quantify over every left-invariant probability
measure `μ` on the unitary group, for the Borel σ-algebra of the matrix entries. The unitary
group is a compact metrizable group, so every finite Borel measure on it is regular, and there
is exactly one such `μ`: the Haar probability measure. Quantifying over `μ` states the
statement for the Haar measure without fixing a construction of it.
-/

namespace PEqualNP.QuantumGravity

open scoped Matrix

/-- The basis index of `n` qubits: the bit strings of length `n`, the standard basis `|x⟩`. -/
abbrev Qubits (n : ℕ) : Type := Fin n → Bool

/-- The unitary group of `n` qubits: the `2^n × 2^n` complex unitary matrices, with rows and
columns indexed by `Qubits n`. -/
abbrev qubitUnitaryGroup (n : ℕ) : Submonoid (Matrix (Qubits n) (Qubits n) ℂ) :=
  Matrix.unitaryGroup (Qubits n) ℂ

/-- The operator norm distance of the matrices `A` and `B` acting on `ℂ^ι` with the Euclidean
norm: the largest singular value of `A - B`. It is the norm of `Matrix.toEuclideanCLM (A - B)`;
under the scoped instance `Matrix.Norms.L2Operator` it is `‖A - B‖`. -/
noncomputable def opDist {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (A - B)‖

/-- Approximate reachability: the unitaries `U` within `ε` of some product `V` of at most `k`
gates from `S`, in the operator norm: `opDist V U ≤ ε`. -/
def ApproxReachableIn {ι : Type} [Fintype ι] [DecidableEq ι] (S : Set (Matrix.unitaryGroup ι ℂ))
    (k : ℕ) (ε : ℝ) : Set (Matrix.unitaryGroup ι ℂ) :=
  {U | ∃ V ∈ ReachableIn S k, opDist (V : Matrix ι ι ℂ) (U : Matrix ι ι ℂ) ≤ ε}

/-- The matrix `U` of `n` qubits acts only on the qubits in `T`: `U = W ⊗ 1` for a matrix `W` of
the qubits in `T`. Entrywise, `⟨x| U |y⟩` is `0` unless `x` and `y` agree outside `T`, and is
then the entry of `W` at the restrictions of `x` and `y` to `T`. -/
def ActsOnQubits {n : ℕ} (T : Finset (Fin n)) (U : Matrix (Qubits n) (Qubits n) ℂ) : Prop :=
  ∃ W : Matrix (T → Bool) (T → Bool) ℂ, ∀ x y : Qubits n,
    U x y = if ∀ i, i ∉ T → x i = y i then W (fun i => x i) (fun i => y i) else 0

/-- The two-qubit gates of `n` qubits: the unitaries that act on at most two of the qubits.
These are Knill's family `G₂` of 2-qubit gates (for `n ≥ 2`). -/
def twoQubitGates (n : ℕ) : Set (qubitUnitaryGroup n) :=
  {U | ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ActsOnQubits T (U : Matrix _ _ ℂ)}

/-- A reversible map `σ` of the basis states, as the unitary that maps `|x⟩` to `|σ x⟩`: the
permutation matrix `σ⁻¹.permMatrix ℂ`, whose entry at `(x, y)` is `1` when `x = σ y` and `0`
otherwise. With `ι = Qubits n` it embeds the reversible circuits of `n` bits
(`Equiv.Perm (Fin n → Bool)`) into the quantum circuits of `n` qubits. -/
def permUnitary {ι : Type} [Fintype ι] [DecidableEq ι] :
    Equiv.Perm ι →* Matrix.unitaryGroup ι ℂ :=
  (Matrix.permMatrixHom (n := ι) (R := ℂ)).codRestrict (Matrix.unitaryGroup ι ℂ) fun σ => by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.permMatrixHom_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_inv, mul_inv_cancel,
      Matrix.permMatrix_one]

end PEqualNP.QuantumGravity
