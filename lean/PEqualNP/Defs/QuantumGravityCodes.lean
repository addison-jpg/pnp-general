import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Definitions for holographic codes in the quantum gravity program

The ruling behind this file is `QuantumGravity/README.md` (track F). The holographic codes of
Pastawski, Yoshida, Harlow and Preskill (arXiv:1503.06237) are built from the five-qubit code
`[[5,1,3]]` and the six-qubit perfect tensor. Both are stabilizer codes, and a stabilizer code
has a classical description over the field with two elements: a Pauli operator up to phase is a
pair of bit vectors, and two Pauli operators commute exactly when their symplectic product is
zero. This file is the thin layer of that classical description. Quantum states and the Hilbert
space are not defined here.

* `PauliVec n`: a Pauli operator on `n` qubits up to phase, as its pair of bit vectors
  `(x, z)`; qubit `i` carries `X` when `x i = 1, z i = 0`, `Z` when `x i = 0, z i = 1`, `Y` when
  both are `1`, and the identity `I` when both are `0`. Products of Pauli operators are sums.
* `symp a b`: the symplectic product; it is `0` exactly when `a` and `b` commute.
* `pauliSupport a`, `pauliWeight a`: the qubits on which `a` is not the identity, and their
  number.
* `IsIsotropic S`: the elements of the subspace `S` commute pairwise. An isotropic subspace is
  the stabilizer group of a stabilizer code, up to phases.
* `pauliNormalizer S`: the Pauli operators that commute with every element of `S`, the logical
  operators of the code (those in `S` act trivially on the code space).
* `HasDistance S d`: every logical operator not in `S` acts on at least `d` qubits.
* `CorrectsErasure S E`: no logical operator not in `S` acts only on qubits in `E`, so the code
  recovers from the loss of the qubits in `E`.
* `pauliString p`: the Pauli operator with letter `p i` (one of `I`, `X`, `Y`, `Z`) on qubit `i`.
* `fiveQubitCode`: the stabilizer group of the five-qubit code, spanned by `XZZXI` and its
  cyclic shifts `IXZZX`, `XIXZZ`, `ZXIXZ`.
* `sixQubitPerfect`: the stabilizer group of the six-qubit perfect state, spanned by `XZZXII`,
  `IXZZXI`, `XIXZZI`, `ZXIXZI`, `XXXXXX`, `ZZZZZZ`.
-/

namespace PEqualNP.QuantumGravity

/-- A Pauli operator on `n` qubits up to phase: its `X` part and its `Z` part, as bit vectors.
The product of two Pauli operators is, up to phase, the sum of their vectors. -/
abbrev PauliVec (n : ℕ) : Type := (Fin n → ZMod 2) × (Fin n → ZMod 2)

/-- The symplectic product of two Pauli operators: `0` when they commute, `1` when they
anticommute. -/
def symp {n : ℕ} (a b : PauliVec n) : ZMod 2 :=
  ∑ i, (a.1 i * b.2 i + a.2 i * b.1 i)

/-- The qubits on which the Pauli operator `a` is not the identity. -/
def pauliSupport {n : ℕ} (a : PauliVec n) : Finset (Fin n) :=
  Finset.univ.filter fun i => a.1 i ≠ 0 ∨ a.2 i ≠ 0

/-- The weight of a Pauli operator: the number of qubits on which it is not the identity. -/
def pauliWeight {n : ℕ} (a : PauliVec n) : ℕ :=
  (pauliSupport a).card

/-- The elements of `S` commute pairwise: `S` is the stabilizer group of a stabilizer code, up
to phases. -/
def IsIsotropic {n : ℕ} (S : Submodule (ZMod 2) (PauliVec n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, symp a b = 0

/-- The normalizer of the stabilizer group `S`: the Pauli operators that commute with every
element of `S`. -/
def pauliNormalizer {n : ℕ} (S : Submodule (ZMod 2) (PauliVec n)) : Set (PauliVec n) :=
  {b | ∀ a ∈ S, symp a b = 0}

/-- The code with stabilizer group `S` has distance at least `d`: every Pauli operator that
commutes with `S` and is not in `S` acts on at least `d` qubits. -/
def HasDistance {n : ℕ} (S : Submodule (ZMod 2) (PauliVec n)) (d : ℕ) : Prop :=
  ∀ b ∈ pauliNormalizer S, b ∉ S → d ≤ pauliWeight b

/-- The code with stabilizer group `S` corrects the erasure of the qubits in `E`: no Pauli
operator that commutes with `S` and is not in `S` acts only on qubits in `E`. -/
def CorrectsErasure {n : ℕ} (S : Submodule (ZMod 2) (PauliVec n)) (E : Finset (Fin n)) :
    Prop :=
  ∀ b ∈ pauliNormalizer S, b ∉ S → ¬ pauliSupport b ⊆ E

/-- A single-qubit Pauli operator up to phase. -/
inductive PauliLetter
  | I
  | X
  | Y
  | Z
  deriving DecidableEq

/-- The `X` bit of a single-qubit Pauli operator: `1` for `X` and `Y`. -/
def PauliLetter.xBit : PauliLetter → ZMod 2
  | .I => 0
  | .X => 1
  | .Y => 1
  | .Z => 0

/-- The `Z` bit of a single-qubit Pauli operator: `1` for `Y` and `Z`. -/
def PauliLetter.zBit : PauliLetter → ZMod 2
  | .I => 0
  | .X => 0
  | .Y => 1
  | .Z => 1

/-- The Pauli operator on `n` qubits with the letter `p i` on qubit `i`. -/
def pauliString {n : ℕ} (p : Fin n → PauliLetter) : PauliVec n :=
  (fun i => (p i).xBit, fun i => (p i).zBit)

open PauliLetter in
/-- The generators of the five-qubit code: `XZZXI` and its cyclic shifts `IXZZX`, `XIXZZ`,
`ZXIXZ`. -/
def fiveQubitGens : Fin 4 → PauliVec 5 :=
  ![pauliString ![X, Z, Z, X, I], pauliString ![I, X, Z, Z, X],
    pauliString ![X, I, X, Z, Z], pauliString ![Z, X, I, X, Z]]

/-- The stabilizer group of the five-qubit code `[[5,1,3]]`: the span of `XZZXI`, `IXZZX`,
`XIXZZ`, `ZXIXZ`. -/
def fiveQubitCode : Submodule (ZMod 2) (PauliVec 5) :=
  Submodule.span (ZMod 2) (Set.range fiveQubitGens)

open PauliLetter in
/-- The generators of the six-qubit perfect state: the five-qubit generators with `I` on a sixth
qubit, and `XXXXXX`, `ZZZZZZ`. -/
def sixQubitGens : Fin 6 → PauliVec 6 :=
  ![pauliString ![X, Z, Z, X, I, I], pauliString ![I, X, Z, Z, X, I],
    pauliString ![X, I, X, Z, Z, I], pauliString ![Z, X, I, X, Z, I],
    pauliString ![X, X, X, X, X, X], pauliString ![Z, Z, Z, Z, Z, Z]]

/-- The stabilizer group of the six-qubit perfect state, the perfect tensor of the holographic
codes: the span of `XZZXII`, `IXZZXI`, `XIXZZI`, `ZXIXZI`, `XXXXXX`, `ZZZZZZ`. -/
def sixQubitPerfect : Submodule (ZMod 2) (PauliVec 6) :=
  Submodule.span (ZMod 2) (Set.range sixQubitGens)

end PEqualNP.QuantumGravity
