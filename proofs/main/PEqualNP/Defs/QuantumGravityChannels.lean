import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Density matrices and quantum channels (`Defs/QuantumGravityChannels.lean`)

Definitions for the quantum gravity program (`QuantumGravity/README.md`), board card D-qg-2. They
are the thin layer over Mathlib's matrices that Deutsch's consistency condition for a quantum
register on a closed timelike curve is stated in. A register of `d` levels has the
computational basis `Fin d`; its states are complex `d × d` matrices.

* `IsDensityMatrix ρ`: `ρ` is positive semidefinite (`Matrix.PosSemidef`, for the order
  `ComplexOrder` on `ℂ`) and has trace `1`.
* `IsKrausFamily K`: the Kraus operators `K i` satisfy `∑ i, (K i)ᴴ * K i = 1`.
* `krausMap K ρ`: the quantum channel in Kraus form, `∑ i, K i * ρ * (K i)ᴴ`.
* `MapsDiagonalToDiagonal K`: `krausMap K` maps every matrix that is diagonal in the
  computational basis to a diagonal matrix. On diagonal density matrices such a channel acts as
  a stochastic matrix: it is the embedding of a classical, probabilistic map.
* `krausOfMap f`: the Kraus operators `|f x⟩⟨x|` of a map `f` of the computational basis, the
  embedding of a classical, deterministic map.
-/

namespace PEqualNP.QuantumGravity

open Matrix
open scoped ComplexOrder

/-- `ρ` is a density matrix on `Fin d`: a complex matrix that is positive semidefinite and has
trace `1`. Positive semidefinite is Mathlib's `Matrix.PosSemidef`, for the order `ComplexOrder`
on `ℂ` (`0 ≤ z` when `z` is a nonnegative real number). -/
def IsDensityMatrix {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The matrices `K i` are the Kraus operators of a quantum channel on `Fin d`:
`∑ i, (K i)ᴴ * K i = 1`. -/
def IsKrausFamily {ι : Type} [Fintype ι] {d : ℕ} (K : ι → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∑ i, (K i)ᴴ * K i = 1

/-- The quantum channel with Kraus operators `K i`: `ρ ↦ ∑ i, K i * ρ * (K i)ᴴ`. It is a
channel (completely positive and trace preserving) when `IsKrausFamily K`. -/
def krausMap {ι : Type} [Fintype ι] {d : ℕ} (K : ι → Matrix (Fin d) (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i, K i * ρ * (K i)ᴴ

/-- `krausMap K` maps every matrix that is diagonal in the computational basis `Fin d` to a
diagonal matrix. -/
def MapsDiagonalToDiagonal {ι : Type} [Fintype ι] {d : ℕ}
    (K : ι → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.IsDiag → (krausMap K ρ).IsDiag

/-- The Kraus operators `|f x⟩⟨x|`, one for each basis state `x`, of the map `f` of the
computational basis `Fin d`. -/
def krausOfMap {d : ℕ} (f : Fin d → Fin d) (x : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.single (f x) x 1

end PEqualNP.QuantumGravity
