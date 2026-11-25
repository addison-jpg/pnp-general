import PEqualNP.Defs.Base
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Definitions for the quantum gravity program

The ruling behind this file is `QuantumGravity/README.md`. Quantum gravity arguments about
complexity (holographic complexity, decoding Hawking radiation, closed timelike curves, bounds on
the number of states of a region) each rest on a classical, finite core. This file is the thin
layer those cores are stated in. Quantum states, unitaries and geometry are not defined here;
the README lists what each physics claim would need.

* `ReachableIn S k`: the elements of a monoid that are products of at most `k` elements of `S`.
  With `S` a gate set in the group of reversible maps of `n` bits, `Equiv.Perm (Fin n → Bool)`,
  these are the maps that have a circuit of at most `k` gates. The least such `k` is the
  circuit complexity that the "complexity = volume" and "complexity = action" conjectures speak
  of, in its classical, reversible form.
* `LocalGate n g`: the reversible map `g` of `n` bits acts on at most three of them.
* `ctcSearchMap φ`: the map of the register `ZMod N` that keeps `x` when `φ x` holds and steps
  to `x + 1` otherwise: the circuit that Brun and Aaronson put on a closed timelike curve.
* `DeutschConsistent f μ`: the map `f` carries the distribution `μ` of the register to itself,
  Deutsch's causal consistency condition for a classical register.
* `InvertibleInPolyTime f`: some polynomial-time `g` returns, on every image `f x`, a preimage of
  `f x`. A polynomial-time `f` without this is a worst-case one-way function.
-/

namespace PEqualNP.QuantumGravity

/-- `g` is a product of at most `k` elements of `S`. The empty product is `1`, so `1` is in
`ReachableIn S k` for every `k`. -/
def ReachableIn {G : Type} [Monoid G] (S : Set G) (k : ℕ) : Set G :=
  {g | ∃ l : List G, l.length ≤ k ∧ (∀ x ∈ l, x ∈ S) ∧ l.prod = g}

/-- The reversible map `g` of `n` bits acts on at most three of them: for some set `T` of at most
three bit positions, `g` leaves every bit outside `T` unchanged, and the new bits in `T` depend
only on the old bits in `T`. -/
def LocalGate (n : ℕ) (g : Equiv.Perm (Fin n → Bool)) : Prop :=
  ∃ T : Finset (Fin n), T.card ≤ 3 ∧
    (∀ x i, i ∉ T → g x i = x i) ∧
      ∀ x y, (∀ i ∈ T, x i = y i) → ∀ i ∈ T, g x i = g y i

/-- The gate set of all reversible maps of `n` bits that act on at most three of them. -/
def localGates (n : ℕ) : Set (Equiv.Perm (Fin n → Bool)) :=
  {g | LocalGate n g}

/-- The circuit on the closed timelike curve register `ZMod N`: keep `x` when `φ x` holds,
otherwise step to `x + 1`. -/
def ctcSearchMap {N : ℕ} (φ : ZMod N → Bool) (x : ZMod N) : ZMod N :=
  if φ x = true then x else x + 1

/-- Deutsch's causal consistency condition for a classical register: the map `f` carries the
distribution `μ` of the register to itself. -/
def DeutschConsistent {S : Type} (f : S → S) (μ : PMF S) : Prop :=
  μ.map f = μ

/-- Some polynomial-time `g` returns a preimage of `f x` on every input `f x`. -/
def InvertibleInPolyTime (f : List Bool → List Bool) : Prop :=
  ∃ g : List Bool → List Bool,
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g ∧
      ∀ x, f (g (f x)) = f x

end PEqualNP.QuantumGravity
