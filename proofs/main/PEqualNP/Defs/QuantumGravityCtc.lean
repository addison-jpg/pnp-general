import PEqualNP.Defs.QuantumGravity
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Vector

/-!
# Definitions for the quantum gravity program: P with a classical closed timelike curve

The ruling behind this file is `QuantumGravity/README.md`, track D (closed timelike curves). It
defines the complexity class P_CTC of Deutsch's model with a classical, deterministic circuit,
as in Aaronson and Watrous (arXiv:0808.2669) and Brun (arXiv:gr-qc/0209061), on top of
`Defs/Base.lean` (machines, `ComputableInPolyTime`, `encodePair`) and
`Defs/QuantumGravity.lean` (`DeutschConsistent`).

* `ctcRegisterMap next x m`: the map of the `m`-bit register on the closed timelike curve that
  the circuit `next` induces on input `x`. The next register is `next (x, r)` cut or padded
  with `false` to exactly `m` bits.
* `bitsSucc r`: the register `r` read as a binary number, least significant bit first, plus one
  modulo `2 ^ (length of r)`. It is the step of Brun's counter on the curve register.
* `PCTC`: the languages decided by a polynomial-time circuit `next` acting on the input and a
  register of polynomially many bits sent back in time, and a polynomial-time read-out `ans`,
  for every Deutsch-consistent distribution of the register.

## Why a deterministic map is the classical Deutsch model

In Deutsch's model a circuit acts on a causality-respecting register, which holds the input `x`,
and on a register that travels along the closed timelike curve. Nature puts the curve register
in a state that the circuit carries to itself: a fixed point of the induced channel. For a
classical circuit the states are probability distributions on bit strings, and a deterministic
circuit induces the push-forward `μ ↦ μ.map (ctcRegisterMap next x m)`; its fixed points are
exactly the distributions `μ` with `DeutschConsistent (ctcRegisterMap next x m) μ`. A circuit
that flips coins induces a Markov kernel instead; that case is gap L-qg-102 and is not part of
this definition.

## Why "every consistent distribution" and not "some"

The algorithm does not choose the fixed point; nature does, and the definition must be correct
whichever one it chooses. That is the quantifier of Aaronson and Watrous. The other quantifier
proves too much: with "some", the circuit that leaves its one-bit register unchanged and the
read-out that answers the register bit put every language, even an undecidable one, in the class,
because the point mass on the right bit is consistent (row L-qg-163). Consistent distributions
always exist (row L-qg-160), so "every" is never vacuous.
-/

namespace PEqualNP.QuantumGravity

/-- The map of the `m`-bit closed timelike curve register induced by the circuit `next` on the
input `x`: the next register is `next (x, r)` cut or padded with `false` to exactly `m` bits. -/
def ctcRegisterMap (next : List Bool × List Bool → List Bool) (x : List Bool) (m : ℕ) :
    List.Vector Bool m → List.Vector Bool m :=
  fun r => ⟨(next (x, r.toList) ++ List.replicate m false).take m, by simp⟩

/-- The register read as a binary number, least significant bit first, plus one modulo
`2 ^ (length of the register)`: flip the leading `true` bits to `false` and the first `false` bit
to `true`. The length does not change. -/
def bitsSucc : List Bool → List Bool
  | [] => []
  | false :: r => true :: r
  | true :: r => false :: bitsSucc r

/-- P_CTC, the classical, deterministic version of Deutsch's model: `L` is in `PCTC` when there
are a polynomial `p` and two polynomial-time functions `ans` and `next` of the pair (input,
register) such that, for every input `x` and every Deutsch-consistent distribution `μ` of
`ctcRegisterMap next x (p (length of x))`, every register `r` charged by `μ` has
`ans (x, r) = true` exactly when `x` is in `L`. -/
def PCTC : Set (Language Bool) :=
  {L | ∃ (p : Polynomial ℕ) (ans : List Bool × List Bool → Bool)
      (next : List Bool × List Bool → List Bool),
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair Computability.encodeBool
        ans ∧
      PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair (fun y : List Bool => y)
        next ∧
      ∀ (x : List Bool) (μ : PMF (List.Vector Bool (p.eval x.length))),
        DeutschConsistent (ctcRegisterMap next x (p.eval x.length)) μ →
          ∀ r ∈ μ.support, (ans (x, r.toList) = true ↔ x ∈ L)}

end PEqualNP.QuantumGravity
