import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Data.Nat.Log

/-!
# Definitions for the general program

The general program asks for lower bounds on circuits of AND, OR and NOT gates with any number of
NOT gates: `SIZE` and `PPoly` of `Defs/CircuitLowerBounds.lean`. Its ruling is `BOARD.md` at the
root of the repository. This file adds the one notion that joins the restricted results to the
general problem:

* `SIZENot s t`: the languages decided, at every length `n`, by a circuit of AND, OR and NOT gates
  of fan-in at most two with at most `s n` gates, of which at most `t n` are NOT gates.

`t = 0` is the monotone case; `t = 1` is the case of L-meta-951; by Markov's theorem and Fischer's
construction `t n = ⌈log₂ (n + 1)⌉` is the unrestricted case up to a polynomial factor (gap
L-gen-104).
-/

namespace PEqualNP.General

open PEqualNP.CircuitLowerBounds

open Classical in
/-- SIZE with a bound on the number of NOT gates: at every length `n`, a circuit of AND, OR and NOT
gates of fan-in at most two with at most `s n` gates, at most `t n` of them NOT gates. -/
def SIZENot (s t : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∀ n, ∃ C : Circuit,
    (∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) ∧
    C.size ≤ s n ∧ (C.gates.filter fun g => g.op = GateOp.not).length ≤ t n ∧ C.Decides L n}

end PEqualNP.General
