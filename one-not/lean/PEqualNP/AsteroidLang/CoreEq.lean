import PEqualNP.W951.AsteroidCheap
import PEqualNP.AsteroidLang.Core
/-!
# The checkers of the executable are the project's checkers

`AsteroidLang/Core.lean` repeats the checkers of `SearchCheck.lean`, `Asteroid.lean` and
`AsteroidCheap.lean` without importing Mathlib, so that the executable `asteroid` does not link it.
Each theorem below says one copy is the original, applied to the fields of the project's `Circ`, and
each is proved by `rfl`. So a verdict the executable prints is a value of the function the generated
theorem is about.
-/
namespace AsteroidLang.CoreEq
open SearchCheck

theorem varTT_eq (n i : Nat) : SearchCheck.varTT n i = Core.varTT n i := rfl
theorem tt_eq (full : Nat) (ws : List Nat) (gs : List Gate) :
    SearchCheck.tt full ws gs = Core.tt Gate.op Gate.a Gate.b full ws gs := rfl
theorem tables_eq (C : Circ) : C.tables = Core.tables C.n C.gates Gate.op Gate.a Gate.b := rfl
theorem correctB_eq (C : Circ) :
    correctB C = Core.correctB C.n C.sets C.outs C.gates Gate.op Gate.a Gate.b := rfl
theorem hasWitness_eq (n : Nat) (sets : List (List Nat)) (t : Nat) :
    hasWitness n sets t = Core.hasWitness n sets t := rfl
theorem witnessCount_eq (C : Circ) :
    witnessCount C = Core.witnessCount C.n C.sets C.gates Gate.op Gate.a Gate.b := rfl
theorem hasWitnessAt_eq (n : Nat) (sets : List (List Nat)) (q t : Nat) :
    hasWitnessAt n sets q t = Core.hasWitnessAt n sets q t := rfl
theorem orTables_eq (C : Circ) : orTables C = Core.orTables C.n C.gates Gate.op Gate.a Gate.b := rfl
theorem baseAt_eq (C : Circ) (q : Nat) : baseAt C q = Core.baseAt C.sets q := rfl
theorem orWitnessAt_eq (C : Circ) (q : Nat) :
    orWitnessAt C q = Core.orWitnessAt C.n C.sets C.gates Gate.op Gate.a Gate.b q := rfl
theorem slackGe_eq (C : Circ) (q : Nat) (k : Int) :
    slackGe C q k = Core.slackGe C.n C.sets C.gates Gate.op Gate.a Gate.b q k := rfl
theorem slackLe_eq (C : Circ) (q : Nat) (k : Int) :
    slackLe C q k = Core.slackLe C.n C.sets C.gates Gate.op Gate.a Gate.b q k := rfl
theorem slackNonnegAll_eq (C : Circ) :
    slackNonnegAll C = Core.slackNonnegAll C.n C.sets C.gates Gate.op Gate.a Gate.b := rfl
theorem setsOkB_eq (C : Circ) : setsOkB C = Core.setsOkB C.n C.sets := rfl
theorem notCount_eq (C : Circ) : notCount C = Core.notCount C.gates Gate.op ⟨0, 0, 0⟩ := rfl
theorem hypsB_eq (C : Circ) :
    hypsB C = Core.hypsB C.n C.sets C.outs C.gates Gate.op ⟨0, 0, 0⟩ := rfl

/-- the circuit of the executable, as a circuit of the project -/
def toProject (C : Core.Circ) : Circ := ⟨C.n, C.sets, C.outs, C.gates.map fun g => ⟨g.op, g.a, g.b⟩⟩

end AsteroidLang.CoreEq
