import PEqualNP.W951.SearchCheck
/-!
# Asteroid: the Lean side of the asteroid language (`asteroid/`)

Kernel-decidable functions on a circuit literal (`SearchCheck.Circ`), over the bit-parallel tables of
`SearchCheck`. A cube `q` is a bit mask of the points set to 1.

* `orWitnessAt C q`: the OR gates that are 0 at a zero point `Z ⊇ q` of a set avoiding `q` and 1 at two of its atoms.
* `baseAt C q`: the sum of `|S| - 1` over the sets avoiding `q`.
* `slackGe C q k`: `orWitnessAt C q - baseAt C q ≥ k`.
* `slackNonnegAll C`: `baseAt C q ≤ orWitnessAt C q` at every cube `q < 2^n`.

These are statements about this evaluator; the theorem tying it to the project's `Circuit.eval` is not proved here.
-/
namespace SearchCheck

/-- does table `t` have a witness above the cube `q` for a set avoiding `q` -/
def hasWitnessAt (n : Nat) (sets : List (List Nat)) (q t : Nat) : Bool :=
  sets.any fun S =>
    (S.all fun s => !q.testBit s) &&
    (List.range (2^n)).any fun r =>
      (Nat.land q r == q) && (S.all fun s => !r.testBit s) && !t.testBit r &&
      (S.filter fun u => t.testBit (Nat.lor r (2^u))).length ≥ 2

/-- the tables of the OR gates -/
def orTables (C : Circ) : List Nat :=
  (((C.tables.toList.drop C.n).zip C.gates).filter fun p => p.2.op == 1).map (·.1)

def baseAt (C : Circ) (q : Nat) : Nat :=
  (C.sets.filter fun S => S.all fun s => !q.testBit s).foldl (fun acc S => acc + (S.length - 1)) 0

def orWitnessAtWith (C : Circ) (T : List Nat) (q : Nat) : Nat :=
  (T.filter (hasWitnessAt C.n C.sets q)).length

def orWitnessAt (C : Circ) (q : Nat) : Nat := orWitnessAtWith C (orTables C) q

def slackGe (C : Circ) (q : Nat) (k : Int) : Bool :=
  decide ((orWitnessAt C q : Int) - (baseAt C q : Int) ≥ k)

def slackLe (C : Circ) (q : Nat) (k : Int) : Bool :=
  decide ((orWitnessAt C q : Int) - (baseAt C q : Int) ≤ k)

def slackNonnegAllWith (C : Circ) (T : List Nat) : Bool :=
  (List.range (2^C.n)).all fun q => decide (baseAt C q ≤ orWitnessAtWith C T q)

/-- slack is nonnegative at every cube -/
def slackNonnegAll (C : Circ) : Bool := slackNonnegAllWith C (orTables C)

end SearchCheck
