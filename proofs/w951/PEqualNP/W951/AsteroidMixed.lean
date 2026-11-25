import PEqualNP.W951.Asteroid
/-!
# AsteroidMixed: mixed slack and the mixed step, kernel-decidable (extension `asteroid/ext_mixed.py`)

A MIXED STATE `(q, r)` is a pair of bit masks over the `n` points: the points of `q` are fixed to 1, those of `r`
to 0, and `q &&& r = 0`. For a circuit `C` (a `SearchCheck.Circ`):

* `S ∖ r` is the set `S` without the points of `r`. A set is ALIVE at `(q, r)` if `S ∩ q = ∅` and `|S ∖ r| ≥ 2`.
* `baseMixed C q r` = sum over alive sets of `|S ∖ r| - 1`.
* `hasWitnessMixed`: the OR gate with table `t` is a witness at `(q, r)`: for some alive `S` there is a point
  `z ⊇ q` with `z ∩ r = ∅`, `z ∩ S = ∅`, `t z = 0` and `t (z + e_u) = 1` for two distinct `u ∈ S ∖ r`.
* `mslackVal C q r` = (number of OR-gate witnesses) - `baseMixed C q r`, as an `Int`.
* `mslackGe` / `mslackLe`: comparisons against an integer. `mslackNonnegAll C`: `mslackVal ≥ 0` at all `3^n` states.
* `mixedStepAll C`: at every state with `baseMixed > 0` there is a free point `v` (not in `q ∪ r`) such that
  moving `v` into `q` (a 1-step) or into `r` (a 0-step) PAYS (the base of the new state is strictly smaller) and
  has `mslackVal` no larger than the current one. This is `continuous.py`'s `cmd_mixed` / `mixed_margin`.

For speed the OR-gate tables are computed once (`orTables C`) and passed along (`...With`). `mixedStepAllWith`
packs the number of witnesses of each state into one big `Nat` (16-bit cells, index `r * 2^n + q`) so a lookup is a
shift and a mask; it checks that every cell fits (fewer than 65536 OR gates).

These are statements about the bit-parallel evaluator of `SearchCheck`, as in `Asteroid.lean`.
-/
namespace SearchCheck

def aliveMixed (S : List Nat) (q r : Nat) : Bool :=
  (S.all fun s => !q.testBit s) && ((S.filter fun s => !r.testBit s).length ≥ 2)

def baseMixed (C : Circ) (q r : Nat) : Nat :=
  (C.sets.filter fun S => aliveMixed S q r).foldl
    (fun acc S => acc + ((S.filter fun s => !r.testBit s).length - 1)) 0

/-- the naive definition: does the gate table `t` have a witness at the mixed state `(q, r)` (loops over all `z < 2^n`) -/
def hasWitnessMixedNaive (n : Nat) (sets : List (List Nat)) (q r t : Nat) : Bool :=
  sets.any fun S =>
    aliveMixed S q r &&
    (List.range (2^n)).any fun z =>
      (Nat.land q z == q) && (Nat.land r z == 0) && (S.all fun s => !z.testBit s) && !t.testBit z &&
      ((S.filter fun u => !r.testBit u).filter fun u => t.testBit (Nat.lor z (2^u))).length ≥ 2

/-- some two entries `a` (earlier), `b` (later) of the list satisfy `f a b` -/
def anyPair (f : Nat → Nat → Bool) : List Nat → Bool
  | [] => false
  | a :: rest => rest.any (f a) || anyPair f rest

/-- precomputed once per circuit: the all-ones table and the tables of the inputs (bit `z` of `ins[v]` is bit `v` of `z`) -/
def mixPre (C : Circ) : Nat × List Nat := (2^(2^C.n) - 1, (List.range C.n).map (varTT C.n))

/-- the same, bit-parallel: `V` = the points `z` with `z ⊇ q`, `z ∩ r = ∅`, `z ∩ S = ∅`; `A` = those with `t z = 0`;
a witness iff some pair `u ≠ u'` of `S ∖ r` has `t (z + e_u) = t (z + e_u') = 1` at some `z` of `A` -/
def hasWitnessMixed (P : Nat × List Nat) (sets : List (List Nat)) (q r t : Nat) : Bool :=
  let full := P.1
  let ins := P.2
  sets.any fun S =>
    aliveMixed S q r &&
    (let V := (List.range ins.length).foldl (fun acc v =>
        Nat.land acc (if q.testBit v then ins.getD v 0
                      else if r.testBit v || S.contains v then Nat.xor full (ins.getD v 0) else full)) full
     let A := Nat.land V (Nat.xor full t)
     let ts := (S.filter fun u => !r.testBit u).map fun u => Nat.land (t >>> (2^u)) (Nat.xor full (ins.getD u 0))
     anyPair (fun a b => Nat.land A (Nat.land a b) != 0) ts)

def witnessMixedWith (C : Circ) (T : List Nat) (q r : Nat) : Nat :=
  (T.filter (hasWitnessMixed (mixPre C) C.sets q r)).length

def mslackValWith (C : Circ) (T : List Nat) (q r : Nat) : Int :=
  (witnessMixedWith C T q r : Int) - (baseMixed C q r : Int)

def mslackVal (C : Circ) (q r : Nat) : Int := mslackValWith C (orTables C) q r

def mslackGe (C : Circ) (q r : Nat) (k : Int) : Bool := decide (mslackVal C q r ≥ k)
def mslackLe (C : Circ) (q r : Nat) (k : Int) : Bool := decide (mslackVal C q r ≤ k)

/-- every mixed state `(q, r)`, `q &&& r = 0`, as a predicate over the masks -/
def allStates (n : Nat) (p : Nat → Nat → Bool) : Bool :=
  (List.range (2^n)).all fun r => (List.range (2^n)).all fun q => (Nat.land q r != 0) || p q r

/-- the bit-parallel and the naive witness tests agree at every state (a check, not used by the claims) -/
def naiveAgrees (C : Circ) : Bool :=
  let T := orTables C
  allStates C.n fun q r => (T.filter (hasWitnessMixedNaive C.n C.sets q r)).length == witnessMixedWith C T q r

def mslackNonnegAllWith (C : Circ) (T : List Nat) : Bool :=
  allStates C.n fun q r => decide (baseMixed C q r ≤ witnessMixedWith C T q r)

/-- mixed slack is nonnegative at all `3^n` mixed states -/
def mslackNonnegAll (C : Circ) : Bool := mslackNonnegAllWith C (orTables C)

/-- the packed table of witness counts: cell `r * 2^n + q` (16 bits) -/
def witnessTable (C : Circ) (T : List Nat) : Nat :=
  (List.range (2^C.n * 2^C.n)).foldr
    (fun i acc => (acc <<< 16) ||| (if Nat.land (i / 2^C.n) (i % 2^C.n) == 0 then witnessMixedWith C T (i % 2^C.n) (i / 2^C.n) else 0)) 0

def cellAt (C : Circ) (W q r : Nat) : Nat := Nat.land (W >>> (16 * (r * 2^C.n + q))) 65535

/-- a paying step from `(q, r)` (to `(q + v, r)` or `(q, r + v)`) with `mslack` no larger -/
def payingStepAt (C : Circ) (W q r : Nat) : Bool :=
  (List.range C.n).any fun v =>
    !q.testBit v && !r.testBit v &&
    ((baseMixed C (Nat.lor q (2^v)) r < baseMixed C q r &&
        decide ((cellAt C W (Nat.lor q (2^v)) r : Int) - (baseMixed C (Nat.lor q (2^v)) r : Int)
                ≤ (cellAt C W q r : Int) - (baseMixed C q r : Int))) ||
     (baseMixed C q (Nat.lor r (2^v)) < baseMixed C q r &&
        decide ((cellAt C W q (Nat.lor r (2^v)) : Int) - (baseMixed C q (Nat.lor r (2^v)) : Int)
                ≤ (cellAt C W q r : Int) - (baseMixed C q r : Int))))

def mixedStepAllWith (C : Circ) (T : List Nat) : Bool :=
  decide (T.length < 65536) &&
  (let W := witnessTable C T
   allStates C.n fun q r => decide (baseMixed C q r = 0) || payingStepAt C W q r)

/-- MixedStep: at every state with positive base some paying 1-step or 0-step has `mslack` no larger -/
def mixedStepAll (C : Circ) : Bool := mixedStepAllWith C (orTables C)

end SearchCheck
