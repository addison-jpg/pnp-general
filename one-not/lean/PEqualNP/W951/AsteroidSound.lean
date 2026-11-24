import Mathlib
import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.W951.Asteroid
/-!
# AsteroidSound: what asteroid's kernel checks say about the project's circuits

Serves the asteroid language (task `asteroid-bridge`). `SearchCheck` evaluates a circuit literal
bit-parallel: one `Nat` per wire, bit `r` = the value on the input vector `r`. This file proves that
those tables are what they are meant to be.

* Layer 1. `Circ.wiresAt C r`: the pointwise evaluation (one `Bool` per wire) on the input vector `r`.
  `varTT_testBit`, `tables_map_testBit`, `tables_testBit`: bit `r` of the table of wire `k` is the value of
  wire `k` at `r`, for every `r < 2^n`.
* Layer 2. `correctB_sound`: `correctB C = true` ⇒ at every `r < 2^n` every output wire is the OR of the
  bits of `r` over its set. No hypothesis on the set elements (a point `≥ n` reads `false` on both sides).
* Layer 3. `Circ.toGates` (the project's gate list), `wiresAt_eq_wires` (the pointwise evaluation IS
  `Circuit.wires` of the project), `toGates_wf` (ops in {and, or, not}, at most two inputs), and the headline
  `correctB_sound_project`: the correctness hypothesis of `L_meta_951` for `C.toGates`, `C.setFin`,
  `fun w => C.outs.getD w 0`.
* The instance `first_ast_tiny_correct` (now in `AsteroidInstances`): the circuit of `asteroid/examples/first.ath`.
-/
namespace SearchCheck

open PEqualNP.CircuitLowerBounds (Circuit GateOp)

/-! ## Layer 1: the tables are pointwise -/

/-- the value of one gate from the list `w` of the wire values so far (a missing wire reads `false`) -/
def gateVal (w : List Bool) (g : Gate) : Bool :=
  match g.op with
  | 0 => w.getD g.a false && w.getD g.b false
  | 1 => w.getD g.a false || w.getD g.b false
  | _ => !(w.getD g.a false)

/-- all wire values: the start list, then one `Bool` per gate -/
def wiresFrom (ws : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [gateVal w g]) ws

/-- **The pointwise evaluator**: the wire values of `C` on the input vector `r` (input `i` = bit `i` of `r`). -/
def Circ.wiresAt (C : Circ) (r : Nat) : List Bool :=
  wiresFrom ((List.range C.n).map fun i => r.testBit i) C.gates

theorem bitStep_testBit_zero (a : Nat) (b : Bool) :
    ((a <<< 1) ||| (if b then 1 else 0)).testBit 0 = b := by
  cases b <;> simp

theorem bitStep_testBit_succ (a : Nat) (b : Bool) (k : Nat) :
    ((a <<< 1) ||| (if b then 1 else 0)).testBit (k + 1) = a.testBit k := by
  cases b <;> simp [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_one_eq_true_iff_self_eq_zero]

theorem foldr_bits_testBit (p : Nat → Bool) (l : List Nat) (k : Nat) :
    (l.foldr (fun r acc => (acc <<< 1) ||| (if p r then 1 else 0)) 0).testBit k
      = (l[k]?.map p).getD false := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => rw [List.foldr_cons, bitStep_testBit_zero]; simp
    | succ k => rw [List.foldr_cons, bitStep_testBit_succ, ih]; simp

/-- bit `r` of the table of input `i`, at every `r` -/
theorem varTT_testBit_gen (n i r : Nat) :
    (varTT n i).testBit r = (decide (r < 2 ^ n) && r.testBit i) := by
  unfold varTT
  rw [foldr_bits_testBit]
  by_cases h : r < 2 ^ n
  · simp [h]
  · simp [h]

/-- **bit `r` of the table of input `i` is bit `i` of `r`** (rows `r < 2^n`) -/
theorem varTT_testBit {n r : Nat} (i : Nat) (hr : r < 2 ^ n) :
    (varTT n i).testBit r = r.testBit i := by
  simp [varTT_testBit_gen, hr]

/-- one step of `tt`, on lists -/
def ttStep (full : Nat) (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | 0 => Nat.land (w.getD g.a 0) (w.getD g.b 0)
  | 1 => Nat.lor (w.getD g.a 0) (w.getD g.b 0)
  | _ => Nat.xor full (w.getD g.a 0)

theorem tt_foldl_toList (full : Nat) (gs : List Gate) (A : Array Nat) :
    (gs.foldl (fun (w : Array Nat) g =>
      let x := w.getD g.a 0
      let y := w.getD g.b 0
      w.push (match g.op with
        | 0 => Nat.land x y
        | 1 => Nat.lor x y
        | _ => Nat.xor full x)) A).toList
      = gs.foldl (fun w g => w ++ [ttStep full w g]) A.toList := by
  induction gs generalizing A with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    congr 1
    rcases g with ⟨op, a, b⟩
    simp only [Array.toList_push, ttStep, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
      Array.getElem?_toList]

/-- `tt` is a fold over lists -/
theorem tt_eq (full : Nat) (ws : List Nat) (gs : List Gate) :
    tt full ws gs = gs.foldl (fun w g => w ++ [ttStep full w g]) ws := by
  exact tt_foldl_toList full gs ws.toArray

theorem getD_map_testBit (T : List Nat) (r k : Nat) :
    (T.map fun t => t.testBit r).getD k false = (T.getD k 0).testBit r := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases T[k]? <;> simp

theorem land_testBit (x y r : Nat) : (Nat.land x y).testBit r = (x.testBit r && y.testBit r) :=
  Nat.testBit_and x y r

theorem lor_testBit (x y r : Nat) : (Nat.lor x y).testBit r = (x.testBit r || y.testBit r) :=
  Nat.testBit_or x y r

theorem xor_testBit (x y r : Nat) : (Nat.xor x y).testBit r = (x.testBit r ^^ y.testBit r) :=
  Nat.testBit_xor x y r

theorem ttStep_testBit {full r : Nat} (hfull : full.testBit r = true) (T : List Nat) (g : Gate) :
    (ttStep full T g).testBit r = gateVal (T.map fun t => t.testBit r) g := by
  rcases g with ⟨op, a, b⟩
  match op with
  | 0 => simp only [ttStep, gateVal, land_testBit, getD_map_testBit]
  | 1 => simp only [ttStep, gateVal, lor_testBit, getD_map_testBit]
  | k + 2 => simp only [ttStep, gateVal, xor_testBit, getD_map_testBit, hfull, Bool.true_xor]

theorem foldl_ttStep_map {full r : Nat} (hfull : full.testBit r = true) (gs : List Gate)
    (T : List Nat) :
    (gs.foldl (fun w g => w ++ [ttStep full w g]) T).map (fun t => t.testBit r)
      = wiresFrom (T.map fun t => t.testBit r) gs := by
  induction gs generalizing T with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih, wiresFrom, wiresFrom, List.foldl_cons, List.map_append,
      List.map_singleton, ttStep_testBit hfull]

/-- bit `r` of the all-ones mask is `1` at every row -/
theorem full_testBit {n r : Nat} (hr : r < 2 ^ n) : (2 ^ (2 ^ n) - 1).testBit r = true := by
  rw [Nat.testBit_two_pow_sub_one]; simpa using hr

/-- **Layer 1.** Row `r` of the tables is the pointwise evaluation at `r`. -/
theorem tables_map_testBit (C : Circ) {r : Nat} (hr : r < 2 ^ C.n) :
    C.tables.toList.map (fun t => t.testBit r) = C.wiresAt r := by
  unfold Circ.tables Circ.wiresAt
  simp only []
  rw [tt_eq, foldl_ttStep_map (full_testBit hr), List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact varTT_testBit i hr

/-- **Layer 1, wire by wire.** Bit `r` of the table of wire `k` is the value of wire `k` at `r`. -/
theorem tables_testBit (C : Circ) {r : Nat} (hr : r < 2 ^ C.n) (k : Nat) :
    (C.tables.getD k 0).testBit r = (C.wiresAt r).getD k false := by
  rw [← tables_map_testBit C hr, getD_map_testBit]
  congr 1
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

/-! ## Layer 2: `correctB` is sound -/

theorem foldl_lor_testBit (f : Nat → Nat) (r : Nat) (S : List Nat) (a : Nat) :
    (S.foldl (fun acc u => Nat.lor acc (f u)) a).testBit r
      = (a.testBit r || S.any fun u => (f u).testBit r) := by
  induction S generalizing a with
  | nil => simp
  | cons u S ih => rw [List.foldl_cons, ih, lor_testBit, List.any_cons, Bool.or_assoc]

theorem testBit_eq_false_of_ge {n r u : Nat} (hr : r < 2 ^ n) (hu : n ≤ u) : r.testBit u = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hu))

theorem ins_getD_testBit {n r : Nat} (hr : r < 2 ^ n) (u : Nat) :
    (((List.range n).map (varTT n)).getD u 0).testBit r = r.testBit u := by
  by_cases hu : u < n
  · simp [List.getD_eq_getElem?_getD, hu, varTT_testBit u hr]
  · simp [List.getD_eq_getElem?_getD, hu, testBit_eq_false_of_ge hr (not_lt.mp hu)]

/-- **Layer 2.** If the kernel check `correctB C` succeeds, then at every input vector `r < 2^n` every
output wire carries the OR of the bits of `r` over its set. -/
theorem correctB_sound (C : Circ) (h : correctB C = true) {r : Nat} (hr : r < 2 ^ C.n)
    (S : List Nat) (o : Nat) (hSo : (S, o) ∈ C.sets.zip C.outs) :
    (C.wiresAt r).getD o false = S.any fun u => r.testBit u := by
  unfold correctB at h
  simp only [List.all_eq_true] at h
  have h1 := h (S, o) hSo
  simp only [beq_iff_eq] at h1
  rw [← tables_testBit C hr, h1, foldl_lor_testBit]
  simp only [Nat.zero_testBit, Bool.false_or, ins_getD_testBit hr]

/-! ## Layer 3: the pointwise evaluation is the project's semantics -/

/-- one gate of the project: op 0 ↦ and [a,b], 1 ↦ or [a,b], else ↦ not [a] -/
def Gate.toGate (g : Gate) : PEqualNP.CircuitLowerBounds.Gate :=
  match g.op with
  | 0 => ⟨GateOp.and, [g.a, g.b]⟩
  | 1 => ⟨GateOp.or, [g.a, g.b]⟩
  | _ => ⟨GateOp.not, [g.a]⟩

/-- **The project's gate list** of a circuit literal. -/
def Circ.toGates (C : Circ) : List PEqualNP.CircuitLowerBounds.Gate := C.gates.map Gate.toGate

theorem gateVal_eq_eval (w : List Bool) (g : Gate) :
    gateVal w g = g.toGate.op.eval (g.toGate.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, a, b⟩
  match op with
  | 0 => simp [gateVal, Gate.toGate, GateOp.eval]
  | 1 => simp [gateVal, Gate.toGate, GateOp.eval]
  | k + 2 => simp [gateVal, Gate.toGate, GateOp.eval]

/-- on any start list, `wiresFrom` is `Circuit.wires` of the translated gates -/
theorem wiresFrom_eq_wires (ws : List Bool) (gs : List Gate) (o : Nat) :
    wiresFrom ws gs = Circuit.wires ⟨gs.map Gate.toGate, o⟩ ws := by
  unfold wiresFrom Circuit.wires
  rw [List.foldl_map]
  congr 1
  funext w g
  rw [gateVal_eq_eval]

theorem ofFn_eq_range_testBit {n : Nat} (x : Fin n → Bool) :
    List.ofFn x = (List.range n).map fun i => (Nat.ofBits x).testBit i := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    simp [Nat.testBit_ofBits_lt x i hi]

/-- **Layer 3.** On the input `x`, read as the number `Nat.ofBits x` (bit `i` = `x i`), the pointwise
evaluation is exactly the project's `Circuit.wires` on `List.ofFn x`. -/
theorem wiresAt_eq_wires (C : Circ) (x : Fin C.n → Bool) (o : Nat) :
    C.wiresAt (Nat.ofBits x) = Circuit.wires ⟨C.toGates, o⟩ (List.ofFn x) := by
  rw [Circ.wiresAt, wiresFrom_eq_wires _ _ o, ← ofFn_eq_range_testBit]
  rfl

/-- the translated gates satisfy the gate hypothesis of `L_meta_951` -/
theorem toGates_wf (C : Circ) : ∀ g ∈ C.toGates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨g0, -, rfl⟩ := List.mem_map.mp hg
  rcases g0 with ⟨op, a, b⟩
  match op with
  | 0 => simp [Gate.toGate]
  | 1 => simp [Gate.toGate]
  | k + 2 => simp [Gate.toGate]

/-- the set number `w` as a `Finset (Fin n)` (points `≥ n` are dropped) -/
def Circ.setFin (C : Circ) (w : Fin C.sets.length) : Finset (Fin C.n) :=
  Finset.univ.filter fun v => v.val ∈ C.sets[w]

theorem any_testBit_ofBits {n : Nat} (x : Fin n → Bool) (S : List Nat) :
    (S.any fun u => (Nat.ofBits x).testBit u) = true ↔ ∃ v : Fin n, v.val ∈ S ∧ x v = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨u, huS, hu⟩
    have hun : u < n := by
      by_contra hc
      rw [Nat.testBit_ofBits_ge x u (not_lt.mp hc)] at hu
      exact Bool.false_ne_true hu
    rw [Nat.testBit_ofBits_lt x u hun] at hu
    exact ⟨⟨u, hun⟩, huS, hu⟩
  · rintro ⟨v, hvS, hv⟩
    exact ⟨v.val, hvS, by rw [Nat.testBit_ofBits_lt x v.val v.isLt]; exact hv⟩

/-- **The headline.** If the kernel check `correctB C` succeeds (and there is an output wire for every
set), then the project's circuit `C.toGates` with output wire `C.outs[w]` computes `OR(S_w)` on every
input, in the project's semantics `Circuit.eval`. This is the correctness hypothesis of `L_meta_951`
with `n := C.n`, `m := C.sets.length`, `S := C.setFin`, `gates := C.toGates`,
`out := fun w => C.outs.getD w 0`. -/
theorem correctB_sound_project (C : Circ) (h : correctB C = true)
    (hlen : C.sets.length ≤ C.outs.length) (w : Fin C.sets.length) (x : Fin C.n → Bool) :
    Circuit.eval ⟨C.toGates, C.outs.getD w 0⟩ (List.ofFn x)
      = decide (∃ v ∈ C.setFin w, x v = true) := by
  have hw : w.val < C.outs.length := lt_of_lt_of_le w.isLt hlen
  have hmem : (C.sets[w], C.outs.getD w 0) ∈ C.sets.zip C.outs := by
    have hz : w.val < (C.sets.zip C.outs).length := by simp [w.isLt, hw]
    have := List.getElem_mem hz
    rw [List.getElem_zip] at this
    simpa [List.getD_eq_getElem?_getD, hw] using this
  have h2 := correctB_sound C h (Nat.ofBits_lt_two_pow x) _ _ hmem
  rw [Circuit.eval, ← wiresAt_eq_wires C x, h2, Bool.eq_iff_iff, any_testBit_ofBits]
  simp [Circ.setFin]

end SearchCheck

#print axioms SearchCheck.tables_testBit
#print axioms SearchCheck.correctB_sound
#print axioms SearchCheck.wiresAt_eq_wires
#print axioms SearchCheck.correctB_sound_project
