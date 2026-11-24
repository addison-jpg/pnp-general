import PEqualNP.General.SizeHierarchy
import PEqualNP.Defs.TimeAlt

/-!
# Kannan's theorem, uniform half: definitions and bit-level lemmas

At length `n` (with `m = mm k n`, `N = 2 ^ m`, `B = n ^ (k + 1)` as in `SizeHierarchy`):

* a circuit is given by a bit string of length `ell k n`: `B` gate fields of width
  `gw k n = 2 + 2 * (1 + w)` (two op bits, then two input slots, each a presence bit and a
  `w`-bit little-endian index, `w = n + B + 1`), then a `w`-bit output index (`decCirc`);
* the circuit is evaluated on `n` inputs, on the zero-padded points `pt k n i`
  (the `m` little-endian bits of `i`, then `n - m` zeros);
* a truth table `T` (a list of `N` bits, entry `i` for the point `pt k n i`) is `Hard` when no
  circuit string computes it; `Tstar k n` is the hard table that is first in the
  lexicographic order (`val T` reads `T` as a big-endian number);
* `x ∈ KL k` iff `Tstar` at the index of the first `m` bits of `x` is `1`.
-/

namespace PEqualNP.General.Kannan

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitLowerBounds.Helpers PEqualNP.Library
open PEqualNP.General.SizeHierarchy

/-! ### Binary numbers -/

/-- Little-endian value of a bit string. -/
def bv : List Bool → ℕ
  | [] => 0
  | b :: l => 2 * bv l + b.toNat

/-- The `w` low bits of `v`, little-endian. -/
def enc : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, v => decide (v % 2 = 1) :: enc w (v / 2)

@[simp] theorem length_enc (w v : ℕ) : (enc w v).length = w := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih => simp [enc, ih]

theorem bv_enc (w v : ℕ) : bv (enc w v) = v % 2 ^ w := by
  induction w generalizing v with
  | zero => simp [enc, bv, Nat.mod_one]
  | succ w ih =>
    simp only [enc, bv, ih]
    rw [pow_succ', Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]; omega

theorem enc_bv (l : List Bool) : enc l.length (bv l) = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b
    · simp only [List.length_cons, enc, bv, Bool.toNat_false, add_zero]
      have h1 : 2 * bv l / 2 = bv l := by omega
      rw [h1, ih]; simp
    · simp only [List.length_cons, enc, bv, Bool.toNat_true]
      have h1 : (2 * bv l + 1) / 2 = bv l := by omega
      rw [h1, ih]; simp

theorem bv_lt (l : List Bool) : bv l < 2 ^ l.length := by
  induction l with
  | nil => simp [bv]
  | cons b l ih =>
    simp only [bv, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- Big-endian value: the lexicographic order on tables of one length. -/
def val (T : List Bool) : ℕ := bv T.reverse

theorem val_inj {T T' : List Bool} (hl : T.length = T'.length) (hv : val T = val T') :
    T = T' := by
  have h1 := enc_bv T.reverse
  have h2 := enc_bv T'.reverse
  simp only [List.length_reverse] at h1 h2
  unfold val at hv
  rw [hl, hv, h2] at h1
  exact List.reverse_injective h1.symm

/-! ### Parameters -/

/-- Table length. -/
def NN (k n : ℕ) : ℕ := 2 ^ mm k n
/-- Size bound. -/
def BB (k n : ℕ) : ℕ := n ^ (k + 1)
/-- Index width. -/
def ww (k n : ℕ) : ℕ := n + BB k n + 1
/-- Gate field width. -/
def gw (k n : ℕ) : ℕ := 2 + 2 * (1 + ww k n)
/-- Circuit string length. -/
def ell (k n : ℕ) : ℕ := BB k n * gw k n + ww k n

/-! ### Decoding circuits -/

def decOp (a b : Bool) : GateOp := if a then GateOp.not else if b then GateOp.or else GateOp.and

def decSlot (w : ℕ) (s : List Bool) : List ℕ :=
  if s.headD false then [bv ((s.drop 1).take w)] else []

def decGate (w : ℕ) (s : List Bool) : Gate :=
  ⟨decOp (s.getD 0 false) (s.getD 1 false), decSlot w (s.drop 2) ++ decSlot w (s.drop (3 + w))⟩

def decGates (w : ℕ) : ℕ → List Bool → List Gate
  | 0, _ => []
  | c + 1, s => decGate w (s.take (2 + 2 * (1 + w))) :: decGates w c (s.drop (2 + 2 * (1 + w)))

/-- The circuit a string stands for at length `n`. -/
def decCirc (k n : ℕ) (s : List Bool) : Circuit :=
  ⟨decGates (ww k n) (BB k n) s, bv ((s.drop (BB k n * gw k n)).take (ww k n))⟩

theorem length_decGates (w c : ℕ) (s : List Bool) : (decGates w c s).length = c := by
  induction c generalizing s with
  | zero => rfl
  | succ c ih => simp [decGates, ih]

theorem decCirc_basic (k n : ℕ) (s : List Bool) : Basic (decCirc k n s) := by
  have : ∀ w c (s : List Bool), ∀ g ∈ decGates w c s,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    intro w c
    induction c with
    | zero => intro s g hg; simp [decGates] at hg
    | succ c ih =>
      intro s g hg
      simp only [decGates, List.mem_cons] at hg
      rcases hg with rfl | hg
      · constructor
        · simp only [decGate, decOp]; split_ifs <;> simp
        · simp only [decGate, decSlot, List.length_append]; split_ifs <;> simp
      · exact ih _ g hg
  exact this _ _ s

theorem decCirc_size (k n : ℕ) (s : List Bool) : (decCirc k n s).size = BB k n :=
  length_decGates _ _ _

/-! ### Encoding descriptors -/

def encOp : Fin 3 → List Bool
  | 0 => [false, false]
  | 1 => [false, true]
  | 2 => [true, false]

def encSlot {M : ℕ} (w : ℕ) : Option (Fin M) → List Bool
  | none => false :: List.replicate w false
  | some i => true :: enc w i

def encGate {M : ℕ} (w : ℕ) (d : GD M) : List Bool :=
  encOp d.1 ++ encSlot w d.2.1 ++ encSlot w d.2.2

def encGs {M : ℕ} (w : ℕ) : List (GD M) → List Bool
  | [] => []
  | d :: ds => encGate w d ++ encGs w ds

/-- The string of a descriptor. -/
def encCirc {n s : ℕ} (w : ℕ) (d : CD n s) : List Bool :=
  encGs w d.1.toList ++ enc w d.2.val

@[simp] theorem length_encOp (o : Fin 3) : (encOp o).length = 2 := by
  fin_cases o <;> rfl

@[simp] theorem length_encSlot {M : ℕ} (w : ℕ) (a : Option (Fin M)) :
    (encSlot w a).length = 1 + w := by
  cases a <;> simp [encSlot] <;> omega

@[simp] theorem length_encGate {M : ℕ} (w : ℕ) (d : GD M) :
    (encGate w d).length = 2 + 2 * (1 + w) := by
  simp [encGate]; omega

theorem length_encGs {M : ℕ} (w : ℕ) (ds : List (GD M)) :
    (encGs w ds).length = ds.length * (2 + 2 * (1 + w)) := by
  induction ds with
  | nil => simp [encGs]
  | cons d ds ih => simp [encGs, ih]; ring

theorem decSlot_encSlot {M : ℕ} (w : ℕ) (hM : M ≤ 2 ^ w) (a : Option (Fin M))
    (r : List Bool) : decSlot w (encSlot w a ++ r) = a.toList.map Fin.val := by
  cases a with
  | none => simp [decSlot, encSlot]
  | some i =>
    simp only [decSlot, encSlot, List.cons_append, List.headD_cons, ite_true, List.drop_succ_cons,
      List.drop_zero, Option.toList_some, List.map_cons, List.map_nil]
    rw [List.take_left' (by simp), bv_enc, Nat.mod_eq_of_lt (by omega)]

theorem decGate_encGate {M : ℕ} (w : ℕ) (hM : M ≤ 2 ^ w) (d : GD M) :
    decGate w (encGate w d) = decodeGate d := by
  obtain ⟨o, a, b⟩ := d
  have h3 : decOp ((encGate w (o, a, b)).getD 0 false) ((encGate w (o, a, b)).getD 1 false) =
      (match o with
        | 0 => GateOp.and
        | 1 => GateOp.or
        | 2 => GateOp.not) := by
    fin_cases o <;> simp [encGate, encOp, decOp]
  have h1 : (encGate w (o, a, b)).drop 2 = encSlot w a ++ encSlot w b := by
    simp only [encGate, List.append_assoc]
    rw [List.drop_left' (by simp)]
  have h2 : (encGate w (o, a, b)).drop (3 + w) = encSlot w b := by
    simp only [encGate, List.append_assoc]
    rw [← List.append_assoc, List.drop_left' (by simp; omega)]
  simp only [decGate, decodeGate, h1, h2, h3, decSlot_encSlot w hM]
  have := decSlot_encSlot w hM b []
  simp only [List.append_nil] at this
  rw [this, List.map_append]
  fin_cases o <;> rfl

theorem decGates_encGs {M : ℕ} (w : ℕ) (hM : M ≤ 2 ^ w) (ds : List (GD M)) (r : List Bool) :
    decGates w ds.length (encGs w ds ++ r) = ds.map decodeGate := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.length_cons, decGates, encGs, List.append_assoc, List.map_cons]
    rw [List.take_left' (by simp), List.drop_left' (by simp), ih, decGate_encGate w hM]

theorem decCirc_encCirc (k n : ℕ) (d : CD n (BB k n)) :
    decCirc k n (encCirc (ww k n) d) = decode d := by
  have hM : n + BB k n + 1 ≤ 2 ^ ww k n := (Nat.lt_two_pow_self).le
  have hl : (encGs (ww k n) d.1.toList).length = BB k n * gw k n := by
    rw [length_encGs]; simp [gw]
  simp only [decCirc, decode, encCirc]
  congr 1
  · have := decGates_encGs (ww k n) hM d.1.toList (enc (ww k n) d.2.val)
    rw [List.Vector.toList_length] at this
    exact this
  · rw [List.drop_left' hl, List.take_of_length_le (by simp), bv_enc,
      Nat.mod_eq_of_lt (lt_of_lt_of_le d.2.isLt hM)]

theorem length_encCirc (k n : ℕ) (d : CD n (BB k n)) :
    (encCirc (ww k n) d).length = ell k n := by
  simp [encCirc, length_encGs, ell, gw]

end PEqualNP.General.Kannan
