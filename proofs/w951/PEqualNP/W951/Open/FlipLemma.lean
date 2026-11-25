import Mathlib
import PEqualNP.W951.SearchCheck

/-!
# FlipLemma: the per-set flip lemma S3(a), any number of NOT gates

Statement (`research/notes/beyond-one-not.md`, S3(a), `FlipClasses.local`): for every correct circuit, every
set `S` and every zero point `Z` of `S`, at least `|S| - 1` flip classes have `|D| ≥ 2` at `(S, Z)`,
where `D(g) = {u ∈ S : g(Z + e_u) ≠ g(Z)}` and a flip class is a wire function up to complement.

* `Core.core`: the graph argument on an abstract list of wire functions, stated with colourings
  (a colouring of the points of `S` in which every `D` met so far is one colour; a new class merges
  at most two colours).
* `flip_lemma`: the statement for `SearchCheck.Circ` (bit-parallel tables `tt`, any number of NOT
  gates, opcode `≥ 2` is NOT), assuming `correctB C = true`.
-/

namespace PEqualNP.W951.FlipLemma

open Classical

/-! ## The abstract graph argument -/

namespace Core

variable {V : Type*}

/-- `D(f)` at the zero point `z`, for the set `S`, with `flip u` the point `z + e_u`. -/
noncomputable def dset (S : Finset ℕ) (flip : ℕ → V) (z : V) (f : V → Bool) : Finset ℕ :=
  S.filter (fun u => f (flip u) ≠ f z)

/-- the class of a wire function: itself and its complement -/
noncomputable def classOf (f : V → Bool) : Finset (V → Bool) := {f, fun v => !f v}

/-- the flip classes among the first `m` wires: classes of wires with `|D| ≥ 2` -/
noncomputable def classes (S : Finset ℕ) (flip : ℕ → V) (z : V) (w : ℕ → V → Bool) (m : ℕ) :
    Finset (Finset (V → Bool)) :=
  ((Finset.range m).filter (fun k => 2 ≤ (dset S flip z (w k)).card)).image (fun k => classOf (w k))

/-- one colour on a set -/
def Mono (col : ℕ → ℕ) (A : Finset ℕ) : Prop := ∀ u ∈ A, ∀ v ∈ A, col u = col v

lemma dset_not (S : Finset ℕ) (flip : ℕ → V) (z : V) (f : V → Bool) :
    dset S flip z (fun v => !f v) = dset S flip z f := by
  unfold dset
  apply Finset.filter_congr
  intro u _
  cases h1 : f (flip u) <;> cases h2 : f z <;> simp [h1, h2]

lemma dset_eq_of_classOf (S : Finset ℕ) (flip : ℕ → V) (z : V) {f g : V → Bool}
    (h : classOf f = classOf g) : dset S flip z f = dset S flip z g := by
  have hf : f ∈ classOf g := by rw [← h]; simp [classOf]
  simp only [classOf, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl
  · rfl
  · exact dset_not S flip z g

lemma dset_op (S : Finset ℕ) (flip : ℕ → V) (z : V) (op : Bool → Bool → Bool)
    (x y : V → Bool) :
    dset S flip z (fun v => op (x v) (y v)) ⊆ dset S flip z x ∪ dset S flip z y := by
  intro u hu
  simp only [dset, Finset.mem_filter, Finset.mem_union] at hu ⊢
  by_contra hc
  push Not at hc
  exact hu.2 (by rw [hc.1 hu.1, hc.2 hu.1])

/-- an input of a gate: a constant (no flips) or an earlier wire -/
def Earlier (S : Finset ℕ) (flip : ℕ → V) (z : V) (w : ℕ → V → Bool) (k : ℕ) (A : Finset ℕ) :
    Prop :=
  A = ∅ ∨ ∃ a < k, A = dset S flip z (w a)

/-- The per-set lemma, abstract form. Wires `0 .. N-1`; every wire has `|D| ≤ 1` or its `D` lies in
the union of the `D`s of two earlier wires (or constants); some wire has `D = S`. Then
`|S| ≤ #classes + 1`. -/
theorem core (S : Finset ℕ) (flip : ℕ → V) (z : V) (w : ℕ → V → Bool) (N : ℕ)
    (hstep : ∀ k < N, (dset S flip z (w k)).card ≤ 1 ∨
      ∃ A B, Earlier S flip z w k A ∧ Earlier S flip z w k B ∧ dset S flip z (w k) ⊆ A ∪ B)
    (hout : ∃ k < N, dset S flip z (w k) = S) :
    S.card ≤ (classes S flip z w N).card + 1 := by
  set D : ℕ → Finset ℕ := fun k => dset S flip z (w k) with hD
  -- invariant
  have inv : ∀ m ≤ N, ∃ col : ℕ → ℕ, (∀ k < m, Mono col (D k)) ∧
      S.card ≤ (S.image col).card + (classes S flip z w m).card := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨id, fun k hk => absurd hk (Nat.not_lt_zero _), ?_⟩
      simp
    | succ m ih =>
      intro hm
      obtain ⟨col, hmono, hcard⟩ := ih (Nat.le_of_succ_le hm)
      have hsub : classes S flip z w m ⊆ classes S flip z w (m + 1) := by
        intro c hc
        simp only [classes, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hc ⊢
        obtain ⟨k, ⟨hk1, hk2⟩, hk3⟩ := hc
        exact ⟨k, ⟨by omega, hk2⟩, hk3⟩
      have hle := Finset.card_le_card hsub
      -- case: D m has at most one point
      by_cases h1 : (D m).card ≤ 1
      · refine ⟨col, ?_, by omega⟩
        intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact hmono k hk
        · intro u hu v hv
          rw [Finset.card_le_one] at h1
          rw [h1 u hu v hv]
      -- case: the class is old
      by_cases hold : ∃ j < m, 2 ≤ (D j).card ∧ classOf (w j) = classOf (w m)
      · obtain ⟨j, hj, _, hcl⟩ := hold
        refine ⟨col, ?_, by omega⟩
        intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact hmono k hk
        · have : D k = D j := (dset_eq_of_classOf S flip z hcl).symm
          rw [this]; exact hmono j hj
      -- case: a new class, merging at most two colours
      have h2 : 2 ≤ (D m).card := by omega
      have hnew : (classes S flip z w (m + 1)).card = (classes S flip z w m).card + 1 := by
        have heq : classes S flip z w (m + 1) =
            insert (classOf (w m)) (classes S flip z w m) := by
          have h2' : 2 ≤ (dset S flip z (w m)).card := h2
          simp only [classes, Finset.range_add_one, Finset.filter_insert, h2', ite_true,
            Finset.image_insert]
        have hnot : classOf (w m) ∉ classes S flip z w m := by
          intro hc
          simp only [classes, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hc
          obtain ⟨k, ⟨hk1, hk2⟩, hk3⟩ := hc
          exact hold ⟨k, hk1, hk2, hk3⟩
        rw [heq, Finset.card_insert_of_notMem hnot]
      have hm' : m < N := Nat.lt_of_succ_le hm
      rcases hstep m hm' with h | ⟨A, B, hA, hB, hAB⟩
      · exact absurd h h1
      have monoE : ∀ A, Earlier S flip z w m A → Mono col A := by
        intro A hA
        rcases hA with rfl | ⟨a, ha, rfl⟩
        · intro u hu; simp at hu
        · exact hmono a ha
      have mA := monoE A hA
      have mB := monoE B hB
      let ca : ℕ := if h : A.Nonempty then col h.choose else 0
      let cb : ℕ := if h : B.Nonempty then col h.choose else 0
      have hca : ∀ u ∈ A, col u = ca := by
        intro u hu
        have hne : A.Nonempty := ⟨u, hu⟩
        simp only [ca, dite_eq_left_of_eq_true (eq_true hne)]
        exact mA u hu _ hne.choose_spec
      have hcb : ∀ u ∈ B, col u = cb := by
        intro u hu
        have hne : B.Nonempty := ⟨u, hu⟩
        simp only [cb, dite_eq_left_of_eq_true (eq_true hne)]
        exact mB u hu _ hne.choose_spec
      let col' : ℕ → ℕ := fun u => if col u = cb then ca else col u
      refine ⟨col', ?_, ?_⟩
      · intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · intro u hu v hv
          simp only [col']
          rw [hmono k hk u hu v hv]
        · have hall : ∀ u ∈ D k, col' u = ca := by
            intro u hu
            rcases Finset.mem_union.mp (hAB hu) with hu | hu
            · simp only [col', hca u hu]
              split_ifs <;> simp_all
            · show (if col u = cb then ca else col u) = ca
              rw [hcb u hu]; simp
          intro u hu v hv
          rw [hall u hu, hall v hv]
      · have himg : S.image col ⊆ insert cb (S.image col') := by
          intro x hx
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
          by_cases hc : col u = cb
          · rw [hc]; exact Finset.mem_insert_self _ _
          · apply Finset.mem_insert_of_mem
            refine Finset.mem_image.mpr ⟨u, hu, ?_⟩
            simp only [col', hc, ite_false]
        have := Finset.card_le_card himg
        have := Finset.card_insert_le cb (S.image col')
        omega
  obtain ⟨col, hmono, hcard⟩ := inv N le_rfl
  obtain ⟨o, ho, hDo⟩ := hout
  have hone : (S.image col).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hm := hmono o ho
    have hDo' : D o = S := hDo
    rw [hDo'] at hm
    exact hm u hu v hv
  omega

end Core

/-! ## The bit-parallel circuits of `SearchCheck` -/

namespace Concrete

open SearchCheck

/-- the value pushed for a gate (the body of the fold in `SearchCheck.tt`) -/
def gv (full : ℕ) (g : Gate) (x y : ℕ) : ℕ :=
  match g.op with
  | 0 => Nat.land x y
  | 1 => Nat.lor x y
  | _ => Nat.xor full x

def stepA (full : ℕ) (w : Array ℕ) (g : Gate) : Array ℕ :=
  w.push (gv full g (w.getD g.a 0) (w.getD g.b 0))

lemma tt_eq (full : ℕ) (ws : List ℕ) (gs : List Gate) :
    tt full ws gs = (gs.foldl (stepA full) ws.toArray).toList := rfl

lemma getD_push (A : Array ℕ) (x i : ℕ) :
    (A.push x).getD i 0 = if i < A.size then A.getD i 0 else if i = A.size then x else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split_ifs with h1 h2 <;> simp_all

lemma getD_ge (A : Array ℕ) (i : ℕ) (h : A.size ≤ i) : A.getD i 0 = 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]; rfl

lemma size_foldl (full : ℕ) (gs : List Gate) (A : Array ℕ) :
    (gs.foldl (stepA full) A).size = A.size + gs.length := by
  induction gs generalizing A with
  | nil => simp
  | cons g gs ih => simp [ih, stepA]; omega

lemma stable (full : ℕ) (gs : List Gate) (A : Array ℕ) (i : ℕ) (hi : i < A.size) :
    (gs.foldl (stepA full) A).getD i 0 = A.getD i 0 := by
  induction gs generalizing A with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [stepA]; omega)]
    simp only [stepA, getD_push, hi, ite_true]

lemma gate (full : ℕ) (gs : List Gate) (A : Array ℕ) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (stepA full) A).getD (A.size + j) 0 =
      gv full gs[j] (((gs.take j).foldl (stepA full) A).getD gs[j].a 0)
        (((gs.take j).foldl (stepA full) A).getD gs[j].b 0) := by
  induction gs generalizing A j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, List.take_zero, List.foldl_nil, List.getElem_cons_zero]
      rw [stable _ _ _ _ (by simp [stepA])]
      simp [stepA]
    | succ j =>
      simp only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ]
      have := ih (stepA full A g) j (by simp at hj; omega)
      rw [show A.size + (j + 1) = (stepA full A g).size + j by simp [stepA]; omega]
      exact this

lemma prefix_getD (full : ℕ) (gs : List Gate) (A : Array ℕ) (j a : ℕ) (hj : j ≤ gs.length) :
    ((gs.take j).foldl (stepA full) A).getD a 0 =
      if a < A.size + j then (gs.foldl (stepA full) A).getD a 0 else 0 := by
  have hsz : ((gs.take j).foldl (stepA full) A).size = A.size + j := by
    rw [size_foldl, List.length_take]; omega
  have hfin : gs.foldl (stepA full) A = (gs.drop j).foldl (stepA full) ((gs.take j).foldl (stepA full) A) := by
    rw [← List.foldl_append, List.take_append_drop]
  split_ifs with h
  · rw [hfin, stable full (gs.drop j) _ a (by omega)]
  · exact getD_ge _ _ (by omega)

/-- `varTT` as a list fold: bit `j` is the bit of the `j`-th row -/
lemma foldr_bits (p : ℕ → Bool) (L : List ℕ) (j : ℕ) :
    (L.foldr (fun r acc => (acc <<< 1) ||| (if p r then 1 else 0)) 0).testBit j =
      (L[j]?.map p).getD false := by
  induction L generalizing j with
  | nil => simp
  | cons r L ih =>
    simp only [List.foldr_cons]
    cases j with
    | zero =>
      simp only [Nat.testBit_or, Nat.testBit_shiftLeft, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some]
      split_ifs <;> simp_all
    | succ j =>
      simp only [Nat.testBit_or, Nat.testBit_shiftLeft, List.getElem?_cons_succ]
      rw [← ih j]
      split_ifs <;> simp [Nat.testBit_succ]

lemma varTT_bit (n i r : ℕ) (hr : r < 2 ^ n) : (varTT n i).testBit r = r.testBit i := by
  unfold varTT
  rw [foldr_bits]
  simp [List.getElem?_range hr]

lemma full_bit (n r : ℕ) (hr : r < 2 ^ n) : (2 ^ (2 ^ n) - 1).testBit r = true := by
  rw [Nat.testBit_two_pow_sub_one]; simpa using hr

/-- the Boolean operation of an opcode -/
def opB (op : ℕ) : Bool → Bool → Bool :=
  match op with
  | 0 => (· && ·)
  | 1 => (· || ·)
  | _ => fun p _ => !p

lemma gv_bit (n : ℕ) (g : Gate) (x y r : ℕ) (hr : r < 2 ^ n) :
    (gv (2 ^ (2 ^ n) - 1) g x y).testBit r = opB g.op (x.testBit r) (y.testBit r) := by
  unfold gv opB
  match g.op with
  | 0 => simp [Nat.land]
  | 1 => simp [Nat.lor]
  | _ + 2 => simp [Nat.xor, full_bit n r hr]

lemma foldl_or_bit (f : ℕ → ℕ) (L : List ℕ) (a r : ℕ) :
    (L.foldl (fun acc u => Nat.lor acc (f u)) a).testBit r =
      (a.testBit r || L.any (fun u => (f u).testBit r)) := by
  induction L generalizing a with
  | nil => simp
  | cons u L ih =>
    simp only [List.foldl_cons, ih, List.any_cons]
    simp [Nat.lor, Bool.or_assoc]

/-- the point `Z + e_u` -/
def flipPt (n : ℕ) (Z : Fin (2 ^ n)) (u : ℕ) : Fin (2 ^ n) :=
  ⟨(Z.val ||| 2 ^ u) % 2 ^ n, Nat.mod_lt _ (by positivity)⟩

/-- the function of wire `k` on the `2^n` rows -/
def wire (C : Circ) (k : ℕ) : Fin (2 ^ C.n) → Bool := fun r => (C.tables.getD k 0).testBit r.val

/-- the flip classes of `C` at `(S, Z)`: wire functions up to complement, among wires with `|D| ≥ 2` -/
noncomputable def flipClasses (C : Circ) (S : List ℕ) (Z : Fin (2 ^ C.n)) :
    Finset (Finset (Fin (2 ^ C.n) → Bool)) :=
  Core.classes S.toFinset (flipPt C.n Z) Z (wire C) C.tables.size

lemma ins_getD (n u : ℕ) (hu : u < n) :
    ((List.range n).map (varTT n)).getD u 0 = varTT n u := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hu]

lemma tables_eq (C : Circ) :
    C.tables = C.gates.foldl (stepA (2 ^ (2 ^ C.n) - 1)) ((List.range C.n).map (varTT C.n)).toArray := by
  simp [Circ.tables, tt_eq]

lemma flipPt_val (n : ℕ) (Z : Fin (2 ^ n)) (u : ℕ) (hu : u < n) :
    (flipPt n Z u).val = Z.val ||| 2 ^ u := by
  unfold flipPt
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow Z.isLt (Nat.pow_lt_pow_right (by norm_num) hu))

lemma tables_size (C : Circ) : C.tables.size = C.n + C.gates.length := by
  rw [tables_eq, size_foldl]; simp

lemma wire_input (C : Circ) (k : ℕ) (hk : k < C.n) (r : Fin (2 ^ C.n)) :
    wire C k r = r.val.testBit k := by
  unfold wire
  rw [tables_eq, stable _ _ _ _ (by simpa using hk)]
  have : ((List.range C.n).map (varTT C.n)).toArray.getD k 0 = varTT C.n k := by
    rw [← ins_getD C.n k hk]
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [this, varTT_bit _ _ _ r.isLt]

/-- **The per-set flip lemma (S3(a)), any number of NOT gates.** For a correct circuit, a set `S`
with output `o`, and a zero point `Z` of `S`: `|S| ≤ #(flip classes with |D| ≥ 2 at (S, Z)) + 1`. -/
theorem flip_lemma (C : Circ) (hC : correctB C = true) (S : List ℕ) (o : ℕ)
    (hSo : (S, o) ∈ C.sets.zip C.outs) (hSn : ∀ u ∈ S, u < C.n)
    (Z : Fin (2 ^ C.n)) (hZ : ∀ u ∈ S, Z.val.testBit u = false) :
    S.toFinset.card ≤ (flipClasses C S Z).card + 1 := by
  set S' := S.toFinset with hS'
  set fl := flipPt C.n Z with hfl
  have hfv : ∀ u ∈ S', (fl u).val = Z.val ||| 2 ^ u := fun u hu =>
    flipPt_val C.n Z u (hSn u (List.mem_toFinset.mp hu))
  have hD : ∀ f, Core.dset S' fl Z f = S'.filter (fun u => f (fl u) ≠ f Z) := fun _ => rfl
  -- the output wire computes the OR of S
  have hout_fun : ∀ r : Fin (2 ^ C.n), wire C o r = S.any (fun u => r.val.testBit u) := by
    intro r
    unfold correctB at hC
    have h := List.all_eq_true.mp hC (S, o) hSo
    simp only [beq_iff_eq] at h
    unfold wire
    rw [h, foldl_or_bit]
    simp only [Nat.zero_testBit, Bool.false_or]
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true]
    constructor <;> rintro ⟨u, hu, h⟩ <;> refine ⟨u, hu, ?_⟩
    · rwa [ins_getD _ _ (hSn u hu), varTT_bit _ _ _ r.isLt] at h
    · rwa [ins_getD _ _ (hSn u hu), varTT_bit _ _ _ r.isLt]
  have hDout : Core.dset S' fl Z (wire C o) = S' := by
    rw [hD]
    apply Finset.filter_true_of_mem
    intro u hu
    rw [hout_fun, hout_fun]
    have hz : S.any (fun v => Z.val.testBit v) = false := by
      rw [List.any_eq_false]; intro v hv; rw [hZ v hv]; simp
    have h1 : S.any (fun v => (fl u).val.testBit v) = true := by
      rw [List.any_eq_true]
      refine ⟨u, List.mem_toFinset.mp hu, ?_⟩
      rw [hfv u hu, Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true]
    rw [hz, h1]; simp
  by_cases hS0 : S' = ∅
  · rw [hS0]; simp
  have ho : o < C.tables.size := by
    by_contra hge
    have : Core.dset S' fl Z (wire C o) = ∅ := by
      rw [hD]
      apply Finset.filter_false_of_mem
      intro u _
      simp [wire, getD_ge C.tables o (by omega)]
    exact hS0 (hDout.symm.trans this)
  apply Core.core S' fl Z (wire C) C.tables.size _ ⟨o, ho, hDout⟩
  intro k hk
  by_cases hkn : k < C.n
  · left
    rw [Finset.card_le_one]
    intro u hu v hv
    have key : ∀ x ∈ Core.dset S' fl Z (wire C k), x = k := by
      intro x hx
      rw [hD, Finset.mem_filter] at hx
      rw [wire_input C k hkn, wire_input C k hkn, hfv x hx.1, Nat.testBit_or,
        Nat.testBit_two_pow] at hx
      by_contra hne
      apply hx.2
      simp [hne]
    rw [key u hu, key v hv]
  · right
    obtain ⟨j, rfl⟩ : ∃ j, k = C.n + j := ⟨k - C.n, by omega⟩
    have hj : j < C.gates.length := by rw [tables_size] at hk; omega
    set P := (C.gates.take j).foldl (stepA (2 ^ (2 ^ C.n) - 1)) ((List.range C.n).map (varTT C.n)).toArray with hP
    set g := C.gates[j] with hg
    have hsz : ((List.range C.n).map (varTT C.n)).toArray.size = C.n := by simp
    have hfun : wire C (C.n + j) =
        fun r => opB g.op ((P.getD g.a 0).testBit r.val) ((P.getD g.b 0).testBit r.val) := by
      funext r
      unfold wire
      rw [tables_eq]
      have := gate (2 ^ (2 ^ C.n) - 1) C.gates ((List.range C.n).map (varTT C.n)).toArray j hj
      rw [hsz] at this
      rw [this, gv_bit C.n _ _ _ _ r.isLt]
    have hearly : ∀ a, Core.Earlier S' fl Z (wire C) (C.n + j)
        (Core.dset S' fl Z (fun r => (P.getD a 0).testBit r.val)) := by
      intro a
      rw [hP, prefix_getD _ _ _ _ _ hj.le, hsz]
      split_ifs with ha
      · right
        refine ⟨a, ha, ?_⟩
        unfold wire
        rw [tables_eq]
      · left
        rw [hD]
        apply Finset.filter_false_of_mem
        intro u _
        simp
    refine ⟨_, _, hearly g.a, hearly g.b, ?_⟩
    rw [hfun]
    exact Core.dset_op S' fl Z (opB g.op) _ _

end Concrete

/-- on the 10-gate-witness counterexample to C4w (`SearchCheck.t4`, 4 NOT gates), the lemma applies to
the set `{0,1,2,3}` at every zero point. -/
example (Z : Fin (2 ^ SearchCheck.t4.n)) (hZ : ∀ u ∈ [0, 1, 2, 3], Z.val.testBit u = false) :
    [0, 1, 2, 3].toFinset.card ≤ (Concrete.flipClasses SearchCheck.t4 [0, 1, 2, 3] Z).card + 1 :=
  Concrete.flip_lemma _ SearchCheck.t4_correct _ 39 (by decide) (by decide) Z hZ

#print axioms Concrete.flip_lemma

end PEqualNP.W951.FlipLemma
