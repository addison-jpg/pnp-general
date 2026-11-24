import Mathlib
import PEqualNP.W951.AsteroidSound
import PEqualNP.W951.F2Induct
/-!
# AsteroidSound2: asteroid's witness counts are the project's `F2` (layer 4)

Serves the asteroid language (task `asteroid-bridge`). `Asteroid.lean` counts, at a cube `q` (a bit mask),
the OR gates whose table has a witness (`orWitnessAt C q`) and the base (`baseAt C q`). `F2Induct.lean`
defines `F2 gates S Q`: the OR gate wires of the real circuit with a real witness for a set alive at `Q`.

Under `Circ.SetsOk C` (every set is a list without repetition of points `< n`), with
`maskOf Q` the bit mask of `Q : Finset (Fin n)`:

* `hasWitnessAt_iff_F2Wit`: the table of wire `i` has a witness above `maskOf Q` iff wire `i` has a real
  witness (`F2Wit`) for some set alive at `Q`.
* **`card_F2_eq_orWitnessAt`**: `(F2 C.toGates C.setFin Q).card = orWitnessAt C (maskOf Q)`.
* `baseAt_eq_baseDQ`: `baseAt C (maskOf Q) = baseDQ C.setFin ∅ Q`.
* **`slackNonnegAll_sound`**: `slackNonnegAll C = true` ⇒ `baseDQ C.setFin ∅ Q ≤ (F2 C.toGates C.setFin Q).card`
  at every `Q`; `MUF2_of_slackNonnegAll`, `MUF2_of_slackGe` (one cube is enough for `MUF2`), and
  `base_le_gates_of_slackGe`: the 951 bound `∑ (|S_w| − 1) ≤ gates` for this circuit.

Why `SetsOk` is needed: `hasWitnessAt` counts list positions (`(S.filter …).length ≥ 2`), so a repeated
point would count twice where `F2Wit` asks for `u ≠ u'`; and for a point `u ≥ n` it reads bit
`r ||| 2^u ≥ 2^n` of the table, which is outside the rows (a NOT gate leaves ones there).
-/
namespace SearchCheck

open PEqualNP.CircuitLowerBounds (Circuit GateOp)
open PEqualNP.Outside.L_meta_951_aux (val F2 F2Wit mem_F2 aliveSets mem_aliveSets baseDQ baseDQ_empty
  IsOrAt MUF2 card_F2_le)

/-- the bit mask of a set of points -/
def maskOf {n : Nat} (Q : Finset (Fin n)) : Nat := Nat.ofBits fun v => decide (v ∈ Q)

/-- every set is a list without repetition of points `< n` -/
def Circ.SetsOk (C : Circ) : Prop := ∀ S ∈ C.sets, S.Nodup ∧ ∀ u ∈ S, u < C.n

/-- the input vector of row `r` -/
def rowOf (n r : Nat) : Fin n → Bool := fun v => r.testBit v

theorem ofBits_rowOf {n r : Nat} (hr : r < 2 ^ n) : Nat.ofBits (rowOf n r) = r := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · rw [Nat.testBit_ofBits_lt _ _ hi]; rfl
  · rw [Nat.testBit_ofBits_ge _ _ (not_lt.mp hi), testBit_eq_false_of_ge hr (not_lt.mp hi)]

theorem rowOf_ofBits {n : Nat} (Z : Fin n → Bool) : rowOf n (Nat.ofBits Z) = Z := by
  funext v
  exact Nat.testBit_ofBits_lt Z v.val v.isLt

/-- bit `r` of the table of wire `k` is the project's value of wire `k` on the input of row `r` -/
theorem table_val (C : Circ) {r : Nat} (hr : r < 2 ^ C.n) (k : Nat) :
    (C.tables.getD k 0).testBit r = val C.toGates (rowOf C.n r) k := by
  rw [tables_testBit C hr]
  conv_lhs => rw [← ofBits_rowOf hr]
  rw [wiresAt_eq_wires C _ 0]
  rfl

theorem rowOf_or {n r u : Nat} (hu : u < n) :
    rowOf n (r ||| 2 ^ u) = Function.update (rowOf n r) ⟨u, hu⟩ true := by
  funext v
  by_cases h : v = ⟨u, hu⟩
  · subst h; simp [rowOf, Nat.testBit_or, Nat.testBit_two_pow_self]
  · have h' : u ≠ v.val := fun e => h (Fin.ext e.symm)
    simp [rowOf, Function.update_of_ne h, Nat.testBit_or, h']

theorem or_two_pow_lt {n r u : Nat} (hr : r < 2 ^ n) (hu : u < n) : r ||| 2 ^ u < 2 ^ n :=
  Nat.or_lt_two_pow hr (Nat.pow_lt_pow_right (by norm_num) hu)

theorem testBit_maskOf {n : Nat} (Q : Finset (Fin n)) (v : Fin n) :
    (maskOf Q).testBit v.val = decide (v ∈ Q) :=
  Nat.testBit_ofBits_lt _ v.val v.isLt

theorem maskOf_empty {n : Nat} : maskOf (∅ : Finset (Fin n)) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · simp [maskOf, Nat.testBit_ofBits_lt _ _ hi]
  · simp [maskOf, Nat.testBit_ofBits_ge _ _ (not_lt.mp hi)]

theorem mem_setFin (C : Circ) (w : Fin C.sets.length) (v : Fin C.n) :
    v ∈ C.setFin w ↔ v.val ∈ C.sets[w.val] := by
  simp [Circ.setFin]

/-- a set is alive at `Q` iff the mask of `Q` avoids it -/
theorem alive_iff (C : Circ) (hC : C.SetsOk) (w : Fin C.sets.length) (Q : Finset (Fin C.n)) :
    Disjoint (C.setFin w) Q ↔ ∀ s ∈ C.sets[w.val], (maskOf Q).testBit s = false := by
  have hS := hC _ (List.getElem_mem w.isLt)
  rw [Finset.disjoint_left]
  constructor
  · intro h s hs
    have hsn := hS.2 s hs
    have h1 := h ((mem_setFin C w ⟨s, hsn⟩).mpr hs)
    have h2 := testBit_maskOf Q ⟨s, hsn⟩
    simp only [h1, decide_false] at h2
    exact h2
  · intro h v hv hvQ
    have h1 := h v.val ((mem_setFin C w v).mp hv)
    rw [testBit_maskOf, decide_eq_false_iff_not] at h1
    exact h1 hvQ

theorem hasWitnessAt_iff (n : Nat) (sets : List (List Nat)) (q t : Nat) :
    hasWitnessAt n sets q t = true ↔
      ∃ S ∈ sets, (∀ s ∈ S, q.testBit s = false) ∧ ∃ r, r < 2 ^ n ∧ q &&& r = q ∧
        (∀ s ∈ S, r.testBit s = false) ∧ t.testBit r = false ∧
        2 ≤ (S.filter fun u => t.testBit (r ||| 2 ^ u)).length := by
  simp only [hasWitnessAt, List.any_eq_true, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, List.mem_range, beq_iff_eq, ge_iff_le]
  constructor
  · rintro ⟨S, hS, h1, r, hr, ⟨⟨h2, h3⟩, h4⟩, h5⟩
    exact ⟨S, hS, h1, r, hr, h2, h3, h4, h5⟩
  · rintro ⟨S, hS, h1, r, hr, h2, h3, h4, h5⟩
    exact ⟨S, hS, h1, r, hr, ⟨⟨h2, h3⟩, h4⟩, h5⟩

theorem exists_two_of_filter {α : Type} (p : α → Bool) {l : List α} (hl : l.Nodup)
    (h : 2 ≤ (l.filter p).length) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ a ≠ b ∧ p a = true ∧ p b = true := by
  have hn := hl.filter p
  have hmem : ∀ x ∈ l.filter p, x ∈ l ∧ p x = true := fun x hx => List.mem_filter.mp hx
  revert hn h hmem
  generalize l.filter p = f
  intro h hn hmem
  match f, hn, h, hmem with
  | a :: b :: _, hn, _, hmem =>
    refine ⟨a, b, (hmem a (by simp)).1, (hmem b (by simp)).1, ?_, (hmem a (by simp)).2,
      (hmem b (by simp)).2⟩
    intro e
    subst e
    simp at hn
  | [], _, h, _ => simp at h
  | [_], _, h, _ => simp at h

theorem two_le_filter {α : Type} (p : α → Bool) {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hne : a ≠ b) (hpa : p a = true) (hpb : p b = true) : 2 ≤ (l.filter p).length := by
  have ha' : a ∈ l.filter p := List.mem_filter.mpr ⟨ha, hpa⟩
  have hb' : b ∈ l.filter p := List.mem_filter.mpr ⟨hb, hpb⟩
  revert ha' hb'
  generalize l.filter p = f
  intro ha' hb'
  match f, ha', hb' with
  | [], ha', _ => simp at ha'
  | [x], ha', hb' =>
    simp only [List.mem_singleton] at ha' hb'
    exact absurd (ha'.trans hb'.symm) hne
  | _ :: _ :: _, _, _ => simp

/-- **The witness of asteroid is the real witness of `F2`.** -/
theorem hasWitnessAt_iff_F2Wit (C : Circ) (hC : C.SetsOk) (Q : Finset (Fin C.n)) (i : Nat) :
    hasWitnessAt C.n C.sets (maskOf Q) (C.tables.getD i 0) = true ↔
      ∃ w ∈ aliveSets C.setFin Q, F2Wit C.toGates (C.setFin w) Q i := by
  rw [hasWitnessAt_iff]
  constructor
  · rintro ⟨S, hS, hal, r, hr, hqr, hrS, ht, hcount⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hS
    have hSok := hC _ hS
    obtain ⟨u, u', hu, hu', hne, hpu, hpu'⟩ := exists_two_of_filter _ hSok.1 hcount
    have hun := hSok.2 u hu
    have hun' := hSok.2 u' hu'
    refine ⟨⟨j, hj⟩, mem_aliveSets.mpr ((alive_iff C hC ⟨j, hj⟩ Q).mpr hal), rowOf C.n r,
      ⟨u, hun⟩, ⟨u', hun'⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (mem_setFin C ⟨j, hj⟩ ⟨u, hun⟩).mpr hu
    · exact (mem_setFin C ⟨j, hj⟩ ⟨u', hun'⟩).mpr hu'
    · intro e; exact hne (congrArg Fin.val e)
    · intro x hx
      exact hrS _ ((mem_setFin C ⟨j, hj⟩ x).mp hx)
    · intro x hx
      have h1 := congrArg (fun z => z.testBit x.val) hqr
      simp only [Nat.testBit_and, testBit_maskOf, hx, decide_true, Bool.true_and] at h1
      exact h1
    · rw [← table_val C hr]; exact ht
    · rw [← rowOf_or hun, ← table_val C (or_two_pow_lt hr hun)]; exact hpu
    · rw [← rowOf_or hun', ← table_val C (or_two_pow_lt hr hun')]; exact hpu'
  · rintro ⟨w, hw, Z, u, u', hu, hu', hne, hZR, hZQ, h0, h1, h2⟩
    have hr : Nat.ofBits Z < 2 ^ C.n := Nat.ofBits_lt_two_pow Z
    have hZ : rowOf C.n (Nat.ofBits Z) = Z := rowOf_ofBits Z
    have hS := hC _ (List.getElem_mem w.isLt)
    refine ⟨C.sets[w.val], List.getElem_mem _, (alive_iff C hC w Q).mp (mem_aliveSets.mp hw),
      Nat.ofBits Z, hr, ?_, ?_, ?_, ?_⟩
    · apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and]
      by_cases hk : k < C.n
      · rw [show (maskOf Q).testBit k = decide ((⟨k, hk⟩ : Fin C.n) ∈ Q) from
          testBit_maskOf Q ⟨k, hk⟩, Nat.testBit_ofBits_lt Z k hk]
        by_cases hq : (⟨k, hk⟩ : Fin C.n) ∈ Q
        · simp [hq, hZQ _ hq]
        · simp [hq]
      · simp [maskOf, Nat.testBit_ofBits_ge _ _ (not_lt.mp hk)]
    · intro s hs
      have hsn := hS.2 s hs
      rw [Nat.testBit_ofBits_lt Z s hsn]
      exact hZR ⟨s, hsn⟩ ((mem_setFin C w ⟨s, hsn⟩).mpr hs)
    · rw [table_val C hr, hZ]; exact h0
    · refine two_le_filter _ ((mem_setFin C w u).mp hu) ((mem_setFin C w u').mp hu')
        (fun e => hne (Fin.ext e)) ?_ ?_
      · show (C.tables.getD i 0).testBit (Nat.ofBits Z ||| 2 ^ u.val) = true
        rw [table_val C (or_two_pow_lt hr u.isLt), rowOf_or u.isLt, hZ]; exact h1
      · show (C.tables.getD i 0).testBit (Nat.ofBits Z ||| 2 ^ u'.val) = true
        rw [table_val C (or_two_pow_lt hr u'.isLt), rowOf_or u'.isLt, hZ]; exact h2

/-! ## The count -/

theorem foldl_snoc_length {α β : Type} (f : List α → β → α) (gs : List β) (T : List α) :
    (gs.foldl (fun w g => w ++ [f w g]) T).length = T.length + gs.length := by
  induction gs generalizing T with
  | nil => rfl
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

theorem tables_length (C : Circ) : C.tables.toList.length = C.n + C.gates.length := by
  unfold Circ.tables
  simp only []
  rw [tt_eq, foldl_snoc_length]
  simp

/-- the OR witness count as a count over gate numbers -/
theorem orWitnessAt_eq (C : Circ) (q : Nat) :
    orWitnessAt C q = ((List.range C.gates.length).filter fun k =>
      hasWitnessAt C.n C.sets q (C.tables.getD (C.n + k) 0) &&
        ((C.gates.getD k ⟨0, 0, 0⟩).op == 1)).length := by
  have hsz : C.tables.size = C.n + C.gates.length := by
    have := tables_length C
    simpa only [Array.length_toList] using this
  have hz : (C.tables.toList.drop C.n).zip C.gates = (List.range C.gates.length).map fun k =>
      (C.tables.getD (C.n + k) 0, C.gates.getD k ⟨0, 0, 0⟩) := by
    apply List.ext_getElem
    · simp [hsz]
    · intro k h1 h2
      have hk : k < C.gates.length := by simpa using h2
      have hk' : C.n + k < C.tables.size := by omega
      simp [List.getD_eq_getElem?_getD, hk, Array.getD_eq_getD_getElem?, hk']
  unfold orWitnessAt orWitnessAtWith orTables
  simp only [hz, List.filter_map, List.length_map, List.filter_filter]
  rfl

theorem toGate_or_iff (g : Gate) : g.toGate.op = GateOp.or ↔ g.op = 1 := by
  rcases g with ⟨op, a, b⟩
  match op with
  | 0 => simp [Gate.toGate]
  | 1 => simp [Gate.toGate]
  | k + 2 => simp [Gate.toGate]

theorem isOrAt_toGates (C : Circ) (k : Nat) :
    IsOrAt C.toGates k ↔ k < C.gates.length ∧ (C.gates.getD k ⟨0, 0, 0⟩).op = 1 := by
  unfold IsOrAt Circ.toGates
  rw [List.getElem?_map]
  constructor
  · rintro ⟨g, hg, hop⟩
    by_cases hk : k < C.gates.length
    · simp only [List.getElem?_eq_getElem hk, Option.map_some, Option.some.injEq] at hg
      subst hg
      refine ⟨hk, ?_⟩
      simpa [List.getD_eq_getElem?_getD, hk] using (toGate_or_iff _).mp hop
    · simp [List.getElem?_eq_none (not_lt.mp hk)] at hg
  · rintro ⟨hk, hop⟩
    refine ⟨(C.gates[k]).toGate, by simp [hk], (toGate_or_iff _).mpr ?_⟩
    simpa [List.getD_eq_getElem?_getD, hk] using hop

/-- **Layer 4.** asteroid's OR witness count at the cube of `Q` is the size of the project's `F2` at `Q`. -/
theorem card_F2_eq_orWitnessAt (C : Circ) (hC : C.SetsOk) (Q : Finset (Fin C.n)) :
    (F2 C.toGates C.setFin Q).card = orWitnessAt C (maskOf Q) := by
  classical
  rw [orWitnessAt_eq]
  have hF : F2 C.toGates C.setFin Q = ((Finset.range C.gates.length).filter fun k =>
      (hasWitnessAt C.n C.sets (maskOf Q) (C.tables.getD (C.n + k) 0) &&
        ((C.gates.getD k ⟨0, 0, 0⟩).op == 1)) = true).image (fun k => C.n + k) := by
    ext i
    rw [mem_F2, Finset.mem_image]
    constructor
    · rintro ⟨⟨k, rfl, hor⟩, hw⟩
      obtain ⟨hk, hop⟩ := (isOrAt_toGates C k).mp hor
      refine ⟨k, ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨hk, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨(hasWitnessAt_iff_F2Wit C hC Q _).mpr hw, hop⟩
    · rintro ⟨k, hk, rfl⟩
      rw [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hk, hPk⟩ := hk
      simp only [Bool.and_eq_true, beq_iff_eq] at hPk
      exact ⟨⟨k, rfl, (isOrAt_toGates C k).mpr ⟨hk, hPk.2⟩⟩,
        (hasWitnessAt_iff_F2Wit C hC Q _).mp hPk.1⟩
  rw [hF, Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h),
    ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1
  ext k
  simp

/-! ## The base and the slack -/

theorem card_setFin (C : Circ) (hC : C.SetsOk) (w : Fin C.sets.length) :
    (C.setFin w).card = (C.sets[w.val]).length := by
  have hS := hC _ (List.getElem_mem w.isLt)
  rw [← List.toFinset_card_of_nodup hS.1, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext s
  simp only [Finset.mem_map, Fin.valEmbedding_apply, List.mem_toFinset]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact (mem_setFin C w v).mp hv
  · intro hs; exact ⟨⟨s, hS.2 s hs⟩, (mem_setFin C w _).mpr hs, rfl⟩

theorem foldl_add_eq_sum {α : Type} (f : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun acc S => acc + f S) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih]; simp; omega

theorem sum_filter_map {α : Type} (p : α → Bool) (f : α → Nat) (l : List α) :
    ((l.filter p).map f).sum = (l.map fun S => if p S = true then f S else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : p x = true
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

theorem sum_fin_getElem {α : Type} (l : List α) (h : α → Nat) :
    ∑ w : Fin l.length, h l[w.val] = (l.map h).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

/-- asteroid's base at the cube of `Q` is the project's base at `Q` -/
theorem baseAt_eq_baseDQ (C : Circ) (hC : C.SetsOk) (Q : Finset (Fin C.n)) :
    baseAt C (maskOf Q) = baseDQ C.setFin ∅ Q := by
  unfold baseAt baseDQ aliveSets
  rw [foldl_add_eq_sum, sum_filter_map, ← sum_fin_getElem, Finset.sum_filter, Nat.zero_add]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sdiff_empty, card_setFin C hC w]
  have hal := alive_iff C hC w Q
  by_cases h : Disjoint (C.setFin w) Q
  · rw [if_pos h, if_pos]
    simpa [List.all_eq_true] using hal.mp h
  · rw [if_neg h, if_neg]
    intro h'
    exact h (hal.mpr (by simpa [List.all_eq_true] using h'))

/-- **Slack at every cube.** If the kernel check `slackNonnegAll C` succeeds, then at every `Q` the base is
at most the number of OR gates with a real witness, in the project's definitions. -/
theorem slackNonnegAll_sound (C : Circ) (hC : C.SetsOk) (h : slackNonnegAll C = true)
    (Q : Finset (Fin C.n)) : baseDQ C.setFin ∅ Q ≤ (F2 C.toGates C.setFin Q).card := by
  rw [card_F2_eq_orWitnessAt C hC, ← baseAt_eq_baseDQ C hC]
  unfold slackNonnegAll slackNonnegAllWith at h
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h (maskOf Q) (List.mem_range.mpr (Nat.ofBits_lt_two_pow _)))

/-- the slack claim at one cube, in the project's definitions -/
theorem slackGe_sound (C : Circ) (hC : C.SetsOk) (Q : Finset (Fin C.n)) (k : Int)
    (h : slackGe C (maskOf Q) k = true) :
    ((F2 C.toGates C.setFin Q).card : Int) - (baseDQ C.setFin ∅ Q : Int) ≥ k := by
  rw [card_F2_eq_orWitnessAt C hC, ← baseAt_eq_baseDQ C hC]
  exact of_decide_eq_true h

/-- `claim slack(c) >= 0 by lean` gives `MUF2` (`base ≤ |F2|` at the empty cube) -/
theorem MUF2_of_slackGe (C : Circ) (hC : C.SetsOk) (h : slackGe C 0 0 = true) :
    MUF2 C.setFin C.toGates := by
  have h1 := slackGe_sound C hC ∅ 0 (by rw [maskOf_empty]; exact h)
  unfold MUF2
  rw [← baseDQ_empty]
  omega

theorem MUF2_of_slackNonnegAll (C : Circ) (hC : C.SetsOk) (h : slackNonnegAll C = true) :
    MUF2 C.setFin C.toGates := by
  have h1 := slackNonnegAll_sound C hC h ∅
  rwa [baseDQ_empty] at h1

/-- **The 951 bound for one circuit from its slack claim**: `∑ (|S_w| − 1) ≤` number of gates. -/
theorem base_le_gates_of_slackGe (C : Circ) (hC : C.SetsOk) (h : slackGe C 0 0 = true) :
    ∑ w, ((C.setFin w).card - 1) ≤ C.toGates.length :=
  le_trans (MUF2_of_slackGe C hC h) (card_F2_le _ _ _)

/-! ## The instance: `asteroid/examples/first.ast` -/

theorem first_ast_tiny_setsOk : Asteroid_first.tiny.SetsOk := by
  intro S hS
  simp only [Asteroid_first.tiny, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl <;> decide

/-- `claim forall cubes slack(tiny) >= 0 by lean`, read in the project's definitions -/
theorem first_ast_tiny_slack (Q : Finset (Fin Asteroid_first.tiny.n)) :
    baseDQ Asteroid_first.tiny.setFin ∅ Q
      ≤ (F2 Asteroid_first.tiny.toGates Asteroid_first.tiny.setFin Q).card :=
  slackNonnegAll_sound _ first_ast_tiny_setsOk Asteroid_first.tiny_claim4 Q

end SearchCheck

#print axioms SearchCheck.hasWitnessAt_iff_F2Wit
#print axioms SearchCheck.card_F2_eq_orWitnessAt
#print axioms SearchCheck.slackNonnegAll_sound
#print axioms SearchCheck.base_le_gates_of_slackGe
#print axioms SearchCheck.first_ast_tiny_slack
