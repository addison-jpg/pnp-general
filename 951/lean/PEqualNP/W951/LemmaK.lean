import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.EasySets
import PEqualNP.W951.Peel

/-!
# Lemma K (class count) for circuits with at most one NOT

Scaffold's Lemma K (scaffold-951 `work/notes951/lemmaK/`, proof in `extra_constraints.md` §0).
For a correct circuit (AND/OR fan-in 2, at most one NOT), let `U` (`lowUnit`) be the gate wires that
are not NOT gates and are true on at most one unit vector `eof u`. Then

  `#NOT + |U| + ∑_{easy w} (|S w| - 1) + ∑_{hard w} min (|S w| - 1) 2 ≤ gates.length`

(`lemmaK_count`). A set is easy when the NOT is true at its zero point (`NotQuiet`), the same
notion as Theorem E (`easy_card`). Consequences:
* `lemmaK_ex`: with a NOT gate, `1 + |U| + base ≤ s + ex_hard`, `ex_hard = ∑_{hard w} (|S w| - 3)`;
* `K1_bound`: `ex = ∑_w (|S w| - 3) ≤ 1` gives the L-meta-951 bound for every circuit with at most one
  NOT (no minimality, no cleanliness);
* `MinCE.lemmaK`: a minimal counterexample has `(base - s) + 1 + |U| ≤ ex_hard`, so
  `MinCE.ex_ge_two : 2 ≤ ∑_w (|S w| - 3)`.

The classes are those of `small_min2_bound` / `easyHard_bound` (Small3, EasySets): `Ded3` wires
(below `OR (S w)`, two units of `S w`) and `LeafK` wires (`Leaf3` and not constantly true). They are
pairwise disjoint over `w` (`sec_unique3`); the NOT wire lies in none of them, because it is
antitone (`not_antitone`); and every member has at least two units, so `U` meets none of them.
`exists_secondK` is Small3's `exists_second3` without the cleanliness hypothesis and with
`LeafK` in place of `Leaf3`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Kernel

/-- The units of wire `c`: the points `u` with `c` true at `eof u`. -/
noncomputable def unitsOf (n : ℕ) (gates : List Gate) (c : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => val gates (eof u) c = true

open Classical in
/-- The wires of NOT gates. -/
noncomputable def notWires (n : ℕ) (gates : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gates.length)).filter fun c =>
    ∃ h : c - n < gates.length, (gates[c - n]'h).op = GateOp.not

open Classical in
/-- `U`: the gate wires that are not NOT gates and are true on at most one unit vector. -/
noncomputable def lowUnit (n : ℕ) (gates : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gates.length)).filter fun c =>
    (∀ h : c - n < gates.length, (gates[c - n]'h).op ≠ GateOp.not) ∧
      (unitsOf n gates c).card ≤ 1

/-- The second class of Lemma K: `Leaf3` (above `OR (S w)`, above no other `OR (S w')`) and not
constantly true. -/
def LeafK {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (w : Fin m) (c : ℕ) :
    Prop :=
  Leaf3 S gates w c ∧ ∃ x : Fin n → Bool, val gates x c = false

section NotWire

variable {n : ℕ} (gates : List Gate)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates)

include hg hU in
/-- With at most one NOT, the NOT wire is antitone. -/
theorem not_antitone (p : ℕ) (hp : p < gates.length) (hn : (gates[p]'hp).op = GateOp.not)
    (x y : Fin n → Bool) (hxy : ∀ c, x c = true → y c = true)
    (hy : val gates y (n + p) = true) : val gates x (n + p) = true := by
  have hmono : ∀ g' ∈ gates.take p, g'.op = GateOp.and ∨ g'.op = GateOp.or := by
    intro g' hg'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
    have hip : i < p := by have := hi; simp at this; omega
    have hi' : i < gates.length := by omega
    rw [List.getElem_take]
    rcases (hg (gates[i]'hi') (List.getElem_mem hi')).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have := hU i p hi' hp h hn
      omega
  have hlen := (hg (gates[p]'hp) (List.getElem_mem hp)).2
  rw [val_gate gates x p hp]
  rw [val_gate gates y p hp] at hy
  rcases GateShape.not_shape (gates[p]'hp) hn hlen (fun i => val (gates.take p) x i)
    with ⟨_, he⟩ | ⟨a, r, hin, he⟩
  · exact he
  · rcases GateShape.not_shape (gates[p]'hp) hn hlen (fun i => val (gates.take p) y i)
      with ⟨hin', _⟩ | ⟨a', r', hin', he'⟩
    · rw [hin] at hin'; exact absurd hin' (by simp)
    · rw [hin] at hin'
      obtain ⟨rfl, -⟩ := List.cons.inj hin'
      rw [he]
      rw [he'] at hy
      have hya : val (gates.take p) y a = false := by simpa using hy
      cases hxa : val (gates.take p) x a
      · rfl
      · have := mono_val (gates.take p) hmono x y hxy a hxa
        rw [hya] at this
        exact absurd this (by simp)

include hg hU in
/-- A NOT wire (with at most one NOT) is antitone. -/
theorem notWire_antitone (c : ℕ) (hc : c ∈ notWires n gates)
    (x y : Fin n → Bool) (hxy : ∀ c, x c = true → y c = true)
    (hy : val gates y c = true) : val gates x c = true := by
  simp only [notWires, Finset.mem_filter, Finset.mem_Ico] at hc
  obtain ⟨⟨hlo, -⟩, hp, hn⟩ := hc
  have hc' : c = n + (c - n) := by omega
  rw [hc'] at hy ⊢
  exact not_antitone gates hg hU (c - n) hp hn x y hxy hy

end NotWire

section Classes

variable {n m : ℕ} (S : Fin m → Finset (Fin n))
  (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
  (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
  (gates : List Gate) (out : Fin m → ℕ)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates)
  (hev : ∀ (w : Fin m) (x : Fin n → Bool),
    val gates x (out w) = decide (∃ v ∈ S w, x v = true))

/-- A `Ded3` wire has at least two units. -/
theorem ded_two_units (w : Fin m) (c : ℕ) (hd : Ded3 S gates w c) :
    2 ≤ (unitsOf n gates c).card := by
  classical
  obtain ⟨-, u, -, u', -, hne, hu, hu'⟩ := hd
  have hsub : ({u, u'} : Finset (Fin n)) ⊆ unitsOf n gates c := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> simp [unitsOf, *]
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hne] at this

include h2 in
/-- A wire above `OR (S w)` has at least two units. -/
theorem above_two_units (w : Fin m) (c : ℕ) (ha : Above3 S gates w c) :
    2 ≤ (unitsOf n gates c).card := by
  have hsub : S w ⊆ unitsOf n gates c := by
    intro u hu
    simp only [unitsOf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha (eof u) ⟨u, hu, eof_self3 u⟩
  exact (h2 w).trans (Finset.card_le_card hsub)

include h2 hev in
/-- The output wire of `w` is a `Ded3` wire of `w`. -/
theorem out_ded (w : Fin m) : Ded3 S gates w (out w) := by
  obtain ⟨u, hu, u', hu', hne⟩ := Finset.one_lt_card.mp (h2 w)
  refine ⟨fun x hx => ?_, u, hu, u', hu', hne, ?_, ?_⟩
  · rw [hev] at hx; simpa using hx
  · rw [hev]; simpa using ⟨u, hu, eof_self3 u⟩
  · rw [hev]; simpa using ⟨u', hu', eof_self3 u'⟩

include hg hU in
/-- The NOT wire is no `Ded3` wire: below `OR (S w)` it would be false at `0`, hence everywhere. -/
theorem notWire_not_ded (w : Fin m) (c : ℕ) (hc : c ∈ notWires n gates)
    (hd : Ded3 S gates w c) : False := by
  obtain ⟨hle, u, -, -, -, -, hcu, -⟩ := hd
  have h0 := notWire_antitone gates hg hU c hc (fun _ => false) (eof u) (by simp) hcu
  obtain ⟨v, -, hfv⟩ := hle _ h0
  simp at hfv

include h2 hg hU in
/-- The NOT wire is no `LeafK` wire: above `OR (S w)` it would be true at `1`, hence everywhere. -/
theorem notWire_not_leafK (w : Fin m) (c : ℕ) (hc : c ∈ notWires n gates)
    (hl : LeafK S gates w c) : False := by
  obtain ⟨⟨hab, -⟩, x, hx⟩ := hl
  obtain ⟨u, hu⟩ : (S w).Nonempty := Finset.card_pos.mp (by have := h2 w; omega)
  have h1 := hab (fun _ => true) ⟨u, hu, rfl⟩
  have := notWire_antitone gates hg hU c hc x (fun _ => true) (by simp) h1
  rw [hx] at this
  exact absurd this (by simp)

include h2 hS hg hU hev in
/-- The second gate of a set with at least three elements (Small3's `exists_second3` without the
cleanliness hypothesis, and with `LeafK` in place of `Leaf3`). -/
theorem exists_secondK (w : Fin m) (h3 : 3 ≤ (S w).card) :
    ∃ c, n ≤ c ∧ c < n + gates.length ∧ c ≠ out w ∧
      (Ded3 S gates w c ∨ LeafK S gates w c) := by
  obtain ⟨hlo, hhi⟩ := out_range3 S h2 gates out hev w
  obtain ⟨j, hoj⟩ : ∃ j, out w = n + j := ⟨out w - n, by omega⟩
  have hev' : ∀ x : Fin n → Bool, val gates x (n + j) = decide (∃ v ∈ S w, x v = true) := by
    intro x; rw [← hoj]; exact hev w x
  rw [hoj]
  have hj : j < gates.length := by omega
  have hjl : j ≤ gates.length := hj.le
  set g := gates[j]'hj with hgdef
  have hF : ∀ x : Fin n → Bool, decide (∃ v ∈ S w, x v = true) =
      g.op.eval (g.inputs.map fun i => val (gates.take j) x i) := by
    intro x
    rw [← hev' x, val_gate gates x j hj]
  obtain ⟨u1, hu1, u2, hu2, u3, hu3, h12, h13, h23⟩ := Finset.two_lt_card.mp h3
  have hF0 : g.op.eval (g.inputs.map fun i => val (gates.take j) (fun _ : Fin n => false) i) =
      false := by
    rw [← hF]; simp
  have hFu : ∀ u ∈ S w, g.op.eval (g.inputs.map fun i => val (gates.take j) (eof u) i) = true := by
    intro u hu
    rw [← hF]; simpa using ⟨u, hu, eof_self3 u⟩
  have hFt : ∀ x : Fin n → Bool, (∃ v ∈ S w, x v = true) →
      g.op.eval (g.inputs.map fun i => val (gates.take j) x i) = true := by
    intro x hx
    rw [← hF]; simpa using hx
  have hFf : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => val (gates.take j) x i) = true →
      ∃ v ∈ S w, x v = true := by
    intro x hx
    rw [← hF] at hx; simpa using hx
  obtain ⟨hop, hlen⟩ := hg g (List.getElem_mem hj)
  -- the output gate is not the NOT gate: the NOT wire is no `Ded3` wire
  have hnot : g.op ≠ GateOp.not := by
    intro hn
    have hmem : n + j ∈ notWires n gates := by
      simp only [notWires, Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, by simpa using hj, ?_⟩
      simpa using hn
    apply notWire_not_ded S gates hg hU w (n + j) hmem
    rw [← hoj]
    exact out_ded S h2 gates out hev w
  have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hnot
  have child_lt : ∀ a (x : Fin n → Bool), val (gates.take j) x a = true → a < n + j := by
    intro a x ha
    by_contra hge
    rw [val_take3 gates x j a hjl, ite_eq_right hge] at ha
    exact absurd ha (by simp)
  have child_eq : ∀ a, a < n + j → ∀ x : Fin n → Bool,
      val (gates.take j) x a = val gates x a := by
    intro a ha x
    rw [val_take3 gates x j a hjl, ite_eq_left ha]
  -- a child below the output that is true on two units of `S w` is a second `Ded3` gate
  have hside : ∀ c, (∀ x : Fin n → Bool, val (gates.take j) x c = true →
      g.op.eval (g.inputs.map fun i => val (gates.take j) x i) = true) →
      ∀ u ∈ S w, ∀ u' ∈ S w, u ≠ u' → val (gates.take j) (eof u) c = true →
      val (gates.take j) (eof u') c = true →
      ∃ c, n ≤ c ∧ c < n + gates.length ∧ c ≠ n + j ∧
        (Ded3 S gates w c ∨ LeafK S gates w c) := by
    intro c hc u hu u' hu' hne e1 e2
    have hlt := child_lt c _ e1
    refine ⟨c, ?_, by omega, by omega, Or.inl ⟨?_, u, hu, u', hu', hne, ?_, ?_⟩⟩
    · by_contra hcn
      push Not at hcn
      rw [child_eq c hlt, val_var3 _ _ _ hcn] at e1 e2
      exact hne ((eof_true3 e1).symm.trans (eof_true3 e2))
    · intro x hx
      rw [← child_eq c hlt] at hx
      exact hFf x (hc x hx)
    · rw [← child_eq c hlt]; exact e1
    · rw [← child_eq c hlt]; exact e2
  rcases GateShape.inputs_cases g hlen with hin | ⟨a, hin⟩ | ⟨a, b, hin⟩
  · -- no inputs: constant
    rw [hin] at hF0
    have hu := hFu u1 hu1
    rw [hin] at hu
    rcases hop' with h | h <;> rw [h] at hF0 hu <;> simp [GateOp.eval] at hF0 hu
  · -- one input: the output copies the child, which is a second `Ded3` gate
    have hcopy : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun i => val (gates.take j) x i) =
        val (gates.take j) x a := by
      intro x
      rw [hin]
      rcases hop' with h | h <;> rw [h] <;> simp [GateOp.eval]
    have e1 := hFu u1 hu1
    have e2 := hFu u2 hu2
    rw [hcopy] at e1 e2
    exact hside a (fun x hx => by rw [hcopy]; exact hx) u1 hu1 u2 hu2 h12 e1 e2
  · rcases hop' with h | h
    · -- AND top: a child is a `LeafK` gate, otherwise both children have witness sets
      have hand : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun i => val (gates.take j) x i) =
          (val (gates.take j) x a && val (gates.take j) x b) := by
        intro x
        rw [hin, h]; simp [GateOp.eval]
      have habove : ∀ c, (∀ x : Fin n → Bool,
          g.op.eval (g.inputs.map fun i => val (gates.take j) x i) = true →
          val (gates.take j) x c = true) →
          n ≤ c ∧ c < n + j ∧ Above3 S gates (n := n) w c := by
        intro c hc
        have hlt := child_lt c _ (hc _ (hFu u1 hu1))
        refine ⟨?_, hlt, ?_⟩
        · by_contra hcn
          push Not at hcn
          have e1 := hc _ (hFu u1 hu1)
          have e2 := hc _ (hFu u2 hu2)
          rw [child_eq c hlt, val_var3 _ _ _ hcn] at e1 e2
          exact h12 ((eof_true3 e1).symm.trans (eof_true3 e2))
        · intro x hx
          rw [← child_eq c hlt]
          exact hc x (hFt x hx)
      obtain ⟨han, halt, haab⟩ := habove a (fun x hx => by
        rw [hand] at hx; simp only [Bool.and_eq_true] at hx; exact hx.1)
      obtain ⟨hbn, hblt, hbab⟩ := habove b (fun x hx => by
        rw [hand] at hx; simp only [Bool.and_eq_true] at hx; exact hx.2)
      have wit : ∀ c, Above3 S gates w c → ¬ LeafK S gates w c →
          ∃ T : Finset (Fin n), (∀ t ∈ T, t ∉ S w) ∧
            ∀ x : Fin n → Bool, (∀ t ∈ T, x t = true) → val gates x c = true := by
        intro c hab hnl
        by_cases hconst : ∀ x : Fin n → Bool, val gates x c = true
        · exact ⟨∅, by simp, fun x _ => hconst x⟩
        · push Not at hconst
          obtain ⟨x0, hx0⟩ := hconst
          have hnl3 : ¬ Leaf3 S gates w c := fun hl => hnl ⟨hl, x0, by simpa using hx0⟩
          have hw' : ∃ w', w' ≠ w ∧ Above3 S gates w' c := by
            by_contra hno
            push Not at hno
            exact hnl3 ⟨hab, fun w' hw' habw => hno w' hw' habw⟩
          obtain ⟨w', hw', habw⟩ := hw'
          obtain ⟨u, hu, hunot⟩ := exists_diff3 S h2 hS w w' (Ne.symm hw')
          exact ⟨{u}, by simpa using hunot, fun x hx => habw x ⟨u, hu, hx u (by simp)⟩⟩
      by_cases hA : LeafK S gates w a
      · exact ⟨a, han, by omega, by omega, Or.inr hA⟩
      by_cases hB : LeafK S gates w b
      · exact ⟨b, hbn, by omega, by omega, Or.inr hB⟩
      exfalso
      classical
      obtain ⟨Ta, hTa, hxa⟩ := wit a haab hA
      obtain ⟨Tb, hTb, hxb⟩ := wit b hbab hB
      set x : Fin n → Bool := fun c => decide (c ∈ Ta ∪ Tb) with hx
      have ea := hxa x (fun t ht => by simp [hx, ht])
      have eb := hxb x (fun t ht => by simp [hx, ht])
      obtain ⟨y, hy, hxy⟩ := hFf x (by rw [hand, child_eq a halt, child_eq b hblt, ea, eb]; rfl)
      simp only [hx, decide_eq_true_eq, Finset.mem_union] at hxy
      rcases hxy with h' | h'
      · exact hTa y h' hy
      · exact hTb y h' hy
    · -- OR top: pigeonhole on three units of `S w`
      have hor : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun i => val (gates.take j) x i) =
          (val (gates.take j) x a || val (gates.take j) x b) := by
        intro x
        rw [hin, h]; simp [GateOp.eval]
      have hsa := hside a (fun x hx => by rw [hor, hx]; rfl)
      have hsb := hside b (fun x hx => by rw [hor, hx]; simp)
      have e1 := hFu u1 hu1
      have e2 := hFu u2 hu2
      have e3 := hFu u3 hu3
      rw [hor] at e1 e2 e3
      cases a1 : val (gates.take j) (eof u1) a <;> cases a2 : val (gates.take j) (eof u2) a <;>
        cases a3 : val (gates.take j) (eof u3) a <;>
        simp only [a1, a2, a3, Bool.false_or, Bool.true_or] at e1 e2 e3
      · exact hsb u1 hu1 u2 hu2 h12 e1 e2
      · exact hsb u1 hu1 u2 hu2 h12 e1 e2
      · exact hsb u1 hu1 u3 hu3 h13 e1 e3
      · exact hsa u2 hu2 u3 hu3 h23 a2 a3
      · exact hsb u2 hu2 u3 hu3 h23 e2 e3
      · exact hsa u1 hu1 u3 hu3 h13 a1 a3
      · exact hsa u1 hu1 u2 hu2 h12 a1 a2
      · exact hsa u1 hu1 u2 hu2 h12 a1 a2

include h2 hS hg hU hev in
/-- **Lemma K** (class count). The NOT wires, the low-unit wires `U` and the classes of the sets
are pairwise disjoint sets of gate wires: an easy set (in `E`) owns its `Dr` class (Theorem E,
`≥ |S w| - 1` wires), any other set owns its output and, if `|S w| ≥ 3`, a second `Ded3`/`LeafK`
gate. -/
theorem lemmaK_count (E : Finset (Fin m)) (hE : ∀ w ∈ E, NotQuiet (S w) gates) :
    (notWires n gates).card + (lowUnit n gates).card +
      ∑ w : Fin m, (if w ∈ E then (S w).card - 1 else min ((S w).card - 1) 2) ≤
        gates.length := by
  classical
  have hex : ∀ w : Fin m, ∃ c, 3 ≤ (S w).card → (n ≤ c ∧ c < n + gates.length ∧ c ≠ out w ∧
      (Ded3 S gates w c ∨ LeafK S gates w c)) := by
    intro w
    by_cases h3 : 3 ≤ (S w).card
    · obtain ⟨c, hc⟩ := exists_secondK S h2 hS gates out hg hU hev w h3
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h h3⟩
  choose φ hφ using hex
  let G : Fin m → Finset ℕ := fun w =>
    if w ∈ E then Dr (S w) gates
    else if 3 ≤ (S w).card then {out w, φ w} else {out w}
  have hmem : ∀ w c, c ∈ G w → c ∈ Finset.Ico n (n + gates.length) ∧
      (Ded3 S gates w c ∨ LeafK S gates w c) := by
    intro w c hc
    have hor := out_range3 S h2 gates out hev w
    simp only [G] at hc
    split_ifs at hc with hwE h3
    · rw [Dr, Finset.mem_filter] at hc
      exact ⟨hc.1, Or.inl hc.2⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact ⟨Finset.mem_Ico.mpr hor, Or.inl (out_ded S h2 gates out hev w)⟩
      · have hp := hφ w h3
        exact ⟨Finset.mem_Ico.mpr ⟨hp.1, hp.2.1⟩, hp.2.2.2⟩
    · simp only [Finset.mem_singleton] at hc
      subst hc
      exact ⟨Finset.mem_Ico.mpr hor, Or.inl (out_ded S h2 gates out hev w)⟩
  have hcard : ∀ w, (if w ∈ E then (S w).card - 1 else min ((S w).card - 1) 2) ≤
      (G w).card := by
    intro w
    simp only [G]
    split_ifs with hwE h3
    · exact easy_card (S w) gates (out w) hg (hE w hwE) (hev w)
    · have hp := hφ w h3
      rw [Finset.card_pair (Ne.symm hp.2.2.1)]
      omega
    · rw [Finset.card_singleton]
      omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (G a) (G b) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro c hca hcb
    have toL3 : ∀ w, (Ded3 S gates w c ∨ LeafK S gates w c) →
        (Ded3 S gates w c ∨ Leaf3 S gates w c) := fun w h => h.imp id fun h => h.1
    exact hab (sec_unique3 S h2 hS gates a b c (toL3 a (hmem a c hca).2)
      (toL3 b (hmem b c hcb).2))
  set A := notWires n gates with hA
  set B := lowUnit n gates with hB
  set C := Finset.univ.biUnion G with hC
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro c hcA hcB
    simp only [hA, notWires, Finset.mem_filter] at hcA
    simp only [hB, lowUnit, Finset.mem_filter] at hcB
    obtain ⟨-, hp, hn⟩ := hcA
    exact hcB.2.1 hp hn
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro c hcA hcC
    obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hcC
    rcases (hmem w c hw).2 with hd | hl
    · exact notWire_not_ded S gates hg hU w c hcA hd
    · exact notWire_not_leafK S h2 gates hg hU w c hcA hl
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro c hcB hcC
    simp only [hB, lowUnit, Finset.mem_filter] at hcB
    obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hcC
    have h2u : 2 ≤ (unitsOf n gates c).card := by
      rcases (hmem w c hw).2 with hd | hl
      · exact ded_two_units S gates w c hd
      · exact above_two_units S h2 gates w c hl.1.1
    omega
  have hCcard : ∑ w, (G w).card = C.card := (Finset.card_biUnion hdisj).symm
  have hsub : A ∪ B ∪ C ⊆ Finset.Ico n (n + gates.length) := by
    intro c hc
    simp only [Finset.mem_union] at hc
    rcases hc with (hc | hc) | hc
    · exact (Finset.mem_filter.mp hc).1
    · exact (Finset.mem_filter.mp hc).1
    · obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hc
      exact (hmem w c hw).1
  calc A.card + B.card +
        ∑ w : Fin m, (if w ∈ E then (S w).card - 1 else min ((S w).card - 1) 2)
      ≤ A.card + B.card + C.card := by
        rw [← hCcard]
        exact Nat.add_le_add_left (Finset.sum_le_sum fun w _ => hcard w) _
    _ = (A ∪ B ∪ C).card := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
          Finset.card_union_of_disjoint hAB]
    _ ≤ (Finset.Ico n (n + gates.length)).card := Finset.card_le_card hsub
    _ = gates.length := by simp

/-- A NOT gate at position `p` is a NOT wire. -/
theorem mem_notWires (p : ℕ) (hp : p < gates.length) (hn : (gates[p]'hp).op = GateOp.not) :
    n + p ∈ notWires n gates := by
  simp only [notWires, Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨by omega, by omega⟩, by simpa using hp, ?_⟩
  simpa using hn

include h2 hS hg hU hev in
/-- Lemma K, excess form: with a NOT gate, `1 + |U| + base ≤ s + ex_E`, where `ex_E` sums
`|S w| - 3` over the sets outside `E` (the hard sets, when `E` is the set of easy sets). -/
theorem lemmaK_ex (p : ℕ) (hp : p < gates.length) (hn : (gates[p]'hp).op = GateOp.not)
    (E : Finset (Fin m)) (hE : ∀ w ∈ E, NotQuiet (S w) gates) :
    1 + (lowUnit n gates).card + ∑ w : Fin m, ((S w).card - 1) ≤
      gates.length + ∑ w : Fin m, (if w ∈ E then 0 else (S w).card - 3) := by
  have hc := lemmaK_count S h2 hS gates out hg hU hev E hE
  have hN : 1 ≤ (notWires n gates).card :=
    Finset.card_pos.mpr ⟨n + p, mem_notWires gates p hp hn⟩
  have hw : ∑ w : Fin m, ((S w).card - 1) ≤
      ∑ w : Fin m, ((if w ∈ E then (S w).card - 1 else min ((S w).card - 1) 2) +
        (if w ∈ E then 0 else (S w).card - 3)) := by
    refine Finset.sum_le_sum fun w _ => ?_
    split_ifs <;> omega
  rw [Finset.sum_add_distrib] at hw
  omega

include h2 hS hg hU hev in
/-- Corollary K1: if `ex = ∑_w (|S w| - 3) ≤ 1`, the L-meta-951 bound holds for every circuit with
at most one NOT (no minimality, no cleanliness). -/
theorem K1_bound (hex : ∑ w : Fin m, ((S w).card - 3) ≤ 1) :
    ∑ w : Fin m, ((S w).card - 1) ≤ gates.length := by
  classical
  by_cases hno : ∀ g ∈ gates, g.op ≠ GateOp.not
  · have hq : ∀ w ∈ (Finset.univ : Finset (Fin m)), NotQuiet (S w) gates := by
      intro w _ pre g rest h hop
      exact absurd hop (hno g (by rw [h]; simp))
    have hc := lemmaK_count S h2 hS gates out hg hU hev Finset.univ hq
    simp only [Finset.mem_univ, ite_true] at hc
    omega
  · push Not at hno
    obtain ⟨g, hgm, hop⟩ := hno
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hgm
    have h := lemmaK_ex S h2 hS gates out hg hU hev p hp hop ∅ (by simp)
    simp only [Finset.notMem_empty, ite_false] at h
    omega

end Classes

/-! ## Minimal counterexamples -/

open Classical in
/-- `ex_hard`: the excess `∑ (|S w| - 3)` over the hard sets (NOT false at the zero point). -/
noncomputable def exHard {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) : ℕ :=
  ∑ w : Fin m, (if NotQuiet (S w) gates then 0 else (S w).card - 3)

/-- Lemma K for a minimal counterexample (K2 without the `V1` term): with
`σ = base - s ≥ 1`, `σ + 1 + |U| ≤ ex_hard`. -/
theorem MinCE.lemmaK {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate}
    {out : Fin m → ℕ} (M : MinCE S gates out) :
    (∑ w : Fin m, ((S w).card - 1) - gates.length) + 1 + (lowUnit n gates).card ≤
      exHard S gates := by
  classical
  have C := M.ce
  have hlt := C.hlt
  by_cases hno : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exfalso
    have hq : ∀ w ∈ (Finset.univ : Finset (Fin m)), NotQuiet (S w) gates := by
      intro w _ pre g rest h hop
      exact absurd hop (hno g (by rw [h]; simp))
    have hc := lemmaK_count S C.h2 C.hS gates out C.hg C.hU C.hev Finset.univ hq
    simp only [Finset.mem_univ, ite_true] at hc
    omega
  · push Not at hno
    obtain ⟨g, hgm, hop⟩ := hno
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hgm
    have h := lemmaK_ex S C.h2 C.hS gates out C.hg C.hU C.hev p hp hop
      (Finset.univ.filter fun w => NotQuiet (S w) gates) (fun w hw => (Finset.mem_filter.mp hw).2)
    have he : ∑ w : Fin m, (if w ∈ Finset.univ.filter (fun w => NotQuiet (S w) gates) then 0
        else (S w).card - 3) = exHard S gates := by
      unfold exHard
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he] at h
    omega

/-- A minimal counterexample has excess `ex = ∑_w (|S w| - 3) ≥ 2`; more precisely
`2 + |U| ≤ ex_hard ≤ ex`. -/
theorem MinCE.ex_ge_two {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate}
    {out : Fin m → ℕ} (M : MinCE S gates out) :
    2 + (lowUnit n gates).card ≤ exHard S gates ∧ exHard S gates ≤ ∑ w : Fin m, ((S w).card - 3) := by
  classical
  have hK := M.lemmaK
  have hlt := M.ce.hlt
  refine ⟨by omega, Finset.sum_le_sum fun w _ => ?_⟩
  split_ifs <;> omega

/-! ## K2: single-reader points (`V1`) -/

open Classical in
/-- `V1`: the single-reader points. -/
noncomputable def V1 {n : ℕ} (gates : List Gate) : Finset (Fin n) :=
  Finset.univ.filter fun v => (Readers v gates).card = 1

/-- Every point of a set has a reader: if no gate reads `x_v`, no wire distinguishes `eof v` from
the all-false row, but the output of a set through `v` does. -/
theorem reader_of_mem {n m : ℕ} (S : Fin m → Finset (Fin n)) (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (v : Fin n) (w : Fin m) (hv : v ∈ S w) : (Readers v gates).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hlo := (out_range3 S h2 gates out hev w).1
  have key := val_congr_of_insens (v : ℕ) gates (eof v) (fun _ => false)
    (fun j hj => by
      have : j ≠ v := fun h => hj (h ▸ rfl)
      simp [eof, this])
    (fun k hk => Or.inr (insens_of_not_reader v gates k hk (by rw [hne]; simp)
      (hg _ (List.getElem_mem hk)).1))
    (out w) (by have := v.2; omega)
  rw [hev, hev] at key
  have h1 : decide (∃ u ∈ S w, eof v u = true) = true := by
    simpa using ⟨v, hv, eof_self3 v⟩
  rw [h1] at key
  simp at key

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- The reader `r` of a single-reader point `v` lies in `U`: it is an AND/OR gate, and it is
false at every unit `eof u` with `u ≠ v` (some set through `v` avoids `u`, and `r = x_v` on the
rows vanishing on that set: `single_core3`). -/
theorem reader_mem_lowUnit (M : MinCE S gates out) (v : Fin n) (r : ℕ)
    (hR : Readers v gates = {r}) : n + r ∈ lowUnit n gates := by
  classical
  have C := M.ce
  obtain ⟨c, b, -, -, hr, -, -, -, -, hop, hcore⟩ := M.single_core3 v r hR
  have hrR : r ∈ Readers v gates := by rw [hR]; simp
  have hdeg := M.deg_two_of_reader v r hrR
  simp only [lowUnit, Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨by omega, by omega⟩, fun h => ?_, ?_⟩
  · have hr' : n + r - n = r := by omega
    have := hop (hr' ▸ h)
    intro hn
    have e : (gates[n + r - n]'h) = gates[r]'(hr' ▸ h) := by simp only [hr']
    rw [e, this] at hn
    cases b <;> simp at hn
  · have hsub : unitsOf n gates (n + r) ⊆ {v} := by
      intro u hu
      simp only [unitsOf, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rw [Finset.mem_singleton]
      by_contra huv
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter
        fun w : Fin m => v ∈ S w).card)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      have havoid : ∃ k, v ∈ S k ∧ u ∉ S k := by
        by_contra hno
        push Not at hno
        have hui := hno i hi
        have huj := hno j hj
        have hsub2 : ({u, v} : Finset (Fin n)) ⊆ S i ∩ S j := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl <;> simp [*]
        have hc := Finset.card_le_card hsub2
        rw [Finset.card_pair huv] at hc
        have := C.hS i j hij
        omega
      obtain ⟨k, hvk, huk⟩ := havoid
      have hx := (hcore k hvk (eof u) fun t ht _ => by
        have : t ≠ u := fun h => huk (h ▸ ht)
        simp [eof, this]).2
      rw [hu] at hx
      have : eof u v = false := by simp [eof, Ne.symm huv]
      rw [this] at hx
      exact absurd hx (by simp)
    exact (Finset.card_le_card hsub).trans (by simp)

/-- `|V1| ≤ |U|`: different single-reader points have different readers, all in `U`. -/
theorem card_V1_le (M : MinCE S gates out) : (V1 (n := n) gates).card ≤ (lowUnit n gates).card := by
  classical
  have hone : ∀ v ∈ V1 (n := n) gates, Readers v gates = {rdr gates v} := by
    intro v hv
    simp only [V1, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hv
    rw [hr, rdr_eq gates v r hr]
  refine Finset.card_le_card_of_injOn (fun v => n + rdr gates v) (fun v hv => ?_) ?_
  · exact M.reader_mem_lowUnit v _ (hone v hv)
  · intro v hv v' hv' he
    simp only at he
    have hrr : rdr gates v = rdr gates v' := by omega
    obtain ⟨-, -, -, -, -, hnotR, -⟩ := M.single_core3 v _ (hone v hv)
    by_contra hne
    apply hnotR v' (Ne.symm hne)
    rw [hrr, hone v' hv']
    simp

/-- **K2**: a minimal counterexample (`σ = base - s ≥ 1`) has `σ + 1 + |V1| ≤ ex_hard`. -/
theorem lemmaK_V1 (M : MinCE S gates out) :
    (∑ w : Fin m, ((S w).card - 1) - gates.length) + 1 + (V1 (n := n) gates).card ≤
      exHard S gates := by
  have h1 := M.lemmaK
  have h2 := M.card_V1_le
  omega

/-- K2 (i), N2: a point of some set with degree `≤ 1 + σ` is a single-reader point. -/
theorem mem_V1_of_deg (M : MinCE S gates out) (v : Fin n) (hv : ∃ w, v ∈ S w)
    (hdeg : (Finset.univ.filter fun w : Fin m => v ∈ S w).card ≤
      1 + (∑ w : Fin m, ((S w).card - 1) - gates.length)) : v ∈ V1 (n := n) gates := by
  classical
  have C := M.ce
  have hlt := C.hlt
  obtain ⟨w, hvw⟩ := hv
  have hr := reader_of_mem S C.h2 gates out C.hg C.hev v w hvw
  have hsub := readers_sub_DC v gates C.hg
  have hpos : 1 ≤ (Readers v gates).card := Finset.card_pos.mpr hr
  have hDC : 1 ≤ (DC v gates).card := hpos.trans (Finset.card_le_card hsub)
  have hb := M.deadBound v hDC
  have hle := Finset.card_le_card hsub
  simp only [V1, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- A minimal counterexample with a point of degree `1` or `2` has `ex_hard ≥ 3`. -/
theorem ex_ge_three_of_deg2 (M : MinCE S gates out) (v : Fin n) (hv : ∃ w, v ∈ S w)
    (hdeg : (Finset.univ.filter fun w : Fin m => v ∈ S w).card ≤ 2) :
    3 ≤ exHard S gates := by
  classical
  have hlt := M.ce.hlt
  have hv := M.mem_V1_of_deg v hv (by omega)
  have hpos : 1 ≤ (V1 (n := n) gates).card := Finset.card_pos.mpr ⟨v, hv⟩
  have := M.lemmaK_V1
  omega

end MinCE

end PEqualNP.Outside.L_meta_951_aux
