import Mathlib
import PEqualNP.Defs
import PEqualNP.Kernel.GateShape
import PEqualNP.W951.Cases
import PEqualNP.W951.Cone
import PEqualNP.W951.Charge

/-! T1: the L-meta-951 bound for set systems with all `|S w| ≤ 3` (clean circuits, AND/OR
fan-in 2 plus at most one NOT).

Direct injection route: every set owns its output wire; every set with at least three elements
owns one more gate wire, a child of its output gate which is either *dedicated*
(`Ded`: below `OR (S w)` and true on two units of `S w`; OR-top case) or a *leaf*
(`Leaf`: above `OR (S w)` and above no other `OR (S w')`; AND-top case, star-forest lemma).
All these wires are pairwise distinct gate wires, so
`∑ w, min (|S w| - 1) 2 ≤ gates.length` (`small_min2_bound`), and for sizes `≤ 3` this is the
full bound (`small3_bound`). No test systems are needed for the count. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Kernel

/-- Wire `c` is above `OR (S w)`. -/
def Above3 {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (w : Fin m) (c : ℕ) :
    Prop :=
  ∀ x : Fin n → Bool, (∃ v ∈ S w, x v = true) → val gates x c = true

/-- Wire `c` is below `OR (S w)` and true on two distinct units of `S w`. -/
def Ded3 {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (w : Fin m) (c : ℕ) :
    Prop :=
  (∀ x : Fin n → Bool, val gates x c = true → ∃ v ∈ S w, x v = true) ∧
    ∃ u ∈ S w, ∃ u' ∈ S w, u ≠ u' ∧ val gates (eof u) c = true ∧ val gates (eof u') c = true

/-- Wire `c` is above `OR (S w)` and above no other `OR (S w')`. -/
def Leaf3 {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (w : Fin m) (c : ℕ) :
    Prop :=
  Above3 S gates w c ∧ ∀ w', w' ≠ w → ¬ Above3 S gates w' c

theorem val_var3 {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val gs x i = x ⟨i, h⟩ := by
  have := val_append [] gs x i (by simpa using h)
  rw [List.nil_append] at this
  rw [this, val_nil, dif_pos h]

/-- Value of an input wire seen from gate `j`. -/
theorem val_take3 {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j c : ℕ) (hj : j ≤ gs.length) :
    val (gs.take j) x c = if c < n + j then val gs x c else false := by
  have hl : (gs.take j).length = j := by simp; omega
  split_ifs with h
  · have := val_append (gs.take j) (gs.drop j) x c (by rw [hl]; exact h)
    rw [List.take_append_drop] at this
    exact this.symm
  · exact val_ge _ _ _ (by rw [hl]; omega)

theorem eof_self3 {n : ℕ} (u : Fin n) : eof u u = true := by simp [eof]

theorem eof_true3 {n : ℕ} {u v : Fin n} (h : eof u v = true) : v = u := by
  simpa [eof] using h

section
variable {n m : ℕ} (S : Fin m → Finset (Fin n))
  (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
  (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)

include h2 hS in
theorem exists_diff3 (i j : Fin m) (hij : i ≠ j) : ∃ u ∈ S j, u ∉ S i := by
  by_contra hcon
  push Not at hcon
  have : S i ∩ S j = S j := Finset.inter_eq_right.mpr hcon
  have h1 := hS i j hij
  have h3 := h2 j
  rw [this] at h1
  omega

include h2 hS in
/-- `OR (S j) ≤ OR (S i)` forces `i = j`. -/
theorem or_le3 (i j : Fin m)
    (h : ∀ x : Fin n → Bool, (∃ v ∈ S j, x v = true) → ∃ v ∈ S i, x v = true) : i = j := by
  by_contra hij
  obtain ⟨u, huj, hui⟩ := exists_diff3 S h2 hS i j hij
  obtain ⟨v, hv, hvu⟩ := h (eof u) ⟨u, huj, eof_self3 u⟩
  rw [eof_true3 hvu] at hv
  exact hui hv

variable (gates : List Gate) (out : Fin m → ℕ)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates)
  (hev : ∀ (w : Fin m) (x : Fin n → Bool),
    val gates x (out w) = decide (∃ v ∈ S w, x v = true))
  (hclean : ∀ k j : ℕ, k < gates.length → j < n + k →
    ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j)

include h2 hS in
theorem sec_unique3 (i j : Fin m) (c : ℕ)
    (hi : Ded3 S gates i c ∨ Leaf3 S gates i c) (hj : Ded3 S gates j c ∨ Leaf3 S gates j c) :
    i = j := by
  have dl : ∀ a b : Fin m, Ded3 S gates a c → Above3 S gates b c → a = b := by
    intro a b ha hb
    exact or_le3 S h2 hS a b fun x hx => ha.1 x (hb x hx)
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · by_contra hij
    obtain ⟨hle, u, hu, u', hu', hne, hcu, hcu'⟩ := hi
    obtain ⟨v, hv, hvu⟩ := hj.1 _ hcu
    obtain ⟨v', hv', hvu'⟩ := hj.1 _ hcu'
    rw [eof_true3 hvu] at hv
    rw [eof_true3 hvu'] at hv'
    have hsub : ({u, u'} : Finset (Fin n)) ⊆ S i ∩ S j := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> simp [*]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at hc
    have := hS i j hij
    omega
  · exact dl i j hi hj.1
  · exact (dl j i hj hi.1).symm
  · by_contra hij
    exact hj.2 i hij hi.1

include hev in
theorem out_above3 (w : Fin m) : Above3 S gates w (out w) := by
  intro x hx
  rw [hev]
  simpa using hx

include h2 hS hev in
theorem out_inj3 (i j : Fin m) (h : out i = out j) : i = j := by
  apply or_le3 S h2 hS i j
  intro x hx
  have := out_above3 S gates out hev j x hx
  rw [← h, hev] at this
  simpa using this

include h2 hS hev in
theorem sec_ne_out3 (i j : Fin m) (c : ℕ) (hij : i ≠ j)
    (hi : Ded3 S gates i c ∨ Leaf3 S gates i c) : c ≠ out j := by
  rintro rfl
  rcases hi with hi | hi
  · exact hij (or_le3 S h2 hS i j fun x hx => hi.1 x (out_above3 S gates out hev j x hx))
  · exact hi.2 j (Ne.symm hij) (out_above3 S gates out hev j)

include h2 hev in
theorem out_range3 (w : Fin m) : n ≤ out w ∧ out w < n + gates.length := by
  have hne : (S w).Nonempty := Finset.card_pos.mp (by have := h2 w; omega)
  obtain ⟨u, hu⟩ := hne
  constructor
  · by_contra hlt
    push Not at hlt
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (h2 w)
    have key : ∀ c ∈ S w, c = ⟨out w, hlt⟩ := by
      intro c hc
      have h := hev w (eof c)
      rw [val_var3 _ _ _ hlt] at h
      have : eof c ⟨out w, hlt⟩ = true := by
        rw [h]; simpa using ⟨c, hc, eof_self3 c⟩
      exact (eof_true3 this).symm
    exact hab ((key a ha).trans (key b hb).symm)
  · by_contra hge
    push Not at hge
    have h := hev w (eof u)
    rw [val_ge _ _ _ hge] at h
    have : decide (∃ v ∈ S w, eof u v = true) = true := by
      simpa using ⟨u, hu, eof_self3 u⟩
    rw [this] at h
    exact absurd h (by simp)

include h2 hS hg hU hev hclean in
/-- The second gate of a set with at least three elements. -/
theorem exists_second3 (w : Fin m) (h3 : 3 ≤ (S w).card) :
    ∃ c, n ≤ c ∧ c < n + gates.length ∧ c ≠ out w ∧
      (Ded3 S gates w c ∨ Leaf3 S gates w c) := by
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
  -- value at the zero point and at units
  have hF0 : g.op.eval (g.inputs.map fun i => val (gates.take j) (fun _ : Fin n => false) i) = false := by
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
  -- the NOT case is impossible
  have hnot : g.op ≠ GateOp.not := by
    intro hn
    have hmono : ∀ g' ∈ gates.take j, g'.op = GateOp.and ∨ g'.op = GateOp.or := by
      intro g' hg'
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
      have hij : i < j := by
        have := hi; simp at this; omega
      have hi' : i < gates.length := by omega
      rw [List.getElem_take]
      rcases (hg (gates[i]'hi') (List.getElem_mem hi')).1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have := hU i j hi' hj h hn
        omega
    have hm := mono_val (gates.take j) hmono (fun _ : Fin n => false) (eof u1) (by simp)
    have hu := hFu u1 hu1
    rcases GateShape.not_shape g hn hlen (fun i => val (gates.take j) (fun _ : Fin n => false) i)
      with ⟨_, he⟩ | ⟨a, r, hin, he⟩
    · rw [he] at hF0; exact absurd hF0 (by simp)
    · rcases GateShape.not_shape g hn hlen (fun i => val (gates.take j) (eof u1) i)
        with ⟨hin', _⟩ | ⟨a', r', hin', he'⟩
      · rw [hin] at hin'; exact absurd hin' (by simp)
      · rw [hin] at hin'
        obtain ⟨rfl, -⟩ := List.cons.inj hin'
        rw [he] at hF0
        rw [he'] at hu
        have := hm a (by simpa using hF0)
        rw [show val (gates.take j) (eof u1) a = false by simpa using hu] at this
        exact absurd this (by simp)
  have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hnot
  -- facts about a child wire
  have child_lt : ∀ a (x : Fin n → Bool), val (gates.take j) x a = true → a < n + j := by
    intro a x ha
    by_contra hge
    rw [val_take3 gates x j a hjl, if_neg hge] at ha
    exact absurd ha (by simp)
  have child_eq : ∀ a, a < n + j → ∀ x : Fin n → Bool, val (gates.take j) x a = val gates x a := by
    intro a ha x
    rw [val_take3 gates x j a hjl, if_pos ha]
  rcases GateShape.inputs_cases g hlen with hin | ⟨a, hin⟩ | ⟨a, b, hin⟩
  · -- no inputs: constant
    rw [hin] at hF0
    have hu := hFu u1 hu1
    rw [hin] at hu
    rcases hop' with h | h <;> rw [h] at hF0 hu <;> simp [GateOp.eval] at hF0 hu
  · -- one input: copies a wire, not clean
    exfalso
    have hcopy : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun i => val (gates.take j) x i) =
        val (gates.take j) x a := by
      intro x
      rw [hin]
      rcases hop' with h | h <;> rw [h] <;> simp [GateOp.eval]
    have hu := hFu u1 hu1
    rw [hcopy] at hu
    have ha := child_lt a _ hu
    apply hclean j a hj ha
    intro x
    rw [val_gate gates x j hj, hcopy, child_eq a ha]
  · -- two inputs
    rcases hop' with h | h
    · -- AND top
      have hand : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun i => val (gates.take j) x i) =
          (val (gates.take j) x a && val (gates.take j) x b) := by
        intro x
        rw [hin, h]; simp [GateOp.eval]
      have habove : ∀ c, (∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun i => val (gates.take j) x i) = true →
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
      by_cases hA : ∃ w', w' ≠ w ∧ Above3 S gates w' a
      · by_cases hB : ∃ w', w' ≠ w ∧ Above3 S gates w' b
        · exfalso
          obtain ⟨wa, hwa, hAa⟩ := hA
          obtain ⟨wb, hwb, hBb⟩ := hB
          obtain ⟨u, hu, hunot⟩ := exists_diff3 S h2 hS w wa (Ne.symm hwa)
          obtain ⟨v, hv, hvnot⟩ := exists_diff3 S h2 hS w wb (Ne.symm hwb)
          set x : Fin n → Bool := fun c => eof u c || eof v c with hx
          have ea := hAa x ⟨u, hu, by simp [hx, eof_self3]⟩
          have eb := hBb x ⟨v, hv, by simp [hx, eof_self3]⟩
          have := hFf x (by rw [hand, child_eq a halt, child_eq b hblt, ea, eb]; rfl)
          obtain ⟨y, hy, hxy⟩ := this
          simp only [hx, Bool.or_eq_true] at hxy
          rcases hxy with e | e
          · rw [eof_true3 e] at hy; exact hunot hy
          · rw [eof_true3 e] at hy; exact hvnot hy
        · refine ⟨b, hbn, by omega, by omega, Or.inr ⟨hbab, ?_⟩⟩
          intro w' hw' hab
          exact hB ⟨w', hw', hab⟩
      · refine ⟨a, han, by omega, by omega, Or.inr ⟨haab, ?_⟩⟩
        intro w' hw' hab
        exact hA ⟨w', hw', hab⟩
    · -- OR top
      have hor : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun i => val (gates.take j) x i) =
          (val (gates.take j) x a || val (gates.take j) x b) := by
        intro x
        rw [hin, h]; simp [GateOp.eval]
      have hside : ∀ c, (∀ x : Fin n → Bool, val (gates.take j) x c = true →
          g.op.eval (g.inputs.map fun i => val (gates.take j) x i) = true) →
          ∀ u ∈ S w, ∀ u' ∈ S w, u ≠ u' → val (gates.take j) (eof u) c = true →
          val (gates.take j) (eof u') c = true →
          ∃ c, n ≤ c ∧ c < n + gates.length ∧ c ≠ n + j ∧
            (Ded3 S gates w c ∨ Leaf3 S gates w c) := by
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

include h2 hS hg hU hev hclean in
/-- T1, general form: every set owns its output gate, and every set with at least three elements
owns a second gate; all these gates are distinct. -/
theorem small_min2_bound :
    ∑ w : Fin m, min ((S w).card - 1) 2 ≤ gates.length := by
  classical
  have hex : ∀ w : Fin m, ∃ c, 3 ≤ (S w).card → (n ≤ c ∧ c < n + gates.length ∧ c ≠ out w ∧
      (Ded3 S gates w c ∨ Leaf3 S gates w c)) := by
    intro w
    by_cases h3 : 3 ≤ (S w).card
    · obtain ⟨c, hc⟩ := exists_second3 S h2 hS gates out hg hU hev hclean w h3
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h h3⟩
  choose φ hφ using hex
  let f : (Σ w : Fin m, Fin (min ((S w).card - 1) 2)) → ℕ :=
    fun s => if s.2.val = 0 then out s.1 else φ s.1
  have hbig : ∀ s : (Σ w : Fin m, Fin (min ((S w).card - 1) 2)), s.2.val ≠ 0 →
      3 ≤ (S s.1).card := by
    intro s hs
    have := s.2.isLt
    omega
  have hinj : Function.Injective f := by
    rintro ⟨w, k⟩ ⟨w', k'⟩ hff
    simp only [f] at hff
    have hk := k.isLt
    have hk' := k'.isLt
    by_cases h0 : k.val = 0 <;> by_cases h0' : k'.val = 0
    · rw [if_pos h0, if_pos h0'] at hff
      obtain rfl := out_inj3 S h2 hS gates out hev w w' hff
      have : k = k' := Fin.ext (by omega)
      rw [this]
    · exfalso
      rw [if_pos h0, if_neg h0'] at hff
      have hp := hφ w' (hbig ⟨w', k'⟩ h0')
      by_cases hww : w' = w
      · subst hww; exact hp.2.2.1 hff.symm
      · exact sec_ne_out3 S h2 hS gates out hev w' w _ hww hp.2.2.2 hff.symm
    · exfalso
      rw [if_neg h0, if_pos h0'] at hff
      have hp := hφ w (hbig ⟨w, k⟩ h0)
      by_cases hww : w = w'
      · subst hww; exact hp.2.2.1 hff
      · exact sec_ne_out3 S h2 hS gates out hev w w' _ hww hp.2.2.2 hff
    · rw [if_neg h0, if_neg h0'] at hff
      have hp := hφ w (hbig ⟨w, k⟩ h0)
      have hp' := hφ w' (hbig ⟨w', k'⟩ h0')
      rw [← hff] at hp'
      obtain rfl := sec_unique3 S h2 hS gates w w' _ hp.2.2.2 hp'.2.2.2
      have : k = k' := Fin.ext (by omega)
      rw [this]
  have hsub : ∀ s, f s ∈ Finset.Ico n (n + gates.length) := by
    intro s
    simp only [f, Finset.mem_Ico]
    split_ifs with h0
    · exact out_range3 S h2 gates out hev s.1
    · have hp := hφ s.1 (hbig s h0)
      exact ⟨hp.1, hp.2.1⟩
  have hcard : Fintype.card (Σ w : Fin m, Fin (min ((S w).card - 1) 2)) ≤
      (Finset.Ico n (n + gates.length)).card := by
    rw [← Finset.card_univ, ← Finset.card_image_of_injective _ hinj]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    exact hsub x
  simpa [Fintype.card_sigma] using hcard

include h2 hS hg hU hev hclean in
/-- T1: if all sets have at most three elements, the L-meta-951 bound holds. -/
theorem small3_bound (h3 : ∀ w : Fin m, (S w).card ≤ 3) :
    ∑ w : Fin m, ((S w).card - 1) ≤ gates.length := by
  have h := small_min2_bound S h2 hS gates out hg hU hev hclean
  have he : ∀ w : Fin m, (S w).card - 1 = min ((S w).card - 1) 2 := by
    intro w
    have := h3 w
    omega
  rw [Finset.sum_congr rfl (fun w _ => he w)]
  exact h

end

end PEqualNP.Outside.L_meta_951_aux
