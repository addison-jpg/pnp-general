import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Small3
import PEqualNP.W951.TwoWorld
import PEqualNP.W951.MinCE

/-! Theorem E (easy sets) and Corollary E'.

A set `Q` is EASY when the NOT gates are true at its zero point (`NotQuiet Q gates`).
* `val_C1_of_quiet`: at the zero point of an easy set the circuit agrees with the upper world `C1`.
* `quiet_le`: a wire that is false at the zero point of an easy set `Q` is below `OR Q` everywhere.
* `easy_card` (Theorem E): an easy set `S` has at least `|S| - 1` gate wires that are below
  `OR S` and true on two units of `S` (the finset `Dr S gates`, i.e. Small3's `Ded3` wires).
* `easyHard_bound` (Corollary E'): `∑_{easy} (|S| - 1) + ∑_{hard} min (|S| - 1) 2 ≤ gates.length`.
* `easy4_bound`: if every set of size `≥ 4` is easy, the L-meta-951 bound holds.
* `MinCE.hard4`: a minimal counterexample has a HARD set of size `≥ 4`. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

theorem C1_snoc (gs : List Gate) (g : Gate) :
    C1 (gs ++ [g]) = C1 gs ++ [constNot GateOp.and g] := by
  simp [C1]

/-- At the zero point of an easy set the circuit agrees with the upper world `C1`. -/
theorem val_C1_of_quiet {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) (hq : NotQuiet Q gs) :
    ∀ i, val (C1 gs) (Zof Q) i = val gs (Zof Q) i := by
  induction gs using List.reverseRecOn with
  | nil => intro i; rfl
  | append_singleton gs g ih =>
    have hq' : NotQuiet Q gs := by
      intro pre g' rest h hop
      exact hq pre g' (rest ++ [g]) (by rw [h]; simp) hop
    have ih' := ih hq'
    intro i
    have hlen : (C1 gs).length = gs.length := by simp [C1]
    rw [C1_snoc, val_snoc, val_snoc, hlen]
    split_ifs with hi
    · have hfun : (fun j => val (C1 gs) (Zof Q) j) = fun j => val gs (Zof Q) j := funext ih'
      rw [hfun]
      by_cases hn : g.op = GateOp.not
      · have h1 := hq gs g [] rfl hn
        rw [h1]
        obtain ⟨op, ins⟩ := g
        simp only at hn
        subst hn
        simp [constNot, GateOp.eval]
      · obtain ⟨op, ins⟩ := g
        simp only at hn
        cases op <;> first | rfl | exact absurd rfl hn
    · exact ih' i

/-- A wire that is false at the zero point of an easy set `Q` is below `OR Q` on all inputs. -/
theorem quiet_le {n : ℕ} (Q : Finset (Fin n)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hq : NotQuiet Q gates) (i : ℕ) (hz : val gates (Zof Q) i = false)
    (x : Fin n → Bool) (hx : val gates x i = true) : ∃ v ∈ Q, x v = true := by
  by_contra hno
  push Not at hno
  have h1 := ((sandwich gates (fun g hm => (hg g hm).1) x) i).2 hx
  have hmono : ∀ g ∈ C1 gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hm =>
    (constNot_mono GateOp.and (Or.inl rfl) gates hg g hm).1
  have h2 := mono_val (C1 gates) hmono x (Zof Q) (fun c hc => by
    simp only [Zof, decide_eq_true_eq]
    intro hcQ
    exact hno c hcQ hc) i h1
  rw [val_C1_of_quiet Q gates hq i, hz] at h2
  exact absurd h2 (by simp)

/-- Gate wire `c` is below `OR S` and true on two distinct units of `S`
(`Ded3 S gates w c` is `DrP (S w) gates c`). -/
def DrP {n : ℕ} (S : Finset (Fin n)) (gates : List Gate) (c : ℕ) : Prop :=
  (∀ x : Fin n → Bool, val gates x c = true → ∃ v ∈ S, x v = true) ∧
    ∃ u ∈ S, ∃ u' ∈ S, u ≠ u' ∧ val gates (eof u) c = true ∧ val gates (eof u') c = true

open Classical in
/-- The gate wires below `OR S` that are true on at least two units of `S`. -/
noncomputable def Dr {n : ℕ} (S : Finset (Fin n)) (gates : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gates.length)).filter fun c => DrP S gates c

theorem ded3_iff_DrP {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (w : Fin m)
    (c : ℕ) : Ded3 S gates w c ↔ DrP (S w) gates c := Iff.rfl

/-- Theorem E: an easy set `S` (NOT gates true at `Zof S`) computed at wire `o` has at least
`|S| - 1` gate wires below `OR S` that are true on two units of `S`. -/
theorem easy_card {n : ℕ} (S : Finset (Fin n)) (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hq : NotQuiet S gates)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ S, x v = true)) :
    S.card - 1 ≤ (Dr S gates).card := by
  classical
  have hz : val gates (Zof S) o = false := by
    rw [hev, decide_eq_false_iff_not]
    rintro ⟨v, hv, hv'⟩
    simp [Zof, hv] at hv'
  have hu : ∀ u ∈ S, val gates (eof u) o = true := by
    intro u hu
    rw [hev, decide_eq_true_eq]
    exact ⟨u, hu, eof_self3 u⟩
  have h1 := count_world S gates o (good_of_quiet S gates hg hq) hz hu
  refine h1.trans (Finset.card_le_card ?_)
  intro i hi
  rw [D, Finset.mem_filter] at hi
  obtain ⟨hI, hzi, u, v, huv, huS, hvS, hui, hvi⟩ := hi
  rw [Dr, Finset.mem_filter]
  exact ⟨hI, fun x hx => quiet_le S gates hg hq i hzi x hx, u, huS, v, hvS, huv, hui, hvi⟩

section
variable {n m : ℕ} (S : Fin m → Finset (Fin n))
  (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
  (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
  (gates : List Gate) (out : Fin m → ℕ)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates)
  (hev : ∀ (w : Fin m) (x : Fin n → Bool),
    val gates x (out w) = decide (∃ v ∈ S w, x v = true))
  (hclean : ∀ k j : ℕ, k < gates.length → j < n + k →
    ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j)

include h2 hS hev in
/-- A wire owned by set `a` (dedicated, leaf, or output) is owned by no other set. -/
theorem own_unique (a b : Fin m) (c : ℕ)
    (ha : (Ded3 S gates a c ∨ Leaf3 S gates a c) ∨ c = out a)
    (hb : (Ded3 S gates b c ∨ Leaf3 S gates b c) ∨ c = out b) : a = b := by
  by_contra hab
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hab (sec_unique3 S h2 hS gates a b c ha hb)
  · exact sec_ne_out3 S h2 hS gates out hev a b c hab ha hb
  · exact sec_ne_out3 S h2 hS gates out hev b a c (Ne.symm hab) hb ha
  · exact hab (out_inj3 S h2 hS gates out hev a b (ha.symm.trans hb))

include h2 hS hg hU hev hclean in
/-- Corollary E': easy sets (those in `E`) pay `|S| - 1`, the other sets pay `min (|S| - 1) 2`. -/
theorem easyHard_bound (E : Finset (Fin m)) (hE : ∀ w ∈ E, NotQuiet (S w) gates) :
    ∑ w : Fin m, (if w ∈ E then (S w).card - 1 else min ((S w).card - 1) 2) ≤ gates.length := by
  classical
  have hex : ∀ w : Fin m, ∃ c, 3 ≤ (S w).card → (n ≤ c ∧ c < n + gates.length ∧ c ≠ out w ∧
      (Ded3 S gates w c ∨ Leaf3 S gates w c)) := by
    intro w
    by_cases h3 : 3 ≤ (S w).card
    · obtain ⟨c, hc⟩ := exists_second3 S h2 hS gates out hg hU hev hclean w h3
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h h3⟩
  choose φ hφ using hex
  let G : Fin m → Finset ℕ := fun w =>
    if w ∈ E then Dr (S w) gates
    else if 3 ≤ (S w).card then {out w, φ w} else {out w}
  have hmem : ∀ w c, c ∈ G w → c ∈ Finset.Ico n (n + gates.length) ∧
      ((Ded3 S gates w c ∨ Leaf3 S gates w c) ∨ c = out w) := by
    intro w c hc
    have hor := out_range3 S h2 gates out hev w
    simp only [G] at hc
    split_ifs at hc with hwE h3
    · rw [Dr, Finset.mem_filter] at hc
      exact ⟨hc.1, Or.inl (Or.inl hc.2)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact ⟨Finset.mem_Ico.mpr hor, Or.inr rfl⟩
      · have hp := hφ w h3
        exact ⟨Finset.mem_Ico.mpr ⟨hp.1, hp.2.1⟩, Or.inl hp.2.2.2⟩
    · simp only [Finset.mem_singleton] at hc
      subst hc
      exact ⟨Finset.mem_Ico.mpr hor, Or.inr rfl⟩
  have hcard : ∀ w, (if w ∈ E then (S w).card - 1 else min ((S w).card - 1) 2) ≤ (G w).card := by
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
    exact hab (own_unique S h2 hS gates out hev a b c (hmem a c hca).2 (hmem b c hcb).2)
  calc ∑ w : Fin m, (if w ∈ E then (S w).card - 1 else min ((S w).card - 1) 2)
      ≤ ∑ w, (G w).card := Finset.sum_le_sum fun w _ => hcard w
    _ = (Finset.univ.biUnion G).card := by rw [Finset.card_biUnion hdisj]
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
        apply Finset.card_le_card
        intro c hc
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hc
        exact (hmem w c hw).1
    _ = gates.length := by simp

include h2 hS hg hU hev hclean in
/-- If every set with at least four elements is easy, the L-meta-951 bound holds. -/
theorem easy4_bound (h4 : ∀ w : Fin m, 4 ≤ (S w).card → NotQuiet (S w) gates) :
    ∑ w : Fin m, ((S w).card - 1) ≤ gates.length := by
  classical
  have h := easyHard_bound S h2 hS gates out hg hU hev hclean
    (Finset.univ.filter fun w => 4 ≤ (S w).card) (fun w hw => h4 w (Finset.mem_filter.mp hw).2)
  refine le_trans (Finset.sum_le_sum fun w _ => ?_) h
  split_ifs with hw
  · exact le_rfl
  · have : ¬ 4 ≤ (S w).card := fun h' => hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w, h'⟩)
    omega

end

/-- A minimal counterexample has a HARD set (NOT not quiet at its zero point) of size `≥ 4`. -/
theorem MinCE.hard4 {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}
    (M : MinCE S gates out) : ∃ w, 4 ≤ (S w).card ∧ ¬ NotQuiet (S w) gates := by
  have C := M.ce
  by_contra hno
  push Not at hno
  have := easy4_bound S C.h2 C.hS gates out C.hg C.hU C.hev M.clean hno
  have := C.hlt
  omega

end PEqualNP.Outside.L_meta_951_aux

