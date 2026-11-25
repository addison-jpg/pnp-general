import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Lift
import PEqualNP.W951.TwoWorld
import PEqualNP.W951.MinCE

/-!
# The lifted monotone form of 951 (S2 "Lift", second half)

`LiftedBound` : every monotone circuit `pre ++ post` over `(x, y)` (`y` = input number `n`) in which
the gates of `pre` do not read `y`, with a wire `hw ≠ n` (value `h x`, taken in `pre`, so `y`-free)
and outputs `F_w(x, y) ∈ [o_w ∧ (y ∨ h), o_w ∨ (y ∧ h)]`, `o_w = OR(S_w)`, has at least
`∑ (|S w| - 1) - 1` gates.

`OneNotBound` : the 951 bound in `val` form (the conclusion of `bound_of_noMinCE`).

* `unlift` : the converse construction, a one-NOT circuit with one gate more (`length_unlift`,
  `unlift_ops`, `unlift_oneNot`, `val_unlift`, `unlift_hev`).
* `liftedBound_of_oneNotBound`, `oneNotBound_of_liftedBound`, `liftedBound_iff_oneNotBound`.
* `no_minCE_of_liftedBound : LiftedBound → ¬ MinCE S gates out`,
  `L_meta_951_of_liftedBound` (the statement of `PEqualNP.Outside.L_meta_951` from `LiftedBound`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- The lifted monotone form of 951. -/
def LiftedBound : Prop :=
  ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (pre post : List Gate) (hw : ℕ) (out : Fin m → ℕ),
    (∀ g ∈ pre ++ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ g ∈ pre, n ∉ g.inputs) → hw ≠ n →
    (∀ (w : Fin m) (x : Fin n → Bool) (y : Bool),
      InInterval (decide (∃ v ∈ S w, x v = true)) y (val pre (ext x y) hw)
        (val (pre ++ post) (ext x y) (out w))) →
    ∑ i : Fin m, ((S i).card - 1) ≤ (pre ++ post).length + 1

/-- The 951 bound for circuits with at most one NOT gate, in `val` form. -/
def OneNotBound : Prop :=
  ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (gates : List Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    AtMostOneNot gates →
    (∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)) →
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length

/-! ## The converse construction: from a lifted circuit back to a one-NOT circuit -/

/-- Inverse of `sh` (on wires `≠ n`). -/
def unsh (n j : ℕ) : ℕ := if j < n then j else j - 1

/-- Inverse of `liftWire` : lifted wire `j` comes from original wire `unW n p j`. -/
def unW (n p j : ℕ) : ℕ :=
  if j < n then j else if j = n then n + p else if j ≤ n + p then j - 1 else j

def unshGate (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (unsh n)⟩

def unGate (n p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (unW n p)⟩

/-- The one-NOT circuit of a lifted circuit `pre ++ post` with `y`-free wire `hw`: the gates of
`pre`, a NOT gate reading `h`, then the gates of `post` reading the NOT gate instead of `y`. -/
def unlift (n : ℕ) (pre post : List Gate) (hw : ℕ) : List Gate :=
  pre.map (unshGate n) ++ ⟨GateOp.not, [unsh n hw]⟩ :: post.map (unGate n pre.length)

theorem length_unlift (n : ℕ) (pre post : List Gate) (hw : ℕ) :
    (unlift n pre post hw).length = (pre ++ post).length + 1 := by
  simp [unlift]; omega

theorem sh_unsh (n j : ℕ) (hj : j ≠ n) : sh n (unsh n j) = j := by
  unfold sh unsh; split_ifs <;> omega

theorem liftWire_unW (n p j : ℕ) : liftWire n p (unW n p j) = j := by
  unfold liftWire unW; split_ifs <;> omega

theorem map_sh_unsh (n : ℕ) (pre : List Gate) (hy : ∀ g ∈ pre, n ∉ g.inputs) :
    (pre.map (unshGate n)).map (shGate n) = pre := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id pre]
  apply List.map_congr_left
  intro g hg
  obtain ⟨op, ins⟩ := g
  simp only [Function.comp, shGate, unshGate, List.map_map, id]
  congr 1
  conv_rhs => rw [← List.map_id ins]
  apply List.map_congr_left
  intro j hj
  exact sh_unsh n j (fun h => hy _ hg (by simpa [h] using hj))

/-- The value of the `y`-free wire `hw` in the one-NOT circuit. -/
theorem val_unsh {n : ℕ} (pre : List Gate) (hy : ∀ g ∈ pre, n ∉ g.inputs) (x : Fin n → Bool)
    (y : Bool) (j : ℕ) (hj : j ≠ n) :
    val (pre.map (unshGate n)) x (unsh n j) = val pre (ext x y) j := by
  have h := val_shift (pre.map (unshGate n)) x y (unsh n j)
  rw [map_sh_unsh n pre hy, sh_unsh n j hj] at h
  exact h.symm

/-- Wire by wire: the circuit `A ++ N :: post.map unGate` against `A.map shGate ++ post` at
`(x, ν x)`, `ν x` = the value of `N`. -/
theorem val_unlift_split {n : ℕ} (A : List Gate) (N : Gate) (post : List Gate)
    (x : Fin n → Bool) :
    ∀ i, val (A ++ N :: post.map (unGate n A.length)) x i =
      val (A.map (shGate n) ++ post)
        (ext x (val (A ++ [N]) x (n + A.length))) (liftWire n A.length i) := by
  induction post using List.reverseRecOn with
  | nil =>
    intro i
    have h := val_lift_split A N [] x i
    simpa [liftPost] using h
  | append_singleton post g ih =>
    intro i
    have e1 : A ++ N :: (post ++ [g]).map (unGate n A.length) =
        (A ++ N :: post.map (unGate n A.length)) ++ [unGate n A.length g] := by simp
    have e2 : A.map (shGate n) ++ (post ++ [g]) = (A.map (shGate n) ++ post) ++ [g] := by simp
    rw [e1, e2, val_snoc, val_snoc]
    simp only [List.length_append, List.length_cons, List.length_map]
    have hiff : liftWire n A.length i = n + 1 + (A.length + post.length) ↔
        i = n + (A.length + (post.length + 1)) := by
      unfold liftWire; split_ifs <;> omega
    by_cases hi : i = n + (A.length + (post.length + 1))
    · rw [ite_eq_left (hiff.mpr hi), ite_eq_left hi]
      simp only [unGate, List.map_map]
      congr 2
      funext j
      simp only [Function.comp]
      rw [ih (unW n A.length j), liftWire_unW]
    · rw [ite_eq_right (fun h => hi (hiff.mp h)), ite_eq_right hi]
      exact ih i

/-- **Converse lift theorem**: lifted wire `j` at `(x, ! h x)` is wire `unW j` of the one-NOT
circuit at `x`. -/
theorem val_unlift {n : ℕ} (pre post : List Gate) (hw : ℕ)
    (hy : ∀ g ∈ pre, n ∉ g.inputs) (hhw : hw ≠ n) (x : Fin n → Bool) (j : ℕ) :
    val (unlift n pre post hw) x (unW n pre.length j) =
      val (pre ++ post) (ext x (!(val pre (ext x false) hw))) j := by
  have key := val_unlift_split (pre.map (unshGate n)) ⟨GateOp.not, [unsh n hw]⟩ post x
    (unW n pre.length j)
  rw [List.length_map, map_sh_unsh n pre hy, liftWire_unW] at key
  have hν : val (pre.map (unshGate n) ++ [⟨GateOp.not, [unsh n hw]⟩]) x (n + pre.length) =
      !(val pre (ext x false) hw) := by
    rw [val_snoc, List.length_map, ite_eq_left rfl, ← val_unsh pre hy x false hw hhw]
    simp [GateOp.eval]
  rw [hν] at key
  exact key

theorem unlift_ops (n : ℕ) (pre post : List Gate) (hw : ℕ)
    (hg : ∀ g ∈ pre ++ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ unlift n pre post hw,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  intro g hm
  simp only [unlift, List.mem_append, List.mem_cons, List.mem_map] at hm
  rcases hm with ⟨g0, h0, rfl⟩ | rfl | ⟨g0, h0, rfl⟩
  · obtain ⟨h1, h2⟩ := hg g0 (List.mem_append_left _ h0)
    refine ⟨?_, by simpa [unshGate] using h2⟩
    rcases h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact ⟨Or.inr (Or.inr rfl), by simp⟩
  · obtain ⟨h1, h2⟩ := hg g0 (List.mem_append_right _ h0)
    refine ⟨?_, by simpa [unGate] using h2⟩
    rcases h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem unlift_oneNot (n : ℕ) (pre post : List Gate) (hw : ℕ)
    (hg : ∀ g ∈ pre ++ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    AtMostOneNot (unlift n pre post hw) := by
  have key : ∀ (i : ℕ) (hi : i < (unlift n pre post hw).length),
      ((unlift n pre post hw)[i]'hi).op = GateOp.not → i = pre.length := by
    intro i hi hop
    by_contra hne
    have hmem : ∃ g ∈ pre ++ post, g.op = GateOp.not := by
      unfold unlift at hi hop
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · rw [List.getElem_append_left (by simpa using h)] at hop
        rw [List.getElem_map] at hop
        exact ⟨_, List.mem_append_left _ (List.getElem_mem _), hop⟩
      · rw [List.getElem_append_right (by simp; omega)] at hop
        simp only [List.length_map] at hop
        obtain ⟨k, hk⟩ : ∃ k, i - pre.length = k + 1 := ⟨i - pre.length - 1, by omega⟩
        simp only [hk, List.getElem_cons_succ, List.getElem_map] at hop
        exact ⟨_, List.mem_append_right _ (List.getElem_mem _), hop⟩
    obtain ⟨g, hgm, hgo⟩ := hmem
    rcases (hg g hgm).1 with h | h <;> rw [h] at hgo <;> cases hgo
  intro i1 i2 h1 h2 e1 e2
  rw [key i1 h1 e1, key i2 h2 e2]

/-- The one-NOT circuit computes `OR(S w)` at output `unW (out w)`. -/
theorem unlift_hev {n m : ℕ} (S : Fin m → Finset (Fin n)) (pre post : List Gate) (hw : ℕ)
    (out : Fin m → ℕ) (hy : ∀ g ∈ pre, n ∉ g.inputs) (hhw : hw ≠ n)
    (hint : ∀ (w : Fin m) (x : Fin n → Bool) (y : Bool),
      InInterval (decide (∃ v ∈ S w, x v = true)) y (val pre (ext x y) hw)
        (val (pre ++ post) (ext x y) (out w)))
    (w : Fin m) (x : Fin n → Bool) :
    val (unlift n pre post hw) x (unW n pre.length (out w)) =
      decide (∃ v ∈ S w, x v = true) := by
  rw [val_unlift pre post hw hy hhw x (out w)]
  have hfree : ∀ y, val pre (ext x y) hw = val pre (ext x false) hw := by
    intro y
    rw [← val_unsh pre hy x y hw hhw, ← val_unsh pre hy x false hw hhw]
  have H := hint w x (!(val pre (ext x false) hw))
  rw [hfree (!(val pre (ext x false) hw))] at H
  exact inInterval_not _ _ _ H

theorem liftedBound_of_oneNotBound (H : OneNotBound) : LiftedBound := by
  intro n m S h2 hS pre post hw out hg hy hhw hint
  have := H n m S h2 hS (unlift n pre post hw) (fun w => unW n pre.length (out w))
    (unlift_ops n pre post hw hg) (unlift_oneNot n pre post hw hg)
    (unlift_hev S pre post hw out hy hhw hint)
  rwa [length_unlift] at this

/-! ## From the lifted bound to the one-NOT bound -/

theorem constNot_of_ne (b : GateOp) (g : Gate) (h : g.op ≠ GateOp.not) : constNot b g = g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> first | rfl | exact absurd rfl h

/-- A circuit without NOT gates satisfies the bound (both worlds are the circuit itself). -/
theorem bound_of_noNot {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hno : ∀ g ∈ gates, g.op ≠ GateOp.not)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true)) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  refine bound_of_noDD S hS gates out hg hev fun w => Or.inl ?_
  have h1 : C1 gates = gates := by
    unfold C1
    conv_rhs => rw [← List.map_id gates]
    exact List.map_congr_left fun g hm => constNot_of_ne _ g (hno g hm)
  rw [h1]
  exact zero_of_sub S S gates out hev (fun _ => subset_rfl) w

theorem oneNotBound_of_liftedBound (H : LiftedBound) : OneNotBound := by
  intro n m S h2 hS gates out hg hU hev
  by_cases hno : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact bound_of_noNot S hS gates out hg hno hev
  · push Not at hno
    obtain ⟨g, hgm, hgo⟩ := hno
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hgm
    have hb := H n m S h2 hS ((gates.take p).map (shGate n)) (liftPost n p (gates.drop (p + 1)))
      (sh n (notIn n p gates)) (fun w => liftWire n p (out w))
      (lift_ops gates p hp hg hU hgo) (lift_pre_noY n _) (sh_ne n _)
      (fun w x y => by
        have := lift_interval S gates out p hp hg hU hgo hev w x y
        rw [val_shift]
        exact this)
    have hl := length_lift n p gates hp
    unfold lift at hl
    rw [hl] at hb
    omega

theorem liftedBound_iff_oneNotBound : LiftedBound ↔ OneNotBound :=
  ⟨oneNotBound_of_liftedBound, liftedBound_of_oneNotBound⟩

/-- The lifted bound excludes every (minimal) counterexample. -/
theorem no_isCE_of_liftedBound (H : LiftedBound) {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gates : List Gate) (out : Fin m → ℕ) : ¬ IsCE S gates out := by
  intro h
  have := oneNotBound_of_liftedBound H n m S h.h2 h.hS gates out h.hg h.hU h.hev
  have := h.hlt
  omega

/-- **`LiftedBound` closes 951**: it implies the only open statement `no_minCE`. -/
theorem no_minCE_of_liftedBound (H : LiftedBound) {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gates : List Gate) (out : Fin m → ℕ) : ¬ MinCE S gates out :=
  fun M => no_isCE_of_liftedBound H S gates out M.ce

/-- L-meta-951 (same statement as `PEqualNP.Outside.L_meta_951`) from `LiftedBound`. -/
theorem L_meta_951_of_liftedBound (H : LiftedBound) : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length := by
  intro n m S h2 hS gates out hg hι hev
  exact oneNotBound_of_liftedBound H n m S h2 hS gates out hg (hU_of_ι hι) hev

end PEqualNP.Outside.L_meta_951_aux
