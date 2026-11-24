import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.LiftFrac
import PEqualNP.W951.EasySets
import PEqualNP.Kernel.W951TwoWorld
import PEqualNP.Kernel.Privacy

/-!
# Helpers for building `LiftClassFrac` from S2.1 configurations at base points

`LiftClassFrac S gates out` (LiftFrac.lean) asks for a NOT gate `p` and a `MonoFrac` family on
`lift n p gates`: for every output finitely many S2.1 configurations `(Z, a)` with `|S w|` atoms,
weights, the five S2.1 hypotheses (nonempty, join-closed, (L), zeros, ones) and loads `≤ 1`.

This file discharges everything except the load condition for configurations **at a base point**:
`Z = {(z, y)}`, atoms `(q t, l t)`, with `z` of any weight (in particular weight `≥ 2`; nothing
below is restricted to the zero point, to unit vectors or to `Zof (S w)`).

* Points: `ext_le_ext_iff`, `ext_castSucc`, `ext_last`; `hval gates p x` (the wire read by the
  NOT gate), `val_not_hval`, `hval_mono`.
* Forced values of the lift: `lift_zero`, `lift_one` (any wire), from `lift_exact`.
* Worlds: `val_lift_wld` : the lift at level `b` is the world `wld b` (`C0` / `C1`).
* Gate indices: `liftIdx`, `liftWire_gate`, `isOrAt_lift_iff`, `exists_liftIdx`.
* (ii) Class transport: `mem_liftClOr_lift_iff` (membership of a lifted class in terms of the two
  worlds of the original circuit), `mem_liftClOr_lift_real` (all points real: in terms of `gates`),
  `exists_of_mem_liftClOr_lift`; supports: `card_unit_eq_supp`, `card_unit_eq_supp_restrictGE`.
* (i) Constructors: `bp_L`, `monoFrac_lift_of_basePoints`, `liftClassFrac_of_basePoints`,
  `liftClassFrac_of_worldClasses` (loads stated on the original gates), the canonical real
  configuration `unitAtoms` with `liftClassFrac_of_realBasePoints`, and the integral blocked form
  `liftClassFrac_of_blocked_basePoints` (`mem_blockP_bp`).
* (iii) Minimal counterexamples: `notQuiet_iff_hval`, `MinCE.hval_zero`,
  `MinCE.two_le_wt_Zof`, `MinCE.exists_basePoint`, `MinCE.exists_unit_hval_false`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Base.Matching

/-! ## Lifted points -/

section Points

variable {n : ℕ}

theorem ext_castSucc (x : Fin n → Bool) (y : Bool) (c : Fin n) : ext x y c.castSucc = x c := by
  simp [ext]

theorem ext_last (x : Fin n → Bool) (y : Bool) : ext x y (Fin.last n) = y := by
  simp [ext]

theorem ext_le_ext_iff {x x' : Fin n → Bool} {y y' : Bool} :
    ext x y ≤ ext x' y' ↔ x ≤ x' ∧ y ≤ y' := by
  constructor
  · intro h
    refine ⟨fun c => ?_, ?_⟩
    · have := h c.castSucc
      rwa [ext_castSucc, ext_castSucc] at this
    · have := h (Fin.last n)
      rwa [ext_last, ext_last] at this
  · rintro ⟨hx, hy⟩ c
    unfold ext
    split_ifs
    · exact hx _
    · exact hy

/-- The weight of a point: the number of its ones. -/
def wt (z : Fin n → Bool) : ℕ := (Finset.univ.filter fun c => z c = true).card

/-- `h x`: the value at `x` of the wire read by the gate at position `p` (the NOT gate). -/
def hval (gates : List Gate) (p : ℕ) (x : Fin n → Bool) : Bool :=
  val (gates.take p) x (notIn n p gates)

/-- The NOT gate is `¬ h`. -/
theorem val_not_hval (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hN : (gates[p]'hp).op = GateOp.not) (x : Fin n → Bool) :
    val gates x (n + p) = !hval gates p x :=
  val_not gates p hp hN x

/-- `h` is monotone (it is computed by the AND/OR prefix). -/
theorem hval_mono (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) {x x' : Fin n → Bool}
    (hxx : x ≤ x') (h : hval gates p x = true) : hval gates p x' = true :=
  mono_val (gates.take p) (PEqualNP.Kernel.take_andOr hg hU p hp hN) x x'
    (fun c hc => le_antisymm (Bool.le_true _) (hc ▸ hxx c)) _ h

end Points

/-! ## Forced zeros and ones of the lift -/

section Forced

variable {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN

/-- **Forced zeros.** A wire false at `x` is false at the lifted point `(x, y)` when `y = 0`, or
when `y = 1` and `h x = 0` (the real point). -/
theorem lift_zero (x : Fin n → Bool) (y : Bool) (i : ℕ) (hy : y = true → hval gates p x = false)
    (hx : val gates x i = false) :
    val (lift n p gates) (ext x y) (liftWire n p i) = false := by
  obtain ⟨e1, -, -, e4⟩ := lift_exact (n := n) gates p hp hg hU hN x i
  cases y with
  | false =>
    cases hF : val (lift n p gates) (ext x false) (liftWire n p i) with
    | false => rfl
    | true => rw [e1 hF] at hx; exact absurd hx (by simp)
  | true => rw [e4 (hy rfl)]; exact hx

/-- **Forced ones.** A wire true at `x` is true at the lifted point `(x, y)` when `y = 1`, or when
`y = 0` and `h x = 1` (the real point). -/
theorem lift_one (x : Fin n → Bool) (y : Bool) (i : ℕ) (hy : y = false → hval gates p x = true)
    (hx : val gates x i = true) :
    val (lift n p gates) (ext x y) (liftWire n p i) = true := by
  obtain ⟨-, e2, e3, -⟩ := lift_exact (n := n) gates p hp hg hU hN x i
  cases y with
  | false => rw [e3 (hy rfl)]; exact hx
  | true => exact e2 hx

end Forced

/-! ## The two worlds are the two levels of the lift -/

/-- The world of level `b`: `C0` (NOT `:= 0`) for `b = false`, `C1` (NOT `:= 1`) for `b = true`. -/
def wld (b : Bool) (gates : List Gate) : List Gate := if b then C1 gates else C0 gates

section World

variable {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hU hN

/-- Replacing the NOT gate by a constant does not change the lift. -/
theorem lift_constNot (c : GateOp) : lift n p (gates.map (constNot c)) = lift n p gates := by
  have key : ∀ k (hk : k < gates.length), k ≠ p → constNot c (gates[k]'hk) = gates[k]'hk :=
    fun k hk hkp => constNot_of_ne c _ (fun h => hkp (hU k p hk hp h hN))
  have h1 : (gates.take p).map (constNot c) = gates.take p := by
    conv_rhs => rw [← List.map_id (gates.take p)]
    refine List.map_congr_left fun g hm => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
    rw [List.getElem_take]
    exact key i _ (by simp at hi; omega)
  have h2 : (gates.drop (p + 1)).map (constNot c) = gates.drop (p + 1) := by
    conv_rhs => rw [← List.map_id (gates.drop (p + 1))]
    refine List.map_congr_left fun g hm => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
    rw [List.getElem_drop]
    exact key _ _ (by omega)
  unfold lift
  rw [← List.map_take, ← List.map_drop, h1, h2]

/-- **The lift at level `b` is the world `b`**: `M(x, 0) = C0(x)`, `M(x, 1) = C1(x)` on every
wire. -/
theorem val_lift_wld (b : Bool) (x : Fin n → Bool) (i : ℕ) :
    val (lift n p gates) (ext x b) (liftWire n p i) = val (wld b gates) x i := by
  have main : ∀ c : GateOp, c.eval [] = b →
      val (lift n p gates) (ext x b) (liftWire n p i) = val (gates.map (constNot c)) x i := by
    intro c hc
    have hp' : p < (gates.map (constNot c)).length := by simpa using hp
    have hW : (gates.map (constNot c))[p]'hp' = ⟨c, []⟩ := by
      rw [List.getElem_map]
      generalize gates[p]'hp = g at hN
      obtain ⟨op, ins⟩ := g
      simp only at hN
      subst hN
      rfl
    have h := val_lift (n := n) (gates.map (constNot c)) p hp' x i
    rw [lift_constNot gates p hp hU hN c, val_gate _ x p hp', hW] at h
    simp only [List.map_nil, hc] at h
    exact h.symm
  cases b with
  | false => exact main GateOp.or (by simp [GateOp.eval])
  | true => exact main GateOp.and (by simp [GateOp.eval])

end World

/-! ## Gate indices of the lift -/

/-- The index in `lift n p gates` of the original gate `i ≠ p`. -/
def liftIdx (p i : ℕ) : ℕ := if i < p then i else i - 1

theorem liftWire_gate (n p i : ℕ) (hip : i ≠ p) : liftWire n p (n + i) = n + 1 + liftIdx p i := by
  unfold liftWire liftIdx; split_ifs <;> omega

theorem liftIdx_lt {gates : List Gate} {p i : ℕ} (n : ℕ) (hp : p < gates.length)
    (hi : i < gates.length) (hip : i ≠ p) : liftIdx p i < (lift n p gates).length := by
  rw [length_lift n p gates hp]; unfold liftIdx; split_ifs <;> omega

theorem liftIdx_inj {p i i' : ℕ} (hi : i ≠ p) (hi' : i' ≠ p) (h : liftIdx p i = liftIdx p i') :
    i = i' := by
  unfold liftIdx at h; split_ifs at h <;> omega

/-- Every gate index of the lift comes from an original gate other than the NOT gate. -/
theorem exists_liftIdx {gates : List Gate} {p j : ℕ} (n : ℕ) (hp : p < gates.length)
    (hj : j < (lift n p gates).length) : ∃ i, i < gates.length ∧ i ≠ p ∧ liftIdx p i = j := by
  rw [length_lift n p gates hp] at hj
  by_cases h : j < p
  · exact ⟨j, by omega, by omega, by simp [liftIdx, h]⟩
  · refine ⟨j + 1, by omega, by omega, ?_⟩
    unfold liftIdx; split_ifs <;> omega

/-- The lift keeps the operations: gate `liftIdx p i` of the lift is an OR iff gate `i` is. -/
theorem isOrAt_lift_iff {gates : List Gate} {p i : ℕ} (n : ℕ) (hp : p < gates.length)
    (hi : i < gates.length) (hip : i ≠ p) :
    IsOrAt (lift n p gates) (liftIdx p i) ↔ IsOrAt gates i := by
  have key : ∃ g, (lift n p gates)[liftIdx p i]? = some g ∧ g.op = (gates[i]'hi).op := by
    unfold lift liftIdx liftPost
    by_cases h : i < p
    · rw [ite_eq_left h, List.getElem?_append_left (by simp; omega)]
      exact ⟨shGate n (gates[i]'hi), by simp [h, hi], rfl⟩
    · rw [ite_eq_right h, List.getElem?_append_right (by simp; omega)]
      have e : i - 1 - (List.map (shGate n) (List.take p gates)).length = i - 1 - p := by
        simp; omega
      rw [e, List.getElem?_mapIdx]
      have e2 : (gates.drop (p + 1))[i - 1 - p]? = some (gates[i]'hi) := by
        rw [List.getElem?_drop, show p + 1 + (i - 1 - p) = i by omega]
        exact List.getElem?_eq_getElem hi
      rw [e2]
      exact ⟨_, rfl, rfl⟩
  obtain ⟨g, hg1, hg2⟩ := key
  unfold IsOrAt
  constructor
  · rintro ⟨g', hg', hop⟩
    rw [hg1] at hg'
    cases hg'
    exact ⟨_, List.getElem?_eq_getElem hi, hg2 ▸ hop⟩
  · rintro ⟨g', hg', hop⟩
    rw [List.getElem?_eq_getElem hi] at hg'
    cases hg'
    exact ⟨g, hg1, hg2 ▸ hop⟩

/-! ## Base-point configurations -/

/-- Lifted atoms: atom `t` is the point `(q t, l t)`. -/
def lAtoms {n k : ℕ} (q : Fin k → Fin n → Bool) (l : Fin k → Bool) : Fin k → Fin (n + 1) → Bool :=
  fun t => ext (q t) (l t)

theorem bp_join {n : ℕ} (z : Fin n → Bool) (y : Bool) :
    ∀ x ∈ ({ext z y} : Finset (Fin (n + 1) → Bool)), ∀ x' ∈ ({ext z y} : Finset _),
      x ⊔ x' ∈ ({ext z y} : Finset (Fin (n + 1) → Bool)) := by
  intro x hx x' hx'
  rw [Finset.mem_singleton] at hx hx'
  subst hx hx'
  simp

/-- **Hypothesis (L) at a base point.** For `Z = {(z, y)}` and atoms `(q t, l t)`: (L) holds as
soon as every input off in `z` is on in at most one `q t`, and (when `y = 0`) at most one atom is
at level `1`. -/
theorem bp_L {n k : ℕ} (z : Fin n → Bool) (y : Bool) (q : Fin k → Fin n → Bool)
    (l : Fin k → Bool)
    (hq : ∀ c, z c = false → ∀ s t, q s c = true → q t c = true → s = t)
    (hl : y = false → ∀ s t, l s = true → l t = true → s = t) :
    ∀ c : Fin (n + 1), (∀ x ∈ ({ext z y} : Finset (Fin (n + 1) → Bool)), x c = false) →
      ∀ s t, lAtoms q l s c = true → lAtoms q l t c = true → s = t := by
  intro c hc s t hs ht
  have hc' := hc _ (Finset.mem_singleton_self _)
  unfold lAtoms at hs ht
  unfold ext at hc' hs ht
  by_cases h : (c : ℕ) < n
  · simp only [h, dite_true] at hc' hs ht
    exact hq _ hc' s t hs ht
  · simp only [h, dite_false] at hc' hs ht
    exact hl hc' s t hs ht

/-- **S2.2 at base points.** Atom `t` is blocked by the base point `(z', y')` iff it is not below
it: not (`q t ≤ z'` and `l t ≤ y'`). -/
theorem mem_blockP_bp {n k : ℕ} (z' : Fin n → Bool) (y' : Bool) (q : Fin k → Fin n → Bool)
    (l : Fin k → Bool) (t : Fin k) :
    t ∈ blockP ({ext z' y'} : Finset (Fin (n + 1) → Bool)) (lAtoms q l) ↔
      ¬ (q t ≤ z' ∧ l t ≤ y') := by
  rw [mem_blockP]
  simp only [Finset.mem_singleton, forall_eq, lAtoms, ext_le_ext_iff]

/-! ## (ii) Class transport along the lift -/

section Transport

variable {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hU hN

/-- **Class transport.** For an original gate `i ≠ p`: its lifted copy lies in the lifted class
`cl_OR({(z, y)}, (q, l))` iff gate `i` is an OR gate, false at `z` in the world of level `y`, and
true at two or more atoms `q t`, each read in the world of its level `l t`. -/
theorem mem_liftClOr_lift_iff {k : ℕ} (z : Fin n → Bool) (y : Bool) (q : Fin k → Fin n → Bool)
    (l : Fin k → Bool) {i : ℕ} (hi : i < gates.length) (hip : i ≠ p) :
    liftIdx p i ∈ liftClOr (lift n p gates) {ext z y} (lAtoms q l) ↔
      IsOrAt gates i ∧ val (wld y gates) z (n + i) = false ∧
        1 < (Finset.univ.filter fun t => val (wld (l t) gates) (q t) (n + i) = true).card := by
  rw [mem_liftClOr, isOrAt_lift_iff n hp hi hip, ← liftWire_gate n p i hip]
  have e : atomsAt (lift n p gates) (lAtoms q l) (liftWire n p (n + i)) =
      Finset.univ.filter fun t => val (wld (l t) gates) (q t) (n + i) = true := by
    ext t
    simp only [mem_atomsAt, lAtoms, Finset.mem_filter, Finset.mem_univ, true_and,
      val_lift_wld gates p hp hU hN]
  rw [e]
  simp only [Finset.mem_singleton, forall_eq, val_lift_wld gates p hp hU hN]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨liftIdx_lt n hp hi hip, h⟩⟩

end Transport

/-- Every gate of a lifted class is the lifted copy of an original gate `i ≠ p`. -/
theorem exists_of_mem_liftClOr_lift {n k : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (Z : Finset (Fin (n + 1) → Bool))
    (a : Fin k → Fin (n + 1) → Bool) {j : ℕ} (hj : j ∈ liftClOr (lift n p gates) Z a) :
    ∃ i, i < gates.length ∧ i ≠ p ∧ liftIdx p i = j :=
  exists_liftIdx n hp (mem_liftClOr.mp hj).1

/-- The original-circuit form of a lifted class: gate `i ≠ p` is an OR gate, false at `z` in the
world of level `y`, true at two or more atoms `q t` in the world of level `l t`. -/
def InWorldCl {n k : ℕ} (gates : List Gate) (p : ℕ) (z : Fin n → Bool) (y : Bool)
    (q : Fin k → Fin n → Bool) (l : Fin k → Bool) (i : ℕ) : Prop :=
  i < gates.length ∧ i ≠ p ∧ IsOrAt gates i ∧ val (wld y gates) z (n + i) = false ∧
    1 < (Finset.univ.filter fun t => val (wld (l t) gates) (q t) (n + i) = true).card

theorem mem_liftClOr_lift_iff_exists {n k : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (z : Fin n → Bool) (y : Bool)
    (q : Fin k → Fin n → Bool) (l : Fin k → Bool) (j : ℕ) :
    j ∈ liftClOr (lift n p gates) {ext z y} (lAtoms q l) ↔
      ∃ i, liftIdx p i = j ∧ InWorldCl gates p z y q l i := by
  constructor
  · intro hj
    obtain ⟨i, hi, hip, rfl⟩ := exists_of_mem_liftClOr_lift gates p hp _ _ hj
    exact ⟨i, rfl, hi, hip, (mem_liftClOr_lift_iff gates p hp hU hN z y q l hi hip).mp hj⟩
  · rintro ⟨i, rfl, hi, hip, h⟩
    exact (mem_liftClOr_lift_iff gates p hp hU hN z y q l hi hip).mpr h

/-! ## (i) Constructors -/

section Constructors

variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
  (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
  (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))

include hg hU hN hev

/-- The S2.1 hypotheses "zeros" and "ones" of one base-point configuration of output `w`. -/
theorem bp_zero (w : Fin m) (z : Fin n → Bool) (y : Bool) (hz : ∀ v ∈ S w, z v = false)
    (hzy : y = true → hval gates p z = false) :
    ∀ x ∈ ({ext z y} : Finset (Fin (n + 1) → Bool)),
      val (lift n p gates) x (liftWire n p (out w)) = false := by
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  refine lift_zero gates p hp hg hU hN z y _ hzy ?_
  rw [hev w z, decide_eq_false_iff_not]
  rintro ⟨v, hv, hzv⟩
  rw [hz v hv] at hzv
  exact Bool.noConfusion hzv

theorem bp_one {k : ℕ} (w : Fin m) (q : Fin k → Fin n → Bool) (l : Fin k → Bool)
    (hqS : ∀ t, ∃ v ∈ S w, q t v = true) (hql : ∀ t, l t = false → hval gates p (q t) = true) :
    ∀ t, val (lift n p gates) (lAtoms q l t) (liftWire n p (out w)) = true := by
  intro t
  refine lift_one gates p hp hg hU hN (q t) (l t) _ (hql t) ?_
  rw [hev w (q t), decide_eq_true_iff]
  exact hqS t

/-- **Constructor (general base points).** For every output `w`, `k w` configurations: base
point `(z, y)` with `z` off on `S w` and (`y = 1` ⇒ `h z = 0`); `|S w|` atoms `(q t, l t)`, each
`q t` hitting `S w`, (`l t = 0` ⇒ `h (q t) = 1`); every input off in `z` on in at most one atom;
if `y = 0` at most one atom at level `1`. All S2.1 hypotheses of `MonoFrac` hold; what remains is
the load condition `hload`. -/
theorem monoFrac_lift_of_basePoints
    (k : Fin m → ℕ) (z : ∀ w, Fin (k w) → Fin n → Bool) (y : ∀ w, Fin (k w) → Bool)
    (q : ∀ w, Fin (k w) → Fin ((S w).card - 1 + 1) → Fin n → Bool)
    (l : ∀ w, Fin (k w) → Fin ((S w).card - 1 + 1) → Bool) (lam : ∀ w, Fin (k w) → ℝ)
    (hlam0 : ∀ w j, 0 ≤ lam w j) (hlam1 : ∀ w, ∑ j, lam w j = 1)
    (hz : ∀ w j, ∀ v ∈ S w, z w j v = false)
    (hzy : ∀ w j, y w j = true → hval gates p (z w j) = false)
    (hqS : ∀ w j t, ∃ v ∈ S w, q w j t v = true)
    (hql : ∀ w j t, l w j t = false → hval gates p (q w j t) = true)
    (hq : ∀ w j c, z w j c = false → ∀ s t, q w j s c = true → q w j t c = true → s = t)
    (hl : ∀ w j, y w j = false → ∀ s t, l w j s = true → l w j t = true → s = t)
    (hload : ∀ g : ℕ, ∑ w, ∑ j,
      (if g ∈ liftClOr (lift n p gates) {ext (z w j) (y w j)} (lAtoms (q w j) (l w j))
        then lam w j else 0) ≤ 1) :
    MonoFrac (N := n + 1) (lift n p gates) (fun w => (S w).card - 1)
      (fun w => liftWire n p (out w)) :=
  ⟨k, fun w j => {ext (z w j) (y w j)}, fun w j => lAtoms (q w j) (l w j), lam, hlam0, hlam1,
    fun _ _ => Finset.singleton_nonempty _, fun w j => bp_join (z w j) (y w j),
    fun w j => bp_L (z w j) (y w j) (q w j) (l w j) (hq w j) (hl w j),
    fun w j => bp_zero S gates out p hp hg hU hN hev w (z w j) (y w j) (hz w j) (hzy w j),
    fun w j => bp_one S gates out p hp hg hU hN hev w (q w j) (l w j) (hqS w j) (hql w j),
    hload⟩

/-- **Constructor, `LiftClassFrac` form.** -/
theorem liftClassFrac_of_basePoints
    (k : Fin m → ℕ) (z : ∀ w, Fin (k w) → Fin n → Bool) (y : ∀ w, Fin (k w) → Bool)
    (q : ∀ w, Fin (k w) → Fin ((S w).card - 1 + 1) → Fin n → Bool)
    (l : ∀ w, Fin (k w) → Fin ((S w).card - 1 + 1) → Bool) (lam : ∀ w, Fin (k w) → ℝ)
    (hlam0 : ∀ w j, 0 ≤ lam w j) (hlam1 : ∀ w, ∑ j, lam w j = 1)
    (hz : ∀ w j, ∀ v ∈ S w, z w j v = false)
    (hzy : ∀ w j, y w j = true → hval gates p (z w j) = false)
    (hqS : ∀ w j t, ∃ v ∈ S w, q w j t v = true)
    (hql : ∀ w j t, l w j t = false → hval gates p (q w j t) = true)
    (hq : ∀ w j c, z w j c = false → ∀ s t, q w j s c = true → q w j t c = true → s = t)
    (hl : ∀ w j, y w j = false → ∀ s t, l w j s = true → l w j t = true → s = t)
    (hload : ∀ g : ℕ, ∑ w, ∑ j,
      (if g ∈ liftClOr (lift n p gates) {ext (z w j) (y w j)} (lAtoms (q w j) (l w j))
        then lam w j else 0) ≤ 1) :
    LiftClassFrac S gates out :=
  ⟨p, hp, hN, monoFrac_lift_of_basePoints S gates out p hp hg hU hN hev k z y q l lam hlam0 hlam1
    hz hzy hqS hql hq hl hload⟩

open Classical in
/-- **Constructor with loads on the original gates.** As `liftClassFrac_of_basePoints`, the load
condition stated on the gates `i ≠ p` of the original circuit through the two-world classes
`InWorldCl` (no lifted circuit in the hypotheses). -/
theorem liftClassFrac_of_worldClasses
    (k : Fin m → ℕ) (z : ∀ w, Fin (k w) → Fin n → Bool) (y : ∀ w, Fin (k w) → Bool)
    (q : ∀ w, Fin (k w) → Fin ((S w).card - 1 + 1) → Fin n → Bool)
    (l : ∀ w, Fin (k w) → Fin ((S w).card - 1 + 1) → Bool) (lam : ∀ w, Fin (k w) → ℝ)
    (hlam0 : ∀ w j, 0 ≤ lam w j) (hlam1 : ∀ w, ∑ j, lam w j = 1)
    (hz : ∀ w j, ∀ v ∈ S w, z w j v = false)
    (hzy : ∀ w j, y w j = true → hval gates p (z w j) = false)
    (hqS : ∀ w j t, ∃ v ∈ S w, q w j t v = true)
    (hql : ∀ w j t, l w j t = false → hval gates p (q w j t) = true)
    (hq : ∀ w j c, z w j c = false → ∀ s t, q w j s c = true → q w j t c = true → s = t)
    (hl : ∀ w j, y w j = false → ∀ s t, l w j s = true → l w j t = true → s = t)
    (hload : ∀ i : ℕ, i < gates.length → i ≠ p → ∑ w, ∑ j,
      (if InWorldCl gates p (z w j) (y w j) (q w j) (l w j) i then lam w j else 0) ≤ 1) :
    LiftClassFrac S gates out := by
  refine liftClassFrac_of_basePoints S gates out p hp hg hU hN hev k z y q l lam hlam0 hlam1
    hz hzy hqS hql hq hl fun g => ?_
  by_cases hex : ∃ i, i < gates.length ∧ i ≠ p ∧ liftIdx p i = g
  · obtain ⟨i, hi, hip, rfl⟩ := hex
    refine le_of_eq_of_le ?_ (hload i hi hip)
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j _ => ?_
    have hiff : liftIdx p i ∈ liftClOr (lift n p gates) {ext (z w j) (y w j)}
        (lAtoms (q w j) (l w j)) ↔ InWorldCl gates p (z w j) (y w j) (q w j) (l w j) i := by
      rw [mem_liftClOr_lift_iff gates p hp hU hN _ _ _ _ hi hip]
      exact ⟨fun h => ⟨hi, hip, h⟩, fun h => h.2.2⟩
    simp only [hiff]
  · rw [Finset.sum_eq_zero]
    · exact zero_le_one
    · intro w _
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right]
      intro hgm
      exact hex (exists_of_mem_liftClOr_lift gates p hp _ _ hgm)

/-- **Integral blocked constructor.** One base-point configuration per output; for `u ≠ v` at
most one atom of `u` is not below the base point of `v`, or conversely (`mem_blockP_bp`). No load
condition is left. -/
theorem liftClassFrac_of_blocked_basePoints
    (z : Fin m → Fin n → Bool) (y : Fin m → Bool)
    (q : ∀ w, Fin ((S w).card - 1 + 1) → Fin n → Bool)
    (l : ∀ w, Fin ((S w).card - 1 + 1) → Bool)
    (hz : ∀ w, ∀ v ∈ S w, z w v = false)
    (hzy : ∀ w, y w = true → hval gates p (z w) = false)
    (hqS : ∀ w t, ∃ v ∈ S w, q w t v = true)
    (hql : ∀ w t, l w t = false → hval gates p (q w t) = true)
    (hq : ∀ w c, z w c = false → ∀ s t, q w s c = true → q w t c = true → s = t)
    (hl : ∀ w, y w = false → ∀ s t, l w s = true → l w t = true → s = t)
    (hblock : ∀ u v : Fin m, u ≠ v →
      (Finset.univ.filter fun t => ¬ (q u t ≤ z v ∧ l u t ≤ y v)).card ≤ 1 ∨
      (Finset.univ.filter fun t => ¬ (q v t ≤ z u ∧ l v t ≤ y u)).card ≤ 1) :
    LiftClassFrac S gates out := by
  have hb : ∀ u v : Fin m, blockP ({ext (z v) (y v)} : Finset (Fin (n + 1) → Bool))
      (lAtoms (q u) (l u)) = Finset.univ.filter fun t => ¬ (q u t ≤ z v ∧ l u t ≤ y v) := by
    intro u v
    ext t
    rw [mem_blockP_bp]
    simp
  refine ⟨p, hp, hN, monoFrac_of_blocked (lift n p gates)
    (fun g hm => (lift_ops gates p hp hg hU hN g hm).1) _ _
    (fun w => {ext (z w) (y w)}) (fun w => lAtoms (q w) (l w))
    (fun _ => Finset.singleton_nonempty _) (fun w => bp_join (z w) (y w))
    (fun w => bp_L (z w) (y w) (q w) (l w) (hq w) (hl w))
    (fun w => bp_zero S gates out p hp hg hU hN hev w (z w) (y w) (hz w) (hzy w))
    (fun w => bp_one S gates out p hp hg hU hN hev w (q w) (l w) (hqS w) (hql w))
    fun u v huv => ?_⟩
  rw [hb u v, hb v u]
  exact hblock u v huv

end Constructors

/-! ## Real points: the world of a point's own level is the circuit -/

section Real

variable {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hU hN

/-- At the real level `¬ h x` the world agrees with the circuit on every wire. -/
theorem val_wld_real (x : Fin n → Bool) (i : ℕ) :
    val (wld (!hval gates p x) gates) x i = val gates x i := by
  rw [← val_lift_wld gates p hp hU hN, ← val_not_hval gates p hp hN x]
  exact (val_lift gates p hp x i).symm

/-- On `{h = 1}` the lower world `C0` is the circuit. -/
theorem val_wld_false_of_hval (x : Fin n → Bool) (hx : hval gates p x = true) (i : ℕ) :
    val (wld false gates) x i = val gates x i := by
  have := val_wld_real gates p hp hU hN x i
  rwa [hx] at this

/-- On `{h = 0}` the upper world `C1` is the circuit. -/
theorem val_wld_true_of_hval (x : Fin n → Bool) (hx : hval gates p x = false) (i : ℕ) :
    val (wld true gates) x i = val gates x i := by
  have := val_wld_real gates p hp hU hN x i
  rwa [hx] at this

end Real

/-! ## The canonical configuration at a base point `z`: atoms `z + e_u`, `u ∈ S`, real level -/

section Canonical

variable {n : ℕ}

/-- An enumeration of `S` by `Fin (|S| - 1 + 1)` (the index type of `MonoFrac` atoms). -/
noncomputable def enumS (S : Finset (Fin n)) (hS : 1 ≤ S.card) : Fin (S.card - 1 + 1) → Fin n :=
  fun t => S.orderEmbOfFin rfl (Fin.cast (by omega) t)

theorem enumS_mem (S : Finset (Fin n)) (hS : 1 ≤ S.card) (t : Fin (S.card - 1 + 1)) :
    enumS S hS t ∈ S :=
  Finset.orderEmbOfFin_mem _ rfl _

theorem enumS_injective (S : Finset (Fin n)) (hS : 1 ≤ S.card) :
    Function.Injective (enumS S hS) := by
  intro s t h
  have := (S.orderEmbOfFin rfl).injective h
  exact Fin.cast_injective _ this

theorem exists_enumS (S : Finset (Fin n)) (hS : 1 ≤ S.card) {v : Fin n} (hv : v ∈ S) :
    ∃ t, enumS S hS t = v := by
  have hr : v ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hv
  obtain ⟨t, ht⟩ := hr
  exact ⟨Fin.cast (by omega) t, by simpa [enumS] using ht⟩

/-- Counting atoms is counting elements of `S`. -/
theorem card_filter_enumS (S : Finset (Fin n)) (hS : 1 ≤ S.card) (P : Fin n → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun t => P (enumS S hS t)).card = (S.filter P).card := by
  refine Finset.card_bij (fun t _ => enumS S hS t) ?_ ?_ ?_
  · intro t ht
    exact Finset.mem_filter.mpr ⟨enumS_mem S hS t, (Finset.mem_filter.mp ht).2⟩
  · intro s _ t _ h
    exact enumS_injective S hS h
  · intro v hv
    obtain ⟨hvS, hPv⟩ := Finset.mem_filter.mp hv
    obtain ⟨t, rfl⟩ := exists_enumS S hS hvS
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPv⟩, rfl⟩

/-- The unit atoms above `z`: atom `t` is `z + e_u`, `u` the `t`-th element of `S`. -/
noncomputable def unitAtoms (z : Fin n → Bool) (S : Finset (Fin n)) (hS : 1 ≤ S.card) :
    Fin (S.card - 1 + 1) → Fin n → Bool :=
  fun t => Function.update z (enumS S hS t) true

theorem le_update_true (z : Fin n → Bool) (u : Fin n) : z ≤ Function.update z u true := by
  intro c
  by_cases h : c = u
  · subst h; rw [Function.update_self]; exact Bool.le_true _
  · rw [Function.update_of_ne h]

theorem unitAtoms_L (z : Fin n → Bool) (S : Finset (Fin n)) (hS : 1 ≤ S.card) :
    ∀ c, z c = false → ∀ s t, unitAtoms z S hS s c = true → unitAtoms z S hS t c = true →
      s = t := by
  intro c hc s t hs ht
  have key : ∀ r, unitAtoms z S hS r c = true → c = enumS S hS r := by
    intro r hr
    by_contra hne
    unfold unitAtoms at hr
    rw [Function.update_of_ne hne, hc] at hr
    exact Bool.noConfusion hr
  exact enumS_injective S hS ((key s hs).symm.trans (key t ht))

theorem unitAtoms_hit (z : Fin n → Bool) (S : Finset (Fin n)) (hS : 1 ≤ S.card)
    (t : Fin (S.card - 1 + 1)) : ∃ v ∈ S, unitAtoms z S hS t v = true :=
  ⟨enumS S hS t, enumS_mem S hS t, by simp [unitAtoms]⟩

end Canonical

open Classical in
/-- **The class of the real base point `z` for the set `S`, in the original circuit**: gate
`i ≠ p` is an OR gate, false at `z`, and true at `z + e_u` for two or more `u ∈ S`, the atoms read
in the world of `z` (`C0` if `h z = 1`: then the atoms are real, `val_wld_false_of_hval`; `C1` if
`h z = 0`). -/
def RealCl {n : ℕ} (gates : List Gate) (p : ℕ) (S : Finset (Fin n)) (z : Fin n → Bool) (i : ℕ) :
    Prop :=
  i < gates.length ∧ i ≠ p ∧ IsOrAt gates i ∧ val gates z (n + i) = false ∧
    1 < (S.filter fun u =>
      val (wld (!hval gates p z) gates) (Function.update z u true) (n + i) = true).card

section CanonicalConstructor

variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
  (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
  (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))

include hU hN in
/-- The lifted class of the canonical configuration at `z` is `RealCl`. -/
theorem inWorldCl_unit_iff (T : Finset (Fin n)) (hT : 1 ≤ T.card) (z : Fin n → Bool) (i : ℕ) :
    InWorldCl gates p z (!hval gates p z) (unitAtoms z T hT) (fun _ => !hval gates p z) i ↔
      RealCl gates p T z i := by
  unfold InWorldCl RealCl
  rw [val_wld_real gates p hp hU hN z (n + i)]
  have e := card_filter_enumS T hT
    (fun u => val (wld (!hval gates p z) gates) (Function.update z u true) (n + i) = true)
  unfold unitAtoms
  rw [e]

include hg hU hN hev

open Classical in
/-- **Constructor (real base points, any weight).** For every output `w` a weighted mixture of
base points `z w j` off on `S w`; the configuration of `z` is `Z = {(z, ¬ h z)}` with the `|S w|`
atoms `(z + e_u, ¬ h z)`, `u ∈ S w`. Every S2.1 hypothesis holds automatically; the only
hypothesis left is the load condition on the classes `RealCl` of the original circuit. -/
theorem liftClassFrac_of_realBasePoints (h1 : ∀ w, 1 ≤ (S w).card)
    (k : Fin m → ℕ) (z : ∀ w, Fin (k w) → Fin n → Bool) (lam : ∀ w, Fin (k w) → ℝ)
    (hlam0 : ∀ w j, 0 ≤ lam w j) (hlam1 : ∀ w, ∑ j, lam w j = 1)
    (hz : ∀ w j, ∀ v ∈ S w, z w j v = false)
    (hload : ∀ i : ℕ, i < gates.length → i ≠ p → ∑ w, ∑ j,
      (if RealCl gates p (S w) (z w j) i then lam w j else 0) ≤ 1) :
    LiftClassFrac S gates out := by
  refine liftClassFrac_of_worldClasses S gates out p hp hg hU hN hev k z
    (fun w j => !hval gates p (z w j)) (fun w j => unitAtoms (z w j) (S w) (h1 w))
    (fun w j _ => !hval gates p (z w j)) lam hlam0 hlam1 hz
    (fun w j h => by simpa using h)
    (fun w j t => unitAtoms_hit (z w j) (S w) (h1 w) t)
    (fun w j t h => hval_mono gates p hp hg hU hN (le_update_true _ _) (by simpa using h))
    (fun w j => unitAtoms_L (z w j) (S w) (h1 w))
    (fun w j h s t hs _ => by rw [h] at hs; exact Bool.noConfusion hs)
    fun i hi hip => ?_
  refine le_of_eq_of_le ?_ (hload i hi hip)
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [inWorldCl_unit_iff gates p hp hU hN (S w) (h1 w) (z w j) i]

open Classical in
/-- **Integral form**: one real base point per output, the classes `RealCl` pairwise disjoint. -/
theorem liftClassFrac_of_disjoint_realBasePoints (h1 : ∀ w, 1 ≤ (S w).card)
    (z : Fin m → Fin n → Bool) (hz : ∀ w, ∀ v ∈ S w, z w v = false)
    (hdis : ∀ u v : Fin m, u ≠ v → ∀ i, i < gates.length → i ≠ p →
      RealCl gates p (S u) (z u) i → ¬ RealCl gates p (S v) (z v) i) :
    LiftClassFrac S gates out := by
  refine liftClassFrac_of_realBasePoints S gates out p hp hg hU hN hev h1 (fun _ => 1)
    (fun w _ => z w) (fun _ _ => 1) (fun _ _ => zero_le_one) (fun _ => by simp)
    (fun w _ => hz w) fun i hi hip => ?_
  simp only [Fin.sum_univ_one]
  by_cases hex : ∃ u, RealCl gates p (S u) (z u) i
  · obtain ⟨u, hu⟩ := hex
    rw [Finset.sum_eq_single u]
    · simp [hu]
    · intro v _ hvu
      rw [ite_eq_right (hdis u v (Ne.symm hvu) i hi hip hu)]
    · simp
  · push Not at hex
    rw [Finset.sum_eq_zero]
    · exact zero_le_one
    · intro v _
      rw [ite_eq_right (hex v)]

end CanonicalConstructor

/-! ## (ii) Supports: unit atoms above `z` are the kernel support `I_z`, also along `restrictGE` -/

section Supp

open PEqualNP.Kernel

variable {n : ℕ}

/-- In any list circuit `W` (e.g. a world `wld b gates`): the elements `u ∈ S` whose unit atom
`z + e_u` switches gate `i` on are `S ∩ I_z(i)`, `I_z` the kernel support at the base point `z`
(`z` off on `S`, the gate off at `z`). -/
theorem filter_unit_eq_supp (W : List Gate) (z : Fin n → Bool) (S : Finset (Fin n))
    (hz : ∀ v ∈ S, z v = false) (i : Fin W.length) (hzi : val W z (n + i) = false) :
    (S.filter fun u => val W (Function.update z u true) (n + i) = true) =
      S ∩ (ofList W W.length : Dag n _).supp z (Fin.natAdd n i) := by
  ext u
  rw [Finset.mem_filter, Finset.mem_inter, Dag.mem_supp, ofList_val, ofList_val]
  simp only [Fin.natAdd, hzi, and_true]
  constructor
  · rintro ⟨hu, h⟩; exact ⟨hu, hz u hu, h⟩
  · rintro ⟨hu, -, h⟩; exact ⟨hu, h⟩

/-- **Along `restrictGE z`**: the same set is `S ∩ I_0(i)` in the circuit restricted to the cube
`{x ≥ z}` (base point `0`). -/
theorem filter_unit_eq_supp_restrictGE (W : List Gate) (z : Fin n → Bool) (S : Finset (Fin n))
    (hz : ∀ v ∈ S, z v = false) (i : Fin W.length) (hzi : val W z (n + i) = false) :
    (S.filter fun u => val W (Function.update z u true) (n + i) = true) =
      S ∩ ((ofList W W.length : Dag n _).restrictGE z).supp (fun _ => false) (Fin.natAdd n i) := by
  rw [Dag.supp_restrictGE_zero]
  exact filter_unit_eq_supp W z S hz i hzi

end Supp

/-! ## (iii) Minimal counterexamples: where the base points are -/

section MinCEFacts

variable {n : ℕ}

/-- The NOT gate of any split of the list is the gate at `p`; its value is `¬ h`. -/
theorem not_eval_split (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (pre : List Gate) (g : Gate)
    (rest : List Gate) (h : gates = pre ++ g :: rest) (hop : g.op = GateOp.not)
    (x : Fin n → Bool) :
    g.op.eval (g.inputs.map fun j => val pre x j) = !hval gates p x := by
  have hlt : pre.length < gates.length := by rw [h]; simp
  have hget : gates[pre.length]'hlt = g := by subst h; simp
  have hlen : pre.length = p := hU pre.length p hlt hp (hget ▸ hop) hN
  subst hlen
  rw [← val_not_hval gates _ hp hN x, val_gate gates x _ hp, hget]
  have htake : gates.take pre.length = pre := by subst h; simp
  rw [htake]

/-- `NotQuiet Q` (the set `Q` is easy) says `h (Zof Q) = 0`. -/
theorem notQuiet_iff_hval (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (Q : Finset (Fin n)) :
    NotQuiet Q gates ↔ hval gates p (Zof Q) = false := by
  constructor
  · intro h
    have := h (gates.take p) (gates[p]'hp) (gates.drop (p + 1)) (split_at hp).symm hN
    rw [not_eval_split gates p hp hU hN _ _ _ (split_at hp).symm hN] at this
    simpa using this
  · intro hq pre g rest h hop
    rw [not_eval_split gates p hp hU hN pre g rest h hop, hq]
    rfl

variable {m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- In a minimal counterexample `h 0 = 0`: every type-0 base point (`h z = 1`) is nonzero. -/
theorem MinCE.hval_zero (M : MinCE S gates out) (p : ℕ) (hp : p < gates.length)
    (hN : (gates[p]'hp).op = GateOp.not) : hval gates p (fun _ : Fin n => false) = false := by
  have h := (notQuiet_iff_hval gates p hp M.ce.hU hN Finset.univ).mp M.h0
  have e : Zof (Finset.univ : Finset (Fin n)) = fun _ => false := by
    funext c; simp [Zof]
  rwa [e] at h

theorem MinCE.wt_pos_of_hval (M : MinCE S gates out) (p : ℕ) (hp : p < gates.length)
    (hN : (gates[p]'hp).op = GateOp.not) (z : Fin n → Bool) (hz : hval gates p z = true) :
    1 ≤ wt z := by
  by_contra hw
  have h0 : z = fun _ => false := by
    funext c
    have : (Finset.univ.filter fun c => z c = true) = ∅ := by
      rw [← Finset.card_eq_zero]; unfold wt at hw; omega
    cases hc : z c
    · rfl
    · have : c ∈ (Finset.univ.filter fun c => z c = true) := by simp [hc]
      simp_all
  rw [h0, M.hval_zero p hp hN] at hz
  exact Bool.noConfusion hz

/-- **Weight `≥ 2`.** In a minimal counterexample the zero point `Zof (S w)` of every set has
weight at least `2` (two or more variables lie outside `S w`): from `core`. -/
theorem MinCE.two_le_wt_Zof (M : MinCE S gates out) (w : Fin m) : 2 ≤ wt (Zof (S w)) := by
  classical
  have C := M.ce
  obtain ⟨u, hu⟩ : (S w).Nonempty := Finset.card_pos.mp (by have := C.h2 w; omega)
  have hc := M.core u ⟨w, hu⟩
  obtain ⟨w', hw', hne⟩ := Finset.exists_mem_ne (show 1 < _ from hc) w
  obtain ⟨-, -, h3⟩ := Finset.mem_filter.mp hw'
  have hint := C.hS w' w hne
  have hsd := Finset.card_sdiff_add_card_inter (S w') (S w)
  have hsub : S w' \ S w ⊆ Finset.univ.filter fun c => Zof (S w) c = true := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Zof, decide_eq_true_eq]
    exact (Finset.mem_sdiff.mp hc).2
  have := Finset.card_le_card hsub
  unfold wt
  omega

/-- **Existence of a weight-`≥ 2` type-0 base point.** A minimal counterexample has a set `S w`
of size `≥ 4` whose zero point `z = Zof (S w)` is off on `S w`, has `h z = 1` (so `(z, 0)` is a
real type-0 base point and all atoms `z + e_u` are real) and has weight `≥ 2`. -/
theorem MinCE.exists_basePoint (M : MinCE S gates out) (p : ℕ) (hp : p < gates.length)
    (hN : (gates[p]'hp).op = GateOp.not) :
    ∃ w, 4 ≤ (S w).card ∧ (∀ v ∈ S w, Zof (S w) v = false) ∧
      hval gates p (Zof (S w)) = true ∧ 2 ≤ wt (Zof (S w)) := by
  obtain ⟨w, h4, hq⟩ := M.hard4
  refine ⟨w, h4, fun v hv => by simp [Zof, hv], ?_, M.two_le_wt_Zof w⟩
  rw [notQuiet_iff_hval gates p hp M.ce.hU hN] at hq
  simpa using hq

/-- In a minimal counterexample some unit vector has `h (e_u) = 0` (else every set is `Good`):
`h` is not `≥` the threshold-1 function. -/
theorem MinCE.exists_unit_hval_false (M : MinCE S gates out) (p : ℕ) (hp : p < gates.length)
    (hN : (gates[p]'hp).op = GateOp.not) : ∃ u : Fin n, hval gates p (eof u) = false := by
  have C := M.ce
  by_contra hall
  push Not at hall
  have hgood : ∀ Q : Finset (Fin n), Good Q gates := by
    intro Q pre g rest h
    by_cases hop : g.op = GateOp.not
    · refine Or.inr (Or.inr fun u => ?_)
      rw [not_eval_split gates p hp C.hU hN pre g rest h hop]
      have := hall u
      simp only [ne_eq, Bool.not_eq_false] at this
      rw [this]; rfl
    · have hmem : g ∈ gates := by rw [h]; simp
      obtain ⟨ho, hl⟩ := C.hg g hmem
      exact Or.inl ⟨by tauto, hl⟩
  have := L951_core_c S gates out C.hev (chargeOKc_of S gates out
    (charge_of_good S gates out C.hS C.hev fun w => hgood (S w)))
  have := C.hlt
  omega

end MinCEFacts

end PEqualNP.Outside.L_meta_951_aux
