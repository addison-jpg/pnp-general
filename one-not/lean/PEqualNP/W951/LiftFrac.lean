import Mathlib
import PEqualNP.Defs
import PEqualNP.Base.Matching.Hall
import PEqualNP.W951.LiftBound
import PEqualNP.W951.LiftCount

/-!
# Lifted class counting gives the bound with one gate to spare (bridge "lifted ClassFrac ⇒ bound")

The lifted circuit `lift n p gates` of a one-NOT circuit is a `MonoList` on `n + 1` inputs with
`gates.length - 1` gates.  Counting S2.1 classes (`LiftCount.lean`) in it therefore bounds
`gates.length - 1`, i.e. gives `s ≥ base + 1`.

* `mono_frac_bound` : generic monotone list; for each `w` a weighted mixture of S2.1 configurations
  with `d w + 1` atoms, every gate with load at most `1` ⇒ `∑ d w ≤ gs.length`
  (`sum_le_card_of_frac_subset` + `lift_count`).
* `lift_integral_bound` (1) : one configuration per output, pairwise blocked
  ⇒ `∑ (|S w| - 1) ≤ gates.length - 1` (`lift_family_le_length` + `length_lift`).
* `lift_frac_bound` (2) : the fractional version, loads `≤ 1` on the lifted circuit.
* `LiftClassFrac S gates out` (3) : there is a NOT gate whose lift carries such a fractional family;
  `bound_of_liftClassFrac`, `not_isCE_of_liftClassFrac`,
  `no_minCE_of_liftClassFrac : (∀ ..., MinCE → LiftClassFrac) → ∀ ..., ¬ MinCE`.
* `monoFrac_of_disjoint`, `monoFrac_of_blocked` : an integral family with pairwise disjoint
  (pairwise blocked) classes is a fractional family (weights `1`); `IsCE.exists_not`,
  `MinCE.exists_not` : a (minimal) counterexample has a NOT gate.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Base.Matching

/-- A fractional family of S2.1 configurations on a gate list `gs` over `N` inputs: output `w`
(wire `o w`, demand `d w`) mixes `k w` configurations `(Z w j, a w j)` with `d w + 1` atoms, with
weights `lam w j ≥ 0` summing to `1`; every gate has load at most `1`. -/
def MonoFrac {N m : ℕ} (gs : List Gate) (d : Fin m → ℕ) (o : Fin m → ℕ) : Prop :=
  ∃ (k : Fin m → ℕ) (Z : ∀ w, Fin (k w) → Finset (Fin N → Bool))
    (a : ∀ w, Fin (k w) → Fin (d w + 1) → Fin N → Bool) (lam : ∀ w, Fin (k w) → ℝ),
    (∀ w j, 0 ≤ lam w j) ∧ (∀ w, ∑ j, lam w j = 1) ∧
    (∀ w j, (Z w j).Nonempty) ∧ (∀ w j, ∀ x ∈ Z w j, ∀ y ∈ Z w j, x ⊔ y ∈ Z w j) ∧
    (∀ w j, ∀ c : Fin N, (∀ x ∈ Z w j, x c = false) →
      ∀ s t, a w j s c = true → a w j t c = true → s = t) ∧
    (∀ w j, ∀ x ∈ Z w j, val gs x (o w) = false) ∧
    (∀ w j, ∀ t, val gs (a w j t) (o w) = true) ∧
    ∀ g : ℕ, ∑ w, ∑ j, (if g ∈ liftClOr gs (Z w j) (a w j) then lam w j else 0) ≤ 1

/-- Double counting: a fractional family on a monotone list gives `∑ d w ≤ gs.length`. -/
theorem mono_frac_bound {N m : ℕ} (gs : List Gate) (hm : MonoList gs) (d : Fin m → ℕ)
    (o : Fin m → ℕ) (h : MonoFrac (N := N) gs d o) : ∑ w, d w ≤ gs.length := by
  obtain ⟨k, Z, a, lam, hlam0, hlam1, hZ, hjoin, hL, hZo, hao, hload⟩ := h
  have := sum_le_card_of_frac_subset Finset.univ k lam
    (fun w j => liftClOr gs (Z w j) (a w j)) d hlam0 (fun w _ => hlam1 w)
    (fun w j => by
      have := lift_count gs hm (Z w j) (hZ w j) (hjoin w j) (a w j) (hL w j) (o w)
        (hZo w j) (hao w j)
      simpa using this)
    hload (Finset.range gs.length) (fun w _ j g hg => by
      have := liftClOr_subset gs (Z w j) (a w j) hg
      simp only [liftCl, Finset.mem_filter] at this
      exact this.1)
  simpa using this

/-! ## (1) Integral: one configuration per output, pairwise blocked -/

/-- **Integral lifted bound.** One NOT gate (position `p`); if every output has an S2.1
configuration in the lifted circuit with `|S w|` atoms, and the configurations are pairwise
blocked, then `∑ (|S w| - 1) ≤ gates.length - 1`. -/
theorem lift_integral_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
    (Z : Fin m → Finset (Fin (n + 1) → Bool))
    (a : ∀ w : Fin m, Fin (S w).card → Fin (n + 1) → Bool)
    (hZ : ∀ w, (Z w).Nonempty) (hjoin : ∀ w, ∀ x ∈ Z w, ∀ y ∈ Z w, x ⊔ y ∈ Z w)
    (hL : ∀ w, ∀ c : Fin (n + 1), (∀ x ∈ Z w, x c = false) →
      ∀ s t, a w s c = true → a w t c = true → s = t)
    (hZo : ∀ w, ∀ x ∈ Z w, val (lift n p gates) x (liftWire n p (out w)) = false)
    (hao : ∀ w, ∀ t, val (lift n p gates) (a w t) (liftWire n p (out w)) = true)
    (hblock : ∀ u v : Fin m, u ≠ v →
      (blockP (Z v) (a u)).card ≤ 1 ∨ (blockP (Z u) (a v)).card ≤ 1) :
    ∑ w, ((S w).card - 1) ≤ gates.length - 1 := by
  have h := lift_family_le_length (lift n p gates) (lift_ops gates p hp hg hU hN) Finset.univ
    (fun w : Fin m => (S w).card) Z a (fun w => liftWire n p (out w))
    (fun w _ => hZ w) (fun w _ => hjoin w) (fun w _ => hL w) (fun w _ => hZo w)
    (fun w _ => hao w) (fun u _ v _ => hblock u v)
  rwa [length_lift n p gates hp] at h

/-! ## (2) Fractional -/

/-- **Fractional lifted bound.** One NOT gate (position `p`); if the lifted circuit carries a
fractional family with `|S w|` atoms per configuration (`(|S w| - 1) + 1`) and loads at most `1`,
then `∑ (|S w| - 1) ≤ gates.length - 1`. -/
theorem lift_frac_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
    (hf : MonoFrac (N := n + 1) (lift n p gates) (fun w => (S w).card - 1)
      (fun w => liftWire n p (out w))) :
    ∑ w, ((S w).card - 1) ≤ gates.length - 1 := by
  have h := mono_frac_bound (lift n p gates) (lift_ops gates p hp hg hU hN) _ _ hf
  rwa [length_lift n p gates hp] at h

/-! ## (3) `LiftClassFrac` -/

/-- **LiftClassFrac**: the circuit has a NOT gate (position `p`) whose lifted circuit carries a
fractional family of S2.1 configurations (`|S w|` atoms each) with all gate loads at most `1`. -/
def LiftClassFrac {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) :
    Prop :=
  ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
    MonoFrac (N := n + 1) (lift n p gates) (fun w => (S w).card - 1)
      (fun w => liftWire n p (out w))

theorem bound_of_liftClassFrac {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hf : LiftClassFrac S gates out) :
    ∑ w, ((S w).card - 1) ≤ gates.length - 1 := by
  obtain ⟨p, hp, hN, hf⟩ := hf
  exact lift_frac_bound S gates out p hp hg hU hN hf

/-- A circuit with a `LiftClassFrac` family is not a counterexample. -/
theorem not_isCE_of_liftClassFrac {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (hf : LiftClassFrac S gates out) : ¬ IsCE S gates out := by
  intro C
  have := bound_of_liftClassFrac S gates out C.hg C.hU hf
  have := C.hlt
  omega

/-- **`LiftClassFrac` on minimal counterexamples closes 951.** -/
theorem no_minCE_of_liftClassFrac
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → LiftClassFrac S gates out) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  fun {n m} S gates out M => not_isCE_of_liftClassFrac S gates out (H n m S gates out M) M.ce

/-- A minimal counterexample (any counterexample) has a NOT gate (`bound_of_noNot`). -/
theorem IsCE.exists_not {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate}
    {out : Fin m → ℕ} (C : IsCE S gates out) :
    ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not := by
  by_contra hno
  have hno' : ∀ g ∈ gates, g.op ≠ GateOp.not := by
    intro g hgm hop
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hgm
    exact hno ⟨p, hp, hop⟩
  have := bound_of_noNot S C.hS gates out C.hg hno' C.hev
  have := C.hlt
  omega

theorem MinCE.exists_not {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate}
    {out : Fin m → ℕ} (M : MinCE S gates out) :
    ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not := M.ce.exists_not

/-- An integral family with pairwise disjoint classes is a fractional family (one configuration
per output, weight `1`). -/
theorem monoFrac_of_disjoint {N m : ℕ} (gs : List Gate) (d : Fin m → ℕ) (o : Fin m → ℕ)
    (Z : Fin m → Finset (Fin N → Bool)) (a : ∀ w : Fin m, Fin (d w + 1) → Fin N → Bool)
    (hZ : ∀ w, (Z w).Nonempty) (hjoin : ∀ w, ∀ x ∈ Z w, ∀ y ∈ Z w, x ⊔ y ∈ Z w)
    (hL : ∀ w, ∀ c : Fin N, (∀ x ∈ Z w, x c = false) →
      ∀ s t, a w s c = true → a w t c = true → s = t)
    (hZo : ∀ w, ∀ x ∈ Z w, val gs x (o w) = false)
    (hao : ∀ w, ∀ t, val gs (a w t) (o w) = true)
    (hdis : ∀ u v : Fin m, u ≠ v →
      Disjoint (liftClOr gs (Z u) (a u)) (liftClOr gs (Z v) (a v))) :
    MonoFrac (N := N) gs d o := by
  refine ⟨fun _ => 1, fun w _ => Z w, fun w _ => a w, fun _ _ => 1, fun _ _ => zero_le_one,
    fun _ => by simp, fun w _ => hZ w, fun w _ => hjoin w, fun w _ => hL w, fun w _ => hZo w,
    fun w _ => hao w, fun g => ?_⟩
  simp only [Fin.sum_univ_one]
  by_cases hex : ∃ u, g ∈ liftClOr gs (Z u) (a u)
  · obtain ⟨u, hu⟩ := hex
    rw [Finset.sum_eq_single u]
    · simp [hu]
    · intro v _ hvu
      rw [ite_eq_right]
      exact fun hv => Finset.disjoint_left.mp (hdis u v (Ne.symm hvu)) hu hv
    · simp
  · push Not at hex
    rw [Finset.sum_eq_zero]
    · exact zero_le_one
    · intro v _
      rw [ite_eq_right (hex v)]

/-- A pairwise blocked integral family is a fractional family (`liftClOr_disjoint`). -/
theorem monoFrac_of_blocked {N m : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (d : Fin m → ℕ) (o : Fin m → ℕ)
    (Z : Fin m → Finset (Fin N → Bool)) (a : ∀ w : Fin m, Fin (d w + 1) → Fin N → Bool)
    (hZ : ∀ w, (Z w).Nonempty) (hjoin : ∀ w, ∀ x ∈ Z w, ∀ y ∈ Z w, x ⊔ y ∈ Z w)
    (hL : ∀ w, ∀ c : Fin N, (∀ x ∈ Z w, x c = false) →
      ∀ s t, a w s c = true → a w t c = true → s = t)
    (hZo : ∀ w, ∀ x ∈ Z w, val gs x (o w) = false)
    (hao : ∀ w, ∀ t, val gs (a w t) (o w) = true)
    (hblock : ∀ u v : Fin m, u ≠ v →
      (blockP (Z v) (a u)).card ≤ 1 ∨ (blockP (Z u) (a v)).card ≤ 1) :
    MonoFrac (N := N) gs d o :=
  monoFrac_of_disjoint gs d o Z a hZ hjoin hL hZo hao fun u v huv =>
    liftClOr_disjoint gs hg (Z u) (Z v) (a u) (a v) (hblock u v huv)

end PEqualNP.Outside.L_meta_951_aux
