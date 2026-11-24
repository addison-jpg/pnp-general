import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PureSDR
import PEqualNP.W951.MergeFrac

/-!
# PureHall: PureSDR and Hall's condition on the pure menus

For the official target PureSDR (`PureSDR.lean`; owner 10:47). The PURE MENU of a set `R` is the
union of the classes of all its valid pure options (`pureMenu`). Results:

* `card_pureCls_eq`: every valid pure class has EXACTLY `|R| - 1` merges (`card_pureCls` and the
  run's upper count `runMT_card_le`).
* `hall_of_pureSDR` (any system, necessary condition): a PureSDR gives, for every family `F` of
  sets, `∑_{w ∈ F} (|S_w| - 1) ≤ |⋃_{w ∈ F} menu(w)|`.
* `pureSDR_of_hall_singleton`: if every valid class has at most one gate, Hall's condition on the
  menus gives a PureSDR (Mathlib's Hall theorem, `Finset.all_card_le_biUnion_card_iff_exists_injective`).
* `pureSDR_iff_hall` (GRAPH systems, all `|S_w| = 2`): each pure class is one gate, and
  PureSDR ⇔ Hall's condition `|F| ≤ |⋃_{w ∈ F} menu(w)|` for every family `F` of sets.
* `no_graph_minCE_of_hall`: if Hall's condition holds on the pure menus of every minimal
  counterexample that is a graph system, no minimal counterexample is a graph system (front's
  lane, 11:32: Hall via heredity).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section PureHall

variable {n : ℕ}

open Classical in
/-- **The pure menu** of `R`: the union of the classes of all valid pure options (lifted wires). -/
noncomputable def pureMenu (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) : Finset ℕ :=
  ((Finset.univ : Finset (Fin n → Bool)).filter fun Z => PureValid gates p R (.one Z)).biUnion
      (fun Z => pureI1 gates p R Z) ∪
    ((Finset.univ : Finset (Fin n → Finset (Fin n))).filter
      fun m => PureValid gates p R (.zero m)).biUnion fun m => pureI0 gates p R m

theorem mem_pureMenu {gates : List Gate} {p : ℕ} {R : Finset (Fin n)} {g : ℕ} :
    g ∈ pureMenu gates p R ↔ ∃ c, PureValid gates p R c ∧ g ∈ pureCls gates p R c := by
  classical
  constructor
  · intro h
    rw [pureMenu, Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion] at h
    rcases h with ⟨Z, hZ, hg⟩ | ⟨m, hm, hg⟩
    · exact ⟨.one Z, (Finset.mem_filter.mp hZ).2, hg⟩
    · exact ⟨.zero m, (Finset.mem_filter.mp hm).2, hg⟩
  · rintro ⟨c, hc, hg⟩
    rw [pureMenu, Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
    cases c with
    | one Z => exact Or.inl ⟨Z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, hg⟩
    | zero m => exact Or.inr ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, hg⟩

theorem pureCls_subset_menu {gates : List Gate} {p : ℕ} {R : Finset (Fin n)} {c : PureOpt n}
    (hc : PureValid gates p R c) : pureCls gates p R c ⊆ pureMenu gates p R :=
  fun _ hg => mem_pureMenu.mpr ⟨c, hc, hg⟩

/-- Upper count: a pure class has at most `|R| - 1` merges (no hypothesis). -/
theorem card_pureCls_le (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) (c : PureOpt n) :
    (pureCls gates p R c).card ≤ R.card - 1 := by
  cases c with
  | one Z =>
    have := runMT_card_le (ext Z true) atom1 (liftSet R) (lift n p gates) (lift n p gates).length
    rwa [card_liftSet] at this
  | zero m =>
    have := runMT_card_le (ext (Zof R) false) (atom0 m) (liftSet R) (lift n p gates)
      (lift n p gates).length
    rwa [card_liftSet] at this

/-! ## Hall's condition -/

/-- **Necessary condition (any system).** A PureSDR gives `∑_{w ∈ F} (|S_w| - 1) ≤ |⋃_{w ∈ F}
menu(w)|` for every family `F`. -/
theorem hall_of_pureSDR {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ)
    (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (H : PureSDR S gates p) (F : Finset (Fin m)) :
    ∑ w ∈ F, ((S w).card - 1) ≤ (F.biUnion fun w => pureMenu gates p (S w)).card := by
  classical
  obtain ⟨c, hc, hdis⟩ := H
  have hpd : (F : Set (Fin m)).PairwiseDisjoint fun w => pureCls gates p (S w) (c w) :=
    fun w _ w' _ hww => hdis w w' hww
  calc ∑ w ∈ F, ((S w).card - 1)
      ≤ ∑ w ∈ F, (pureCls gates p (S w) (c w)).card :=
        Finset.sum_le_sum fun w _ => card_pureCls gates p hp hg hU hN (S w) (c w) (hc w) (out w) (hev w)
    _ = (F.biUnion fun w => pureCls gates p (S w) (c w)).card := (Finset.card_biUnion hpd).symm
    _ ≤ (F.biUnion fun w => pureMenu gates p (S w)).card :=
        Finset.card_le_card (Finset.biUnion_mono fun w _ => pureCls_subset_menu (hc w))

/-- **Hall ⇒ PureSDR when classes are single gates.** -/
theorem pureSDR_of_hall_singleton {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (p : ℕ) (hsing : ∀ w c, PureValid gates p (S w) c → (pureCls gates p (S w) c).card ≤ 1)
    (hall : ∀ F : Finset (Fin m), F.card ≤ (F.biUnion fun w => pureMenu gates p (S w)).card) :
    PureSDR S gates p := by
  classical
  obtain ⟨f, hf, hfm⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective fun w => pureMenu gates p (S w)).mp hall
  choose c hc hfc using fun w => mem_pureMenu.mp (hfm w)
  have hsg : ∀ w, pureCls gates p (S w) (c w) = {f w} := fun w =>
    (Finset.eq_singleton_iff_unique_mem.mpr ⟨hfc w, fun x hx =>
      Finset.card_le_one.mp (hsing w (c w) (hc w)) x hx (f w) (hfc w)⟩)
  refine ⟨c, hc, fun w w' hww => ?_⟩
  rw [hsg w, hsg w', Finset.disjoint_singleton]
  exact fun h => hww (hf h)

/-- **Graph systems: PureSDR ⇔ Hall.** If every set has two points, every valid pure class is
exactly one gate, and a PureSDR exists iff `|F| ≤ |⋃_{w ∈ F} menu(w)|` for every family `F`. -/
theorem pureSDR_iff_hall {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ)
    (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (h2 : ∀ w, (S w).card = 2) :
    PureSDR S gates p ↔
      ∀ F : Finset (Fin m), F.card ≤ (F.biUnion fun w => pureMenu gates p (S w)).card := by
  constructor
  · intro H F
    have := hall_of_pureSDR S gates p hp hg hU hN out hev H F
    simp only [h2] at this
    simpa using this
  · intro hall
    refine pureSDR_of_hall_singleton S gates p (fun w c _ => ?_) hall
    have := card_pureCls_le gates p (S w) c
    rw [h2 w] at this
    exact this

/-- On a graph system every valid pure class is exactly one gate. -/
theorem card_pureCls_graph (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (R : Finset (Fin n))
    (hR : R.card = 2) (c : PureOpt n) (hc : PureValid gates p R c) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true)) :
    (pureCls gates p R c).card = 1 := by
  have h1 := card_pureCls gates p hp hg hU hN R c hc o hev
  have h2 := card_pureCls_le gates p R c
  rw [hR] at h1 h2
  omega

end PureHall

/-- **951 on graph systems from Hall** (front's lane): if Hall's condition holds on the pure menus
of every minimal counterexample whose sets all have two points (for its NOT gate), then no minimal
counterexample is a graph system. -/
theorem no_graph_minCE_of_hall
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → (∀ w, (S w).card = 2) →
        ∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not →
          ∀ F : Finset (Fin m), F.card ≤ (F.biUnion fun w => pureMenu gates p (S w)).card) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ¬ ∀ w, (S w).card = 2 := by
  intro n m S gates out M h2
  obtain ⟨p, hp, hN⟩ := M.exists_not
  have hP := (pureSDR_iff_hall S gates p hp M.ce.hg M.ce.hU hN out M.ce.hev h2).mpr
    (H n m S gates out M h2 p hp hN)
  have h1 := bound_of_pureSDR gates p hp M.ce.hg M.ce.hU hN S out M.ce.hev hP
  have h3 := M.ce.hlt
  omega

end PEqualNP.Outside.L_meta_951_aux
