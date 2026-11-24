import Mathlib
import PEqualNP.Defs
import PEqualNP.Base.Matching.Duality
import PEqualNP.W951.PureHeredity

/-!
# PureFrac: fractional pure classes, their price form, and MU (coord item 3, 12:07; front A1's target)

For a one-NOT circuit (NOT gate at `p`) and sets `S`:

* `validCls gates p R`: the finset of the classes of all valid pure options of `R` (all four kinds);
  never empty (`validCls_nonempty`: `one 0` if the NOT gate is `1` at `0`, else `zero ∅`).
* `PureFrac S gates p`: for every set a convex combination of its valid classes, every gate with load
  at most `1`.
* `PurePrice S gates p`: `∀ π ≥ 0, ∑_w min_{C valid for w} π(C) ≤ π(⋃_w menu(w))`.
* `pureFrac_iff_purePrice`: LP duality (`exists_frac_iff_prices`, with the items the gates of the
  menu union).
* `mu_of_purePrice` (the price `π = 1`), `mu_of_pureFrac`, `pureFrac_of_pureSDR`,
  `no_minCE_of_purePrice`, `no_minCE_of_pureFrac`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Base.Matching

section PureFrac

variable {n m : ℕ}

open Classical in
/-- The classes of all valid pure options of `R`. -/
noncomputable def validCls (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) : Finset (Finset ℕ) :=
  (Finset.univ.filter fun s => PureValid gates p R (optOfSum s)).image
    fun s => pureCls gates p R (optOfSum s)

theorem mem_validCls {gates : List Gate} {p : ℕ} {R : Finset (Fin n)} {C : Finset ℕ} :
    C ∈ validCls gates p R ↔ ∃ c, PureValid gates p R c ∧ pureCls gates p R c = C := by
  classical
  rw [validCls, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨optOfSum s, (Finset.mem_filter.mp hs).2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨s, rfl⟩ := optOfSum_surj c
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, rfl⟩

theorem validCls_nonempty (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) :
    (validCls gates p R).Nonempty := by
  have h0 : canonPt (∅ : Finset (Fin n)) = fun _ => false := by
    funext c; simp [canonPt]
  cases h : val gates (fun _ => false) (n + p) with
  | true =>
    exact ⟨_, mem_validCls.mpr ⟨.one fun _ => false, ⟨fun _ _ => rfl, h⟩, rfl⟩⟩
  | false =>
    refine ⟨_, mem_validCls.mpr ⟨.zero fun _ => ∅, ⟨fun _ _ v hv => absurd hv (Finset.notMem_empty v),
      fun _ _ => ?_⟩, rfl⟩⟩
    rw [h0]; exact h

/-- The union of all menus (the items of the duality). -/
noncomputable def menuU (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun w => pureMenu gates p (S w)

theorem validCls_subset_menuU {S : Fin m → Finset (Fin n)} {gates : List Gate} {p : ℕ} {w : Fin m}
    {C : Finset ℕ} (hC : C ∈ validCls gates p (S w)) : C ⊆ menuU S gates p := by
  obtain ⟨c, hc, rfl⟩ := mem_validCls.mp hC
  exact (pureCls_subset_menu hc).trans
    (Finset.subset_biUnion_of_mem (fun w => pureMenu gates p (S w)) (Finset.mem_univ w))

/-- **PureFrac**: a convex combination of valid classes per set, every gate with load `≤ 1`. -/
def PureFrac (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ) : Prop :=
  ∃ μ : Fin m → Finset ℕ → ℝ,
    (∀ w C, 0 ≤ μ w C) ∧ (∀ w C, C ∉ validCls gates p (S w) → μ w C = 0) ∧
    (∀ w, ∑ C ∈ validCls gates p (S w), μ w C = 1) ∧
    ∀ g : ℕ, ∑ w, ∑ C ∈ validCls gates p (S w), μ w C * (if g ∈ C then 1 else 0) ≤ 1

/-- **PurePrice**, the LP dual: `∀ π ≥ 0, ∑_w min_{C valid} π(C) ≤ π(⋃ menus)`. -/
def PurePrice (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ) : Prop :=
  ∀ π : ℕ → ℝ, (∀ g, 0 ≤ π g) →
    ∑ w, (validCls gates p (S w)).inf' (validCls_nonempty gates p (S w)) (fun C => ∑ g ∈ C, π g)
      ≤ ∑ g ∈ menuU S gates p, π g

/-! ## The translation to items of the menu union -/

variable (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ)

/-- A class as a finset of items of the menu union. -/
noncomputable def toSub (C : Finset ℕ) : Finset (menuU S gates p) := C.subtype (· ∈ menuU S gates p)

/-- The options of the duality: the valid classes as item sets. -/
noncomputable def optU (w : Fin m) : Finset (Finset (menuU S gates p)) :=
  (validCls gates p (S w)).image (toSub S gates p)

theorem mem_toSub {C : Finset ℕ} {a : menuU S gates p} : a ∈ toSub S gates p C ↔ (a : ℕ) ∈ C :=
  Finset.mem_subtype

theorem toSub_injOn (w : Fin m) : Set.InjOn (toSub S gates p) (validCls gates p (S w) : Set (Finset ℕ)) := by
  intro C hC C' hC' h
  ext g
  constructor
  · intro hg
    have := (mem_toSub S gates p (a := ⟨g, validCls_subset_menuU hC hg⟩)).mpr hg
    rw [h] at this
    exact (mem_toSub S gates p).mp this
  · intro hg
    have := (mem_toSub S gates p (a := ⟨g, validCls_subset_menuU hC' hg⟩)).mpr hg
    rw [← h] at this
    exact (mem_toSub S gates p).mp this

theorem sum_toSub (w : Fin m) {C : Finset ℕ} (hC : C ∈ validCls gates p (S w)) (π : ℕ → ℝ) :
    ∑ a ∈ toSub S gates p C, π a = ∑ g ∈ C, π g := by
  rw [toSub, Finset.sum_subtype_eq_sum_filter (fun g => π g),
    Finset.filter_true_of_mem fun g hg => validCls_subset_menuU hC hg]

theorem optU_nonempty (w : Fin m) : (optU S gates p w).Nonempty :=
  (validCls_nonempty gates p (S w)).image _

/-- **PureFrac ⇔ a fractional choice on the item options.** -/
theorem pureFrac_iff_frac :
    PureFrac S gates p ↔ ∃ lam : Fin m → Finset (menuU S gates p) → ℝ,
      IsFracChoice (optU S gates p) lam ∧ ∀ a, load (optU S gates p) lam a ≤ 1 := by
  classical
  constructor
  · rintro ⟨μ, h0, hsupp, h1, hl⟩
    refine ⟨fun w M => ∑ C ∈ (validCls gates p (S w)).filter (fun C => toSub S gates p C = M), μ w C,
      ⟨fun w M => Finset.sum_nonneg fun C _ => h0 w C, fun w M hM => ?_, fun w => ?_⟩, fun a => ?_⟩
    · refine Finset.sum_eq_zero fun C hC => ?_
      obtain ⟨hCv, rfl⟩ := Finset.mem_filter.mp hC
      exact absurd (Finset.mem_image_of_mem _ hCv) hM
    · rw [optU, Finset.sum_fiberwise_of_maps_to fun C hC => Finset.mem_image_of_mem _ hC]
      exact h1 w
    · refine le_of_eq_of_le ?_ (hl a)
      unfold load
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [Finset.sum_mul]
      have hfib : ∀ M ∈ optU S gates p w, ∑ C ∈ (validCls gates p (S w)).filter
          (fun C => toSub S gates p C = M), μ w C * (if a ∈ M then 1 else 0) =
          ∑ C ∈ (validCls gates p (S w)).filter (fun C => toSub S gates p C = M),
            μ w C * (if a ∈ toSub S gates p C then 1 else 0) := fun M _ =>
        Finset.sum_congr rfl fun C hC => by rw [(Finset.mem_filter.mp hC).2]
      rw [Finset.sum_congr rfl hfib, optU, Finset.sum_fiberwise_of_maps_to
        (fun C hC => Finset.mem_image_of_mem (toSub S gates p) hC)
        (fun C => μ w C * if a ∈ toSub S gates p C then 1 else 0)]
      refine Finset.sum_congr rfl fun C _ => ?_
      simp only [mem_toSub]
  · rintro ⟨lam, ⟨h0, hsupp, h1⟩, hl⟩
    refine ⟨fun w C => if C ∈ validCls gates p (S w) then lam w (toSub S gates p C) else 0,
      fun w C => ?_, fun w C hC => by simp [hC], fun w => ?_, fun g => ?_⟩
    · dsimp only
      split_ifs
      · exact h0 w _
      · exact le_rfl
    · dsimp only
      rw [Finset.sum_ite_of_true fun C hC => hC, ← h1 w, optU,
        Finset.sum_image (toSub_injOn S gates p w)]
    · by_cases hg : g ∈ menuU S gates p
      · refine le_of_eq_of_le ?_ (hl ⟨g, hg⟩)
        unfold load
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [optU, Finset.sum_image (toSub_injOn S gates p w)]
        refine Finset.sum_congr rfl fun C hC => ?_
        dsimp only
        rw [ite_eq_left hC]
        simp only [mem_toSub]
      · refine le_of_eq_of_le (Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun C hC => ?_) zero_le_one
        rw [ite_eq_right (show ¬ g ∈ C from fun h => hg (validCls_subset_menuU hC h)), mul_zero]

/-- **PurePrice ⇔ the price form on the item options.** -/
theorem purePrice_iff_prices :
    PurePrice S gates p ↔ ∀ π : menuU S gates p → ℝ, (∀ a, 0 ≤ π a) →
      ∑ w, (optU S gates p w).inf' (optU_nonempty S gates p w) (fun M => ∑ a ∈ M, π a) ≤ ∑ a, π a := by
  classical
  have hinf : ∀ (π : ℕ → ℝ) (w : Fin m),
      (optU S gates p w).inf' (optU_nonempty S gates p w) (fun M => ∑ a ∈ M, π a) =
        (validCls gates p (S w)).inf' (validCls_nonempty gates p (S w)) (fun C => ∑ g ∈ C, π g) := by
    intro π w
    refine le_antisymm (Finset.le_inf' _ _ fun C hC => ?_) (Finset.le_inf' _ _ fun M hM => ?_)
    · rw [← sum_toSub S gates p w hC π]
      exact Finset.inf'_le _ (Finset.mem_image_of_mem _ hC)
    · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hM
      rw [sum_toSub S gates p w hC π]
      exact Finset.inf'_le _ hC
  constructor
  · intro H π hπ
    let π' : ℕ → ℝ := fun g => if h : g ∈ menuU S gates p then π ⟨g, h⟩ else 0
    have hπ' : ∀ g, 0 ≤ π' g := fun g => by
      simp only [π']; split_ifs
      · exact hπ _
      · exact le_rfl
    have hsub : ∀ M : Finset (menuU S gates p), ∑ a ∈ M, π' a = ∑ a ∈ M, π a := fun M =>
      Finset.sum_congr rfl fun a _ => by simp [π', a.2]
    have key := H π' hπ'
    have hl : ∑ w, (optU S gates p w).inf' (optU_nonempty S gates p w) (fun M => ∑ a ∈ M, π a) =
        ∑ w, (validCls gates p (S w)).inf' (validCls_nonempty gates p (S w)) (fun C => ∑ g ∈ C, π' g) := by
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← hinf π' w]
      exact Finset.inf'_congr _ rfl fun M _ => (hsub M).symm
    have hr : ∑ g ∈ menuU S gates p, π' g = ∑ a, π a := by
      rw [← Finset.sum_attach]
      exact Finset.sum_congr rfl fun a _ => by simp [π', a.2]
    rw [hl]; rw [hr] at key; exact key
  · intro H π hπ
    have key := H (fun a => π a) fun a => hπ a
    have hl : ∑ w, (optU S gates p w).inf' (optU_nonempty S gates p w) (fun M => ∑ a ∈ M, π a) =
        ∑ w, (validCls gates p (S w)).inf' (validCls_nonempty gates p (S w)) (fun C => ∑ g ∈ C, π g) :=
      Finset.sum_congr rfl fun w _ => hinf π w
    have hr : ∑ a : menuU S gates p, π a = ∑ g ∈ menuU S gates p, π g := by
      rw [← Finset.sum_attach (menuU S gates p)]
      rfl
    rw [hl, hr] at key
    exact key

/-- **LP duality: PureFrac ⇔ PurePrice.** -/
theorem pureFrac_iff_purePrice : PureFrac S gates p ↔ PurePrice S gates p := by
  rw [pureFrac_iff_frac, purePrice_iff_prices]
  exact exists_frac_iff_prices (optU S gates p) (optU_nonempty S gates p)

/-! ## MU from the price form -/

variable (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **PurePrice ⇒ MU** (the constant price `1`: every valid class has at least `d_w` gates). -/
theorem mu_of_purePrice (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (H : PurePrice S gates p) : MU S gates p := by
  have key := H (fun _ => 1) fun _ => zero_le_one
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at key
  have hle : ∀ w, (((S w).card - 1 : ℕ) : ℝ) ≤
      (validCls gates p (S w)).inf' (validCls_nonempty gates p (S w)) (fun C => (C.card : ℝ)) := by
    intro w
    refine Finset.le_inf' _ _ fun C hC => ?_
    obtain ⟨c, hc, rfl⟩ := mem_validCls.mp hC
    exact_mod_cast card_pureCls gates p hp hg hU hN (S w) c hc (out w) (hev w)
  have h2 : ((∑ w, ((S w).card - 1) : ℕ) : ℝ) ≤ ((menuU S gates p).card : ℝ) := by
    push_cast
    exact (Finset.sum_le_sum fun w _ => hle w).trans key
  exact_mod_cast h2

include hg hU hN in
theorem mu_of_pureFrac (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (H : PureFrac S gates p) : MU S gates p :=
  mu_of_purePrice S gates p hp hg hU hN out hev ((pureFrac_iff_purePrice S gates p).mp H)

/-- **PureSDR ⇒ PureFrac** (weight `1` on the chosen class). -/
theorem pureFrac_of_pureSDR (H : PureSDR S gates p) : PureFrac S gates p := by
  classical
  obtain ⟨c, hc, hdis⟩ := H
  have hmem : ∀ w, pureCls gates p (S w) (c w) ∈ validCls gates p (S w) := fun w =>
    mem_validCls.mpr ⟨c w, hc w, rfl⟩
  refine ⟨fun w C => if C = pureCls gates p (S w) (c w) then 1 else 0,
    fun w C => by dsimp only; split_ifs <;> norm_num,
    fun w C hC => by dsimp only; rw [ite_eq_right fun h => hC (by rw [h]; exact hmem w)], fun w => ?_, fun g => ?_⟩
  · dsimp only
    rw [Finset.sum_ite_eq' _ _ (fun _ => (1 : ℝ)), ite_eq_left (hmem w)]
  · have hterm : ∀ w, ∑ C ∈ validCls gates p (S w),
        (if C = pureCls gates p (S w) (c w) then (1 : ℝ) else 0) * (if g ∈ C then 1 else 0) =
          if g ∈ pureCls gates p (S w) (c w) then 1 else 0 := by
      intro w
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' _ _ (fun C => if g ∈ C then (1 : ℝ) else 0), ite_eq_left (hmem w)]
    simp only [hterm]
    by_cases hex : ∃ w, g ∈ pureCls gates p (S w) (c w)
    · obtain ⟨w0, hw0⟩ := hex
      rw [Finset.sum_eq_single w0 (fun w _ hw => ite_eq_right fun h =>
        Finset.disjoint_left.mp (hdis w w0 hw) h hw0) (by simp), ite_eq_left hw0]
    · push Not at hex
      rw [Finset.sum_eq_zero fun w _ => ite_eq_right (hex w)]
      exact zero_le_one

end PureFrac

/-- **951 from PurePrice** (front A1's target): if every minimal counterexample has a NOT gate whose
pure price form holds, there is no minimal counterexample. -/
theorem no_minCE_of_purePrice
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out →
        ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧ PurePrice S gates p) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_MU fun n m S gates out M => by
    obtain ⟨p, hp, hN, hP⟩ := H n m S gates out M
    exact ⟨p, hp, hN, mu_of_purePrice S gates p hp M.ce.hg M.ce.hU hN out M.ce.hev hP⟩

/-- **951 from PureFrac.** -/
theorem no_minCE_of_pureFrac
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out →
        ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧ PureFrac S gates p) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_purePrice fun n m S gates out M => by
    obtain ⟨p, hp, hN, hP⟩ := H n m S gates out M
    exact ⟨p, hp, hN, (pureFrac_iff_purePrice S gates p).mp hP⟩

end PEqualNP.Outside.L_meta_951_aux
