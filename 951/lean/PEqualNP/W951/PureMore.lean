import Mathlib
import PEqualNP.Defs
import PEqualNP.Base.Matching.Duality
import PEqualNP.W951.PureHeredity
import PEqualNP.W951.PureStar
import PEqualNP.W951.PureLLift
import PEqualNP.W951.RunTransfer
import PEqualNP.Kernel.W951CubeKeep
import PEqualNP.W951.PureGP

section PureFrac

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

end PureFrac

section PureMenu

/-!
# PureMenu: STAR-SEP / STAR-COUNT over any monotone menu system; Menu2 (front A2, 12:16)

The induction of `PureStar.lean` only uses that the menus shrink as `Q` grows and that every class
is a set of at least `d_w` lifted gates. Here it is stated for an arbitrary MENU SYSTEM
`Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ)` (the classes of set `w` allowed at `Q`):

* `StarSepG`, `MenuSDRG`, `menuSDRG_of_starSepG` (STAR-SEP at every `Q` ⇒ an SDR at every `Q`),
  `UQG`, `StarCountG`, `sum_alive_le_UQG` (STAR-COUNT at every `Q` ⇒ `∑_{alive} d_w ≤ |U(Q)|`),
  assuming only `MenuMono Mn` (`Mn (insert v Q) w ⊆ Mn Q w`);
* `MenuSound gates p S Mn`: every class of `Mn ∅ w` has `≥ d_w` gates, all among the
  `gates.length - 1` lifted gates; then `bound_of_menuSDRG`, `bound_of_starCountG` and
  `no_minCE_of_starSepG`, `no_minCE_of_starCountG`.
* **Menu2** (`menu2`): Menu1 (`InMenuQ`) ∪ the real merge sets `M_z(w)` as lifted classes
  (`realLTS`, PureLLift: zero point `(z, ν z)`, atoms `(z + e_u, ν(z + e_u))`) with `Q ⊆ z`,
  `z ∩ S_w = ∅`. `menu2_mono`, `menu2_sound`, `no_minCE_of_starSep2`, `no_minCE_of_starCount2`.
  (`starSep_heavy` stays a Menu1 lemma.)
* L-U_v (front A2): `ltsCls_zero`, `menu2_U_zero` (every gate of `U(Q)` is `0` at `(Q, 0)`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section PureMenu

variable {n m : ℕ}

/-- The menus shrink as `Q` grows. -/
def MenuMono (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ)) : Prop :=
  ∀ Q v w, Mn (insert v Q) w ⊆ Mn Q w

/-- STAR-SEP over a menu system. -/
def StarSepG (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (Q : Finset (Fin n)) : Prop :=
  (aliveSets S Q).Nonempty → ∃ v : Fin n, (starSets S Q v).Nonempty ∧ ∃ K : Fin m → Finset ℕ,
    (∀ w ∈ starSets S Q v, K w ∈ Mn Q w) ∧
    (∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → Disjoint (K w) (K w')) ∧
    ∀ w ∈ starSets S Q v, ∀ w' ∈ aliveSets S Q, v ∉ S w' → ∀ C' ∈ Mn (insert v Q) w', Disjoint (K w) C'

/-- An SDR of the alive sets from the menus at `Q`. -/
def MenuSDRG (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (Q : Finset (Fin n)) : Prop :=
  ∃ K : Fin m → Finset ℕ, (∀ w ∈ aliveSets S Q, K w ∈ Mn Q w) ∧
    ∀ w ∈ aliveSets S Q, ∀ w' ∈ aliveSets S Q, w ≠ w' → Disjoint (K w) (K w')

/-- **STAR-SEP ⇒ SDR**, for any monotone menu system. -/
theorem menuSDRG_of_starSepG (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (hmono : MenuMono Mn) (H : ∀ Q, StarSepG S Mn Q) :
    ∀ k (Q : Finset (Fin n)), (aliveSets S Q).card ≤ k → MenuSDRG S Mn Q := by
  classical
  have hempty : ∀ Q, aliveSets S Q = ∅ → MenuSDRG S Mn Q := fun Q h =>
    ⟨fun _ => ∅, fun w hw => by simp [h] at hw, fun w hw => by simp [h] at hw⟩
  intro k
  induction k with
  | zero => intro Q hQ; exact hempty Q (Finset.card_eq_zero.mp (Nat.le_zero.mp hQ))
  | succ k ih =>
    intro Q hQ
    rcases (aliveSets S Q).eq_empty_or_nonempty with h0 | hne
    · exact hempty Q h0
    obtain ⟨v, ⟨w0, hw0⟩, K, hK, hKK, hKo⟩ := H Q hne
    have hw0' := Finset.mem_filter.mp hw0
    have hlt : (aliveSets S (insert v Q)).card < (aliveSets S Q).card := by
      refine Finset.card_lt_card ⟨fun w hw => ((aliveSets_insert S Q v w).mp hw).1, fun hsub => ?_⟩
      exact ((aliveSets_insert S Q v w0).mp (hsub hw0'.1)).2 hw0'.2
    obtain ⟨K', hK'm, hK'd⟩ := ih (insert v Q) (by omega)
    have hstar : ∀ w, w ∈ starSets S Q v ↔ w ∈ aliveSets S Q ∧ v ∈ S w := fun w => Finset.mem_filter
    have hout : ∀ w, w ∈ aliveSets S Q → v ∉ S w → w ∈ aliveSets S (insert v Q) := fun w hw hv =>
      (aliveSets_insert S Q v w).mpr ⟨hw, hv⟩
    refine ⟨fun w => if v ∈ S w then K w else K' w, fun w hw => ?_, fun w hw w' hw' hww => ?_⟩
    · by_cases hv : v ∈ S w
      · simp only [hv, ite_true]; exact hK w ((hstar w).mpr ⟨hw, hv⟩)
      · simp only [hv, ite_false]; exact hmono Q v w (hK'm w (hout w hw hv))
    · by_cases hv : v ∈ S w <;> by_cases hv' : v ∈ S w' <;> simp only [hv, hv', ite_true, ite_false]
      · exact hKK w ((hstar w).mpr ⟨hw, hv⟩) w' ((hstar w').mpr ⟨hw', hv'⟩) hww
      · exact hKo w ((hstar w).mpr ⟨hw, hv⟩) w' hw' hv' (K' w') (hK'm w' (hout w' hw' hv'))
      · exact (hKo w' ((hstar w').mpr ⟨hw', hv'⟩) w hw hv (K' w) (hK'm w (hout w hw hv))).symm
      · exact hK'd w (hout w hw hv) w' (hout w' hw' hv') hww

/-- `U(Q)` for a menu system. -/
def UQG (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (Q : Finset (Fin n)) : Finset ℕ :=
  (aliveSets S Q).biUnion fun w => (Mn Q w).biUnion id

theorem UQG_insert_subset (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (hmono : MenuMono Mn) (Q : Finset (Fin n)) (v : Fin n) : UQG S Mn (insert v Q) ⊆ UQG S Mn Q := by
  intro g hg
  simp only [UQG, Finset.mem_biUnion, id] at hg ⊢
  obtain ⟨w, hw, C, hC, hgC⟩ := hg
  exact ⟨w, ((aliveSets_insert S Q v w).mp hw).1, C, hmono Q v w hC, hgC⟩

/-- STAR-COUNT over a menu system. -/
def StarCountG (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (Q : Finset (Fin n)) (v : Fin n) : Prop :=
  ∑ w ∈ starSets S Q v, ((S w).card - 1) ≤ (UQG S Mn Q \ UQG S Mn (insert v Q)).card

/-- **STAR-COUNT ⇒ `∑_{alive} d_w ≤ |U(Q)|`**, for any monotone menu system. -/
theorem sum_alive_le_UQG (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (hmono : MenuMono Mn)
    (H : ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ StarCountG S Mn Q v) :
    ∀ k (Q : Finset (Fin n)), (aliveSets S Q).card ≤ k →
      ∑ w ∈ aliveSets S Q, ((S w).card - 1) ≤ (UQG S Mn Q).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro Q hQ
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hQ), Finset.sum_empty]
    exact Nat.zero_le _
  | succ k ih =>
    intro Q hQ
    rcases (aliveSets S Q).eq_empty_or_nonempty with h0 | hne
    · rw [h0, Finset.sum_empty]; exact Nat.zero_le _
    obtain ⟨v, ⟨w0, hw0⟩, hcount⟩ := H Q hne
    have hw0' := Finset.mem_filter.mp hw0
    have hsplit : (aliveSets S Q).filter (fun w => v ∉ S w) = aliveSets S (insert v Q) := by
      ext w
      rw [Finset.mem_filter, aliveSets_insert]
    have hlt : (aliveSets S (insert v Q)).card < (aliveSets S Q).card := by
      refine Finset.card_lt_card ⟨fun w hw => ((aliveSets_insert S Q v w).mp hw).1, fun hsub => ?_⟩
      exact ((aliveSets_insert S Q v w0).mp (hsub hw0'.1)).2 hw0'.2
    have hih := ih (insert v Q) (by omega)
    rw [← Finset.sum_filter_add_sum_filter_not (aliveSets S Q) (fun w => v ∈ S w), hsplit]
    have hcard := Finset.card_sdiff_add_card_eq_card (UQG_insert_subset S Mn hmono Q v)
    unfold StarCountG starSets at hcount
    omega

/-- Soundness of a menu system at `Q = ∅`: every class has at least `d_w` gates, all among the
lifted gates. -/
def MenuSound (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ)) : Prop :=
  ∀ w, ∀ C ∈ Mn ∅ w, (S w).card - 1 ≤ C.card ∧ C ⊆ Finset.Ico (n + 1) (n + 1 + (lift n p gates).length)

theorem aliveSets_empty (S : Fin m → Finset (Fin n)) : aliveSets S ∅ = Finset.univ := by
  ext w; simp [mem_aliveSets]

/-- **An SDR from a sound menu system ⇒ the bound with one gate to spare.** -/
theorem bound_of_menuSDRG (gates : List Gate) (p : ℕ) (hp : p < gates.length) (S : Fin m → Finset (Fin n))
    (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ)) (hs : MenuSound gates p S Mn)
    (H : MenuSDRG S Mn ∅) : ∑ w, ((S w).card - 1) ≤ gates.length - 1 := by
  classical
  obtain ⟨K, hK, hdis⟩ := H
  rw [aliveSets_empty] at hK hdis
  have hpd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint K :=
    fun w _ w' _ hww => hdis w (Finset.mem_univ _) w' (Finset.mem_univ _) hww
  calc ∑ w, ((S w).card - 1)
      ≤ ∑ w, (K w).card := Finset.sum_le_sum fun w _ => (hs w (K w) (hK w (Finset.mem_univ _))).1
    _ = (Finset.univ.biUnion K).card := (Finset.card_biUnion hpd).symm
    _ ≤ (Finset.Ico (n + 1) (n + 1 + (lift n p gates).length)).card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr fun w _ => (hs w (K w) (hK w (Finset.mem_univ _))).2)
    _ = gates.length - 1 := by rw [Nat.card_Ico, length_lift n p gates hp]; omega

/-- **STAR-COUNT for a sound monotone menu system ⇒ the bound with one gate to spare.** -/
theorem bound_of_starCountG (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (hmono : MenuMono Mn) (hs : MenuSound gates p S Mn)
    (H : ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ StarCountG S Mn Q v) :
    ∑ w, ((S w).card - 1) ≤ gates.length - 1 := by
  have h := sum_alive_le_UQG S Mn hmono H _ ∅ le_rfl
  rw [aliveSets_empty] at h
  have hsub : UQG S Mn ∅ ⊆ Finset.Ico (n + 1) (n + 1 + (lift n p gates).length) := by
    intro g hg
    simp only [UQG, Finset.mem_biUnion, id] at hg
    obtain ⟨w, -, C, hC, hgC⟩ := hg
    exact (hs w C hC).2 hgC
  have h2 := Finset.card_le_card hsub
  rw [Nat.card_Ico, length_lift n p gates hp] at h2
  omega

/-! ## Menu2 (front A2): Menu1 plus the real merge sets as lifted classes -/

open Classical in
/-- **Menu2_Q(w)**: the `Menu1_Q` classes (`InMenuQ`) and the lifted real merge sets
`ltsCls (realLTS z)` with `Q ⊆ z` and `z ∩ S_w = ∅`. -/
noncomputable def menu2 (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n))
    (w : Fin m) : Finset (Finset ℕ) :=
  ((Finset.univ.filter fun s => InMenuQ gates p Q (S w) (optOfSum s)).image
      fun s => pureCls gates p (S w) (optOfSum s)) ∪
    ((Finset.univ.filter fun z : Fin n → Bool => (∀ v ∈ Q, z v = true) ∧ ∀ v ∈ S w, z v = false).image
      fun z => ltsCls gates p (S w) (realLTS gates p z))

theorem mem_menu2 {gates : List Gate} {p : ℕ} {S : Fin m → Finset (Fin n)} {Q : Finset (Fin n)}
    {w : Fin m} {C : Finset ℕ} :
    C ∈ menu2 gates p S Q w ↔ (∃ c, InMenuQ gates p Q (S w) c ∧ pureCls gates p (S w) c = C) ∨
      ∃ z : Fin n → Bool, ((∀ v ∈ Q, z v = true) ∧ ∀ v ∈ S w, z v = false) ∧
        ltsCls gates p (S w) (realLTS gates p z) = C := by
  classical
  rw [menu2, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact Or.inl ⟨optOfSum s, (Finset.mem_filter.mp hs).2, rfl⟩
    · exact Or.inr ⟨z, (Finset.mem_filter.mp hz).2, rfl⟩
  · rintro (⟨c, hc, rfl⟩ | ⟨z, hz, rfl⟩)
    · obtain ⟨s, rfl⟩ := optOfSum_surj c
      exact Or.inl ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, rfl⟩
    · exact Or.inr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩

theorem menu2_mono (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) :
    MenuMono (menu2 gates p S) := by
  intro Q v w C hC
  rcases mem_menu2.mp hC with ⟨c, hc, rfl⟩ | ⟨z, ⟨hzQ, hzS⟩, rfl⟩
  · exact mem_menu2.mpr (Or.inl ⟨c, InMenuQ.mono (Finset.subset_insert v Q) hc, rfl⟩)
  · exact mem_menu2.mpr (Or.inr ⟨z, ⟨fun x hx => hzQ x (Finset.mem_insert_of_mem hx), hzS⟩, rfl⟩)

/-- **Menu2 is sound** (Menu1 classes by `card_pureCls`; real merge sets by L-LIFT, `realLTS_valid`). -/
theorem menu2_sound (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (S : Fin m → Finset (Fin n))
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)) :
    MenuSound gates p S (menu2 gates p S) := by
  intro w C hC
  rcases mem_menu2.mp hC with ⟨c, hc, rfl⟩ | ⟨z, ⟨-, hzS⟩, rfl⟩
  · exact ⟨card_pureCls gates p hp hg hU hN (S w) c hc.valid (out w) (hev w),
      pureCls_subset gates p (S w) c⟩
  · exact ⟨card_ltsCls gates p hp hg hU hN (S w) (out w) _
      (realLTS_valid gates p hp hg hU hN (S w) (out w) (hev w) z hzS), ltsCls_subset gates p (S w) _⟩

/-! ## L-U_v (front A2, 12:21): every gate of `U(Q)` is `0` at `(Q, 0)` -/

/-- A gate of a lifted class is `0` at the class's zero point. -/
theorem ltsCls_zero {gates : List Gate} {p : ℕ} {R : Finset (Fin n)} {t : LTS n} {i : ℕ}
    (hi : i ∈ ltsCls gates p R t) : val (lift n p gates) t.zero i = false := by
  classical
  have h := run_sub_DT _ _ _ _ _ hi
  rw [DT, Finset.mem_filter] at h
  exact h.2.1

/-- **L-U_v for Menu2**: every gate of `U(Q)` (the Menu2 classes of the sets alive at `Q`) is `0` in
`C_0` at the point `Q` (`(Q, 0)` in the lift). Every Menu2 zero point lies above `(Q, 0)`: `(Z, 1)`
with `Q ⊆ R' ⊆ Z`; `(top_w, 0)` with `Q ∩ S_w = ∅`; `(z, ν z)` with `Q ⊆ z`. Apply it at
`insert v Q` for front's statement about `U(Q ∪ {v})`. -/
theorem menu2_U_zero (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (S : Fin m → Finset (Fin n))
    (Q : Finset (Fin n)) :
    ∀ g ∈ UQG S (menu2 gates p S) Q, val (lift n p gates) (ext (canonPt Q) false) g = false := by
  classical
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  intro g hg'
  simp only [UQG, Finset.mem_biUnion, id] at hg'
  obtain ⟨w, hw, C, hC, hgC⟩ := hg'
  have hQw := mem_aliveSets.mp hw
  -- it suffices that the class's zero point lies above `(Q, 0)`
  have key : ∀ t : LTS n, ext (canonPt Q) false ≤ t.zero → g ∈ ltsCls gates p (S w) t →
      val (lift n p gates) (ext (canonPt Q) false) g = false := fun t hle hgt =>
    val_false_of_le _ hm.andOr hle (ltsCls_zero hgt)
  rcases mem_menu2.mp hC with ⟨c, hc, rfl⟩ | ⟨z, ⟨hzQ, -⟩, rfl⟩
  · rw [pureCls_eq_ltsCls] at hgC
    refine key _ ?_ hgC
    cases c with
    | oneAt Z A =>
      obtain ⟨-, R', -, hQR, hRZ⟩ := hc
      exact ext_le_of_le (canonPt_le fun x hx => hRZ x (hQR hx)) (by decide)
    | zero m' =>
      exact ext_le_of_le (canonPt_le_Zof hQw.symm) le_rfl
    | one Z => exact hc.elim
    | zeroAt z m' => exact hc.elim
  · exact key _ (ext_le_of_le (canonPt_le hzQ) (Bool.false_le _)) hgC

end PureMenu

/-- **951 from STAR-SEP over a sound monotone menu system.** -/
theorem no_minCE_of_starSepG
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (_ : p < gates.length) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ)),
        MenuMono Mn ∧ MenuSound gates p S Mn ∧ ∀ Q, StarSepG S Mn Q) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  intro n m S gates out M
  obtain ⟨p, hp, Mn, hmono, hs, hS⟩ := H n m S gates out M
  have h1 := bound_of_menuSDRG gates p hp S Mn hs (menuSDRG_of_starSepG S Mn hmono hS _ ∅ le_rfl)
  have h2 := M.ce.hlt
  omega

/-- **951 from STAR-COUNT over a sound monotone menu system.** -/
theorem no_minCE_of_starCountG
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (_ : p < gates.length) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ)),
        MenuMono Mn ∧ MenuSound gates p S Mn ∧
          ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ StarCountG S Mn Q v) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  intro n m S gates out M
  obtain ⟨p, hp, Mn, hmono, hs, hS⟩ := H n m S gates out M
  have h1 := bound_of_starCountG gates p hp S Mn hmono hs hS
  have h2 := M.ce.hlt
  omega

/-- **951 from STAR-SEP over Menu2** (front A2). -/
theorem no_minCE_of_starSep2
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, StarSepG S (menu2 gates p S) Q) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_starSepG fun n m S gates out M => by
    obtain ⟨p, hp, hN, hS⟩ := H n m S gates out M
    exact ⟨p, hp, menu2 gates p S, menu2_mono gates p S,
      menu2_sound gates p hp M.ce.hg M.ce.hU hN S out M.ce.hev, hS⟩

/-- **951 from STAR-COUNT over Menu2** (front A2). -/
theorem no_minCE_of_starCount2
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ StarCountG S (menu2 gates p S) Q v) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_starCountG fun n m S gates out M => by
    obtain ⟨p, hp, hN, hS⟩ := H n m S gates out M
    exact ⟨p, hp, menu2 gates p S, menu2_mono gates p S,
      menu2_sound gates p hp M.ce.hg M.ce.hU hN S out M.ce.hev, hS⟩

end PEqualNP.Outside.L_meta_951_aux

end PureMenu

section PureRestrict

/-! PureRestrict: the restricted circuit as an actual gate list (coord 11:59; the gap left open in
cTAHG's PureHeredity note, where the restricted instance's classes are modelled by evaluating the
original circuit at points of the subcube).

* `exists_restrict_runs` (any list circuit, any subcube `Cube Z ρ`): ONE restricted list `gates'`
  (`Kernel.list_restrictCube_keep`: constants propagated, the gates that are constant or copies of
  an earlier wire on the cube deleted, the others kept in order with their values on the cube) such
  that EVERY union-find run whose zero point and test points lie in the cube has the same final
  labelling on `gates'` and the same merge set up to renaming kept wire `n + t` to `n + e t`
  (`RunTransfer.run_transfer`: no merge at constants or copies).
* `exists_restrictedLift`: the lift `lift n p gates` (NOT gate replaced by the input `y`) restricted
  to `x_v := 0` for `v ∉ V`, `y` free (cTAHG's model: "NOT gate kept"). For every `R ⊆ V` and every
  restricted option (`RestrValid`), cTAHG's restricted class `restrCls gates p V R o` (the original
  run at subcube points) is the class `clsOn L V R o` of the run on the restricted list `L`,
  renamed. So the restricted instance's pure classes ARE pure-option runs on an actual gate list.
* `exists_restricted_correct`: the restricted real circuit for a family `F` with `S_w ⊆ V`
  (`list_restrictCube`, outputs `out w`, `w ∈ F`) computes `OR (S_w)` for every `w ∈ F` on EVERY
  input, keeps the 951 gate shape and at most one NOT gate, and has size
  `|gates_res| + #dead = |gates|` (the dead gates: constant or copied on the subcube, or outside
  every cone of the outputs of `F` after propagation), i.e. `|gates_res|` = the number of live gates.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## One restricted list for all runs in a cube -/

section General

variable {n : ℕ}

theorem exists_restrict_runs (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (Z : Finset (Fin n)) (ρ : Fin n → Bool) :
    ∃ (gates' : List Gate) (e : ℕ → ℕ), PEqualNP.Kernel.ShapeMap gates gates' e ∧
      (∀ t < gates'.length, ∀ x, PEqualNP.Kernel.Cube Z ρ x →
        val gates' x (n + t) = val gates x (n + e t)) ∧
      ∀ (z : Fin n → Bool) (pt : Fin n → Fin n → Bool) (R : Finset (Fin n)),
        (∀ u ∈ R, ∀ c, pt u c = true → z c = false → c = u) →
        PEqualNP.Kernel.Cube Z ρ z → (∀ u ∈ R, PEqualNP.Kernel.Cube Z ρ (pt u)) →
        runLT z pt R gates gates.length = runLT z pt R gates' gates'.length ∧
        runMT z pt R gates gates.length =
          (runMT z pt R gates' gates'.length).image (fun i => n + e (i - n)) := by
  obtain ⟨gates', e, hsh, hkeep, hdead⟩ := PEqualNP.Kernel.list_restrictCube_keep gates hops Z ρ
  refine ⟨gates', e, hsh, hkeep, fun z pt R hT hz hp => ?_⟩
  exact run_transfer z pt R gates gates' e (PEqualNP.Kernel.Cube Z ρ) hT hz hp hsh.1
    (fun t ht => (hsh.2 t ht).fst) hkeep hdead

end General

/-! ## The restricted lift: pure classes of the restricted instance -/

section Lift

variable {n : ℕ}

/-- The class of a pure option of the instance restricted to `V`, computed by a run on the
lifted list `L` (cTAHG's restricted points: `topIn V R` for `zero`). -/
noncomputable def clsOn (L : List Gate) (V R : Finset (Fin n)) : PureOpt n → Finset ℕ
  | .one Z => runMT (ext Z true) atom1 (liftSet R) L L.length
  | .zero m => runMT (ext (topIn V R) false) (atom0 m) (liftSet R) L L.length
  | .zeroAt z m => runMT (ext z false) (atom0 m) (liftSet R) L L.length
  | .oneAt Z A => runMT (ext Z true) (atom1W A) (liftSet R) L L.length

theorem restrCls_eq_clsOn (gates : List Gate) (p : ℕ) (V R : Finset (Fin n)) (o : PureOpt n) :
    restrCls gates p V R o = clsOn (lift n p gates) V R o := by
  cases o <;> rfl

/-- The lifted coordinates set to `0` by the restriction: `x_v`, `v ∉ V` (`y` stays free). -/
def offV (V : Finset (Fin n)) : Finset (Fin (n + 1)) := liftSet (Finset.univ \ V)

theorem cube_ext (V : Finset (Fin n)) (z : Fin n → Bool) (b : Bool)
    (hz : ∀ v, v ∉ V → z v = false) :
    PEqualNP.Kernel.Cube (offV V) (fun _ => false) (ext z b) := by
  intro t ht
  obtain ⟨v, hv, rfl⟩ := mem_liftSet_iff.mp ht
  rw [ext_castSucc]
  exact hz v (by simpa using hv)

theorem canonPt_off (V X : Finset (Fin n)) (hX : X ⊆ V) : ∀ v, v ∉ V → canonPt X v = false := by
  intro v hv
  cases h : canonPt X v
  · rfl
  · exact absurd (hX (canonPt_eq_true.mp h)) hv

theorem cube_atom1 (V R : Finset (Fin n)) (hRV : R ⊆ V) :
    ∀ c ∈ liftSet R, PEqualNP.Kernel.Cube (offV V) (fun _ => false) (atom1 c) := by
  intro c hc
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  rw [atom1_castSucc]
  exact cube_ext V _ true (canonPt_off V {u} (by simpa using hRV hu))

theorem cube_atom0 (V R : Finset (Fin n)) (hRV : R ⊆ V) (m : Fin n → Finset (Fin n))
    (hm : ∀ u ∈ R, m u ⊆ V) :
    ∀ c ∈ liftSet R, PEqualNP.Kernel.Cube (offV V) (fun _ => false) (atom0 m c) := by
  intro c hc
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  rw [atom0_castSucc]
  exact cube_ext V _ false (canonPt_off V _ (Finset.insert_subset (hRV hu) (hm u hu)))

theorem cube_atom1W (V R : Finset (Fin n)) (hRV : R ⊆ V) (A : Fin n → Finset (Fin n))
    (hA : ∀ u ∈ R, A u ⊆ V) :
    ∀ c ∈ liftSet R, PEqualNP.Kernel.Cube (offV V) (fun _ => false) (atom1W A c) := by
  intro c hc
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  rw [atom1W_castSucc]
  exact cube_ext V _ true (canonPt_off V _ (Finset.insert_subset (hRV hu) (hA u hu)))

/-! Test-point conditions (`hT` of `runLT_inv`) for the lifted atoms. -/

theorem hT_atom1 (R : Finset (Fin n)) (Z : Fin n → Bool) :
    ∀ c ∈ liftSet R, ∀ c' : Fin (n + 1), atom1 c c' = true → ext Z true c' = false → c' = c := by
  intro c _ c' h1 h2
  rw [atom1, canonPt_eq_true, Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with h1 | h1
  · exact h1
  · rw [h1, ext_last] at h2
    exact absurd h2 (by decide)

theorem hT_atom0 (R : Finset (Fin n)) (z : Fin n → Bool) (m : Fin n → Finset (Fin n))
    (hmz : ∀ u ∈ R, ∀ v ∈ m u, v = u ∨ z v = true) :
    ∀ c ∈ liftSet R, ∀ c' : Fin (n + 1), atom0 m c c' = true → ext z false c' = false → c' = c := by
  intro c hc c' h1 h2
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  rw [atom0_castSucc] at h1
  induction c' using Fin.lastCases with
  | last => rw [ext_last] at h1; exact absurd h1 (by decide)
  | cast v =>
    rw [ext_castSucc, canonPt_eq_true, Finset.mem_insert] at h1
    rw [ext_castSucc] at h2
    rcases h1 with rfl | h1
    · rfl
    · rcases hmz u hu v h1 with rfl | h3
      · rfl
      · rw [h3] at h2; exact absurd h2 (by decide)

theorem hT_atom1W (R : Finset (Fin n)) (Z : Fin n → Bool) (A : Fin n → Finset (Fin n))
    (hAZ : ∀ u ∈ R, ∀ v ∈ A u, v = u ∨ Z v = true) :
    ∀ c ∈ liftSet R, ∀ c' : Fin (n + 1), atom1W A c c' = true → ext Z true c' = false →
      c' = c := by
  intro c hc c' h1 h2
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  rw [atom1W_castSucc] at h1
  induction c' using Fin.lastCases with
  | last => rw [ext_last] at h2; exact absurd h2 (by decide)
  | cast v =>
    rw [ext_castSucc, canonPt_eq_true, Finset.mem_insert] at h1
    rw [ext_castSucc] at h2
    rcases h1 with rfl | h1
    · rfl
    · rcases hAZ u hu v h1 with rfl | h3
      · rfl
      · rw [h3] at h2; exact absurd h2 (by decide)

/-- The zero condition `topIn V R` for `zero m` options. -/
theorem topIn_mz (V R : Finset (Fin n)) (m : Fin n → Finset (Fin n))
    (hm : ∀ u ∈ R, ∀ v ∈ m u, v ∈ R → v = u) (hmV : ∀ u ∈ R, m u ⊆ V) :
    ∀ u ∈ R, ∀ v ∈ m u, v = u ∨ topIn V R v = true := by
  intro u hu v hv
  by_cases hvR : v ∈ R
  · exact Or.inl (hm u hu v hv hvR)
  · right
    rw [topIn, canonPt_eq_true, Finset.mem_sdiff]
    exact ⟨hmV u hu hv, hvR⟩

/-- **The restricted lift.** One list `L`: the lift restricted to `x_v := 0` off `V` (`y` free),
with kept-gate map `e`; for every `R ⊆ V` and every restricted option, the restricted class (the
original run at subcube points) is the run on `L`, renamed. -/
theorem exists_restrictedLift (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (V : Finset (Fin n)) :
    ∃ (L : List Gate) (e : ℕ → ℕ), PEqualNP.Kernel.ShapeMap (lift n p gates) L e ∧
      (∀ t < L.length, ∀ x, PEqualNP.Kernel.Cube (offV V) (fun _ => false) x →
        val L x (n + 1 + t) = val (lift n p gates) x (n + 1 + e t)) ∧
      ∀ R : Finset (Fin n), R ⊆ V → ∀ o : PureOpt n, RestrValid gates p V R o →
        restrCls gates p V R o = (clsOn L V R o).image (fun i => n + 1 + e (i - (n + 1))) := by
  have hops : ∀ g ∈ lift n p gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hgm => ((lift_ops gates p hp hg hU hN g hgm).1).elim Or.inl (fun h => Or.inr (Or.inl h))
  obtain ⟨L, e, hsh, hkeep, hrun⟩ := exists_restrict_runs (lift n p gates) hops (offV V)
    (fun _ => false)
  refine ⟨L, e, hsh, hkeep, fun R hRV o ho => ?_⟩
  rw [restrCls_eq_clsOn]
  cases o with
  | one Z =>
    obtain ⟨⟨hZR, -⟩, hZV⟩ := ho
    exact (hrun _ _ _ (hT_atom1 R Z) (cube_ext V Z true hZV) (cube_atom1 V R hRV)).2
  | zero m =>
    obtain ⟨⟨hm, -⟩, hmV⟩ := ho
    have hz : ∀ v, v ∉ V → topIn V R v = false :=
      canonPt_off V (V \ R) Finset.sdiff_subset
    exact (hrun _ _ _ (hT_atom0 R _ m (topIn_mz V R m hm hmV)) (cube_ext V _ false hz)
      (cube_atom0 V R hRV m hmV)).2
  | zeroAt z m =>
    obtain ⟨⟨-, hmz, -⟩, hzV, hmV⟩ := ho
    exact (hrun _ _ _ (hT_atom0 R z m hmz) (cube_ext V z false hzV)
      (cube_atom0 V R hRV m hmV)).2
  | oneAt Z A =>
    obtain ⟨⟨-, -, hAZ⟩, hZV, hAV⟩ := ho
    exact (hrun _ _ _ (hT_atom1W R Z A hAZ) (cube_ext V Z true hZV)
      (cube_atom1W V R hRV A hAV)).2

end Lift

/-! ## The restricted real circuit is a correct circuit for `F` -/

section Correct

variable {n m : ℕ}

theorem exists_restricted_correct (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (F : Finset (Fin m)) (V : Finset (Fin n)) (hFV : ∀ w ∈ F, S w ⊆ V)
    (h1 : ∀ w ∈ F, (S w).Nonempty) :
    ∃ (gates' : List Gate) (out' : Fin m → ℕ),
      gates'.length +
          (PEqualNP.Kernel.deadLC gates (Finset.univ \ V) (fun _ => false) (F.image out)).card =
        gates.length ∧
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      AtMostOneNot gates' ∧
      ∀ w ∈ F, ∀ x : Fin n → Bool, val gates' x (out' w) = decide (∃ v ∈ S w, x v = true) := by
  classical
  obtain ⟨gates', e, r, hlen, hsh, hout⟩ := PEqualNP.Kernel.list_restrictCube gates
    (fun g hgm => (hg g hgm).1) (Finset.univ \ V) (fun _ => false) (F.image out)
  refine ⟨gates', fun w => r (out w), hlen, hsh.hg hg, hsh.hU hU, fun w hw x => ?_⟩
  rcases hout (out w) (Finset.mem_image_of_mem out hw) with ⟨c, hc⟩ | h
  · exfalso
    obtain ⟨u, hu⟩ := h1 w hw
    have hcube : ∀ X : Finset (Fin n), X ⊆ V →
        PEqualNP.Kernel.Cube (Finset.univ \ V) (fun _ => false) (canonPt X) := by
      intro X hX t ht
      exact canonPt_off V X hX t (by simpa using ht)
    have e0 := hc (canonPt ∅) (hcube ∅ (Finset.empty_subset _))
    have e1 := hc (canonPt {u}) (hcube {u} (by simpa using hFV w hw hu))
    rw [hev] at e0 e1
    have : decide (∃ v ∈ S w, canonPt (∅ : Finset (Fin n)) v = true) = false := by
      simp [canonPt]
    have h' : decide (∃ v ∈ S w, canonPt ({u} : Finset (Fin n)) v = true) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨u, hu, canonPt_eq_true.mpr (Finset.mem_singleton_self u)⟩
    rw [this] at e0
    rw [h', ← e0] at e1
    exact absurd e1 (by decide)
  · rw [h x, hev]
    congr 1
    apply propext
    constructor
    · rintro ⟨v, hv, hxv⟩
      refine ⟨v, hv, ?_⟩
      rw [PEqualNP.Kernel.proj_notMem (Finset.univ \ V) (fun _ => false) x
        (by simpa using hFV w hw hv)] at hxv
      exact hxv
    · rintro ⟨v, hv, hxv⟩
      refine ⟨v, hv, ?_⟩
      rw [PEqualNP.Kernel.proj_notMem (Finset.univ \ V) (fun _ => false) x
        (by simpa using hFV w hw hv)]
      exact hxv

end Correct

end PEqualNP.Outside.L_meta_951_aux

end PureRestrict

section UGame

/-!
# UGame: Theorem G of the global-price route (Fable, fable-global-price.md §3), refereed by cTAHG

The U-GAME on the lifted outputs: every set picks a valid lifted test system (`LTSValid`), and every
pair of sets is certified in one direction by Theorem U (`LTSCert`: of every two distinct atoms of `t`,
one lies below the zero point of `t'`). **Theorem G**: a won U-game gives LiftSDR, hence MUL and
`base ≤ #gates - 1`. No minimality, no hypothesis on Berge cycles or junk gates.

* `LTSCert`, `UGameWon`, **`liftSDR_of_ugame`** (Theorem G), **`no_minCE_of_ugame`**.
* The pure-world forms: **G1** (`ugame_of_G1`: zero points `(Z_w, 1)` with `h(Z_w) = 0`, atoms `(e_u, 1)`,
  certificate `|S_w \ Z_w'| ≤ 1`) and **G0** (`ugame_of_G0`: zero points `(top_w, 0)`, atoms
  `(A_u, 0)` with `h(A_u) = 1`, `A_u ∩ S_w ⊆ {u}`, certificate: of two points one atom misses `S_w'`).
* Corollaries: (a) `ugame_of_allHeavy` (every point of every set heavy); (c) `ugame_of_typeB` (every
  set type B, `h(top_w) = 0`).

Referee (cTAHG, board 951/board/agents/cTAHG-referee-thmG.md): Theorem G, Lemma N, Propositions 1, 2, S,
G0/G1 validity, corollaries (a)-(e), Theorem D and Lemma T checked line by line; the U-game is won and
independently verified on 19 of the 21 barrier witnesses (MATCH-C, MATCH-S, all twin trees, STAR4,
STAR4b, PAPPUS-JUNK, cxMU_clean2, ...) and lost exactly on cxMU_dd and cx44_1_junk (the DD core, the
open part (X) of the note).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section UGame

variable {n m : ℕ}

/-- **Theorem U's certificate** `t → t'` for the set `R`: of every two distinct atoms of `t`, one lies
below the zero point of `t'`. -/
def LTSCert (R : Finset (Fin n)) (t t' : LTS n) : Prop :=
  ∀ c ∈ liftSet R, ∀ c' ∈ liftSet R, c ≠ c' → t.atom c ≤ t'.zero ∨ t.atom c' ≤ t'.zero

/-- **The U-game is won**: valid lifted test systems, every pair certified in one direction. -/
def UGameWon (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) (p : ℕ) : Prop :=
  ∃ t : Fin m → LTS n, (∀ w, LTSValid gates p (S w) (out w) (t w)) ∧
    ∀ w w', w ≠ w' → LTSCert (S w) (t w) (t w') ∨ LTSCert (S w') (t w') (t w)

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hp hg hU hN in
/-- **Theorem U** for lifted test systems: a certificate `t → t'` makes the classes disjoint. -/
theorem ltsCls_disjoint_of_cert (R R' : Finset (Fin n)) (t t' : LTS n) (h : LTSCert R t t') :
    Disjoint (ltsCls gates p R t) (ltsCls gates p R' t') :=
  runMT_disjoint_of_le _ (monoList_lift (n := n) gates p hp hg hU hN) _ _ _ _ _ _ h

include hp hg hU hN in
/-- **Theorem G**: a won U-game gives LiftSDR. -/
theorem liftSDR_of_ugame (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (H : UGameWon S gates out p) : LiftSDR S gates out p := by
  obtain ⟨t, hv, hc⟩ := H
  refine ⟨t, hv, fun w w' hww => ?_⟩
  rcases hc w w' hww with h | h
  · exact ltsCls_disjoint_of_cert gates p hp hg hU hN _ _ _ _ h
  · exact (ltsCls_disjoint_of_cert gates p hp hg hU hN _ _ _ _ h).symm

/-! ## The pure-world forms -/

include hp hg hU hN in
/-- **G1** (world 1): zero points `(Z_w, 1)` with `Z_w ∩ S_w = ∅` and `h(Z_w) = 0` (the NOT gate `1`),
atoms `(e_u, 1)`; certificate `w → w'` when at most one point of `S_w` is outside `Z_w'`. -/
theorem ugame_of_G1 (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (Z : Fin m → Fin n → Bool) (hZS : ∀ w, ∀ u ∈ S w, Z w u = false)
    (hZ : ∀ w, val gates (Z w) (n + p) = true)
    (hcert : ∀ w w', w ≠ w' →
      ((S w).filter fun u => Z w' u = false).card ≤ 1 ∨
        ((S w').filter fun u => Z w u = false).card ≤ 1) :
    UGameWon S gates out p := by
  have hone : ∀ (R R' : Finset (Fin n)) (Z' : Fin n → Bool),
      (R.filter fun u => Z' u = false).card ≤ 1 → ∀ Z0 : Fin n → Bool,
      LTSCert R ((PureOpt.one Z0).toLTS R) ((PureOpt.one Z').toLTS R') := by
    intro R R' Z' hR Z0
    refine liftSet_pairs fun u hu v hv huv => ?_
    simp only [PureOpt.toLTS]
    rw [atom1_castSucc, atom1_castSucc]
    have key : ∀ x : Fin n, Z' x = true → ext (canonPt {x}) true ≤ ext Z' true := fun x hx =>
      ext_le_of_le (canonPt_le fun y hy => by rw [Finset.mem_singleton.mp hy]; exact hx) le_rfl
    by_cases hu' : Z' u = true
    · exact Or.inl (key u hu')
    · by_cases hv' : Z' v = true
      · exact Or.inr (key v hv')
      · have : 1 < (R.filter fun u => Z' u = false).card := Finset.one_lt_card.mpr
          ⟨u, Finset.mem_filter.mpr ⟨hu, by simpa using hu'⟩, v,
            Finset.mem_filter.mpr ⟨hv, by simpa using hv'⟩, huv⟩
        omega
  refine ⟨fun w => (PureOpt.one (Z w)).toLTS (S w), fun w => ?_, fun w w' hww => ?_⟩
  · exact pureValid_ltsValid gates p hp hg hU hN (S w) (out w) (hev w) _ ⟨hZS w, hZ w⟩
  · rcases hcert w w' hww with h | h
    · exact Or.inl (hone (S w) (S w') (Z w') h (Z w))
    · exact Or.inr (hone (S w') (S w) (Z w) h (Z w'))

include hp hg hU hN in
/-- **G0** (world 0): zero points `(top_w, 0)`, atoms `(A_u, 0)` with `h(A_u) = 1` (the NOT gate `0`)
and `A_u ∩ S_w ⊆ {u}`; certificate `w → w'` when of every two points of `S_w` one atom misses
`S_w'`. -/
theorem ugame_of_G0 (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (A : Fin m → Fin n → Finset (Fin n)) (hAS : ∀ w, ∀ u ∈ S w, ∀ v ∈ A w u, v ∈ S w → v = u)
    (hA : ∀ w, ∀ u ∈ S w, val gates (canonPt (A w u)) (n + p) = false)
    (hcert : ∀ w w', w ≠ w' →
      (∀ u ∈ S w, ∀ u' ∈ S w, u ≠ u' →
        Disjoint (insert u (A w u)) (S w') ∨ Disjoint (insert u' (A w u')) (S w')) ∨
      (∀ u ∈ S w', ∀ u' ∈ S w', u ≠ u' →
        Disjoint (insert u (A w' u)) (S w) ∨ Disjoint (insert u' (A w' u')) (S w))) :
    UGameWon S gates out p := by
  have hzero : ∀ (R R' : Finset (Fin n)) (A' : Fin n → Finset (Fin n)),
      (∀ u ∈ R, ∀ u' ∈ R, u ≠ u' →
        Disjoint (insert u (A' u)) R' ∨ Disjoint (insert u' (A' u')) R') →
      LTSCert R ((PureOpt.zero A').toLTS R) ((PureOpt.zero A').toLTS R') := by
    intro R R' A' h
    refine liftSet_pairs fun u hu v hv huv => ?_
    simp only [PureOpt.toLTS]
    rw [atom0_castSucc, atom0_castSucc]
    have key : ∀ x : Fin n, Disjoint (insert x (A' x)) R' →
        ext (canonPt (insert x (A' x))) false ≤ ext (Zof R') false := fun x hx =>
      ext_le_of_le (canonPt_le fun y hy => by
        simp [Zof, Finset.disjoint_left.mp hx hy]) le_rfl
    rcases h u hu v hv huv with h1 | h1
    · exact Or.inl (key u h1)
    · exact Or.inr (key v h1)
  refine ⟨fun w => (PureOpt.zero (A w)).toLTS (S w), fun w => ?_, fun w w' hww => ?_⟩
  · exact pureValid_ltsValid gates p hp hg hU hN (S w) (out w) (hev w) _ ⟨hAS w, hA w⟩
  · rcases hcert w w' hww with h | h
    · left
      have := hzero (S w) (S w') (A w) h
      intro c hc c' hc' hcc
      rcases this c hc c' hc' hcc with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · right
      have := hzero (S w') (S w) (A w') h
      intro c hc c' hc' hcc
      rcases this c hc c' hc' hcc with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1

include hp hg hU hN in
/-- **Corollary (a)**: if every point of every set is heavy (`h(e_u) = 1`), the U-game is won (G0 with
`A_u = {u}`). -/
theorem ugame_of_allHeavy (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hheavy : ∀ w, ∀ u ∈ S w, val gates (canonPt {u}) (n + p) = false) :
    UGameWon S gates out p := by
  classical
  refine ugame_of_G0 gates p hp hg hU hN S out hev (fun _ u => {u})
    (fun w u _ v hv _ => Finset.mem_singleton.mp hv) hheavy fun w w' hww => Or.inl ?_
  intro u hu u' hu' huu
  simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.disjoint_singleton_left]
  by_contra hc
  push Not at hc
  have : 1 < (S w ∩ S w').card := Finset.one_lt_card.mpr
    ⟨u, Finset.mem_inter.mpr ⟨hu, hc.1⟩, u', Finset.mem_inter.mpr ⟨hu', hc.2⟩, huu⟩
  have := hS w w' hww
  omega

include hp hg hU hN in
/-- **Corollary (c)**: if every set is type B (`h(top_w) = 0`, the NOT gate `1` at `Zof S_w`), the
U-game is won (G1 with `Z_w = top_w`). -/
theorem ugame_of_typeB (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hB : ∀ w, val gates (Zof (S w)) (n + p) = true) : UGameWon S gates out p := by
  classical
  refine ugame_of_G1 gates p hp hg hU hN S out hev (fun w => Zof (S w)) (fun w u hu => by simp [Zof, hu]) hB
    fun w w' hww => Or.inl ?_
  have : ((S w).filter fun u => Zof (S w') u = false) = S w ∩ S w' := by
    ext u
    simp [Zof, Finset.mem_inter]
  rw [this]
  exact hS w w' hww

end UGame

/-- **951 from the U-game** (Theorem G): if every minimal counterexample has a NOT gate whose lifted
outputs win the U-game, there is no minimal counterexample. -/
theorem no_minCE_of_ugame
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out →
        ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧ UGameWon S gates out p) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_liftSDR fun n m S gates out M => by
    obtain ⟨p, hp, hN, hW⟩ := H n m S gates out M
    exact ⟨p, hp, hN, liftSDR_of_ugame gates p hp M.ce.hg M.ce.hU hN S out hW⟩

end PEqualNP.Outside.L_meta_951_aux

end UGame
