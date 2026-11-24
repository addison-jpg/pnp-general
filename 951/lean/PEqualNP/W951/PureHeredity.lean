import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PureHall
import PEqualNP.W951.SDRWitnessFixh16

/-!
# PureHeredity: pure menus under the restriction `x_v := 0` off `V` (front's graph lane)

Coord 11:08: relate the pure menus of the instance RESTRICTED to a family `F` (variables outside
`V = ⋃_{w ∈ F} S_w` set to `0`, NOT gate kept) to the original menus.

**Model.** The restricted circuit's wires take, at a point `x` of the subcube `{x | x = 0 off V}`,
the original values (`Kernel/W951Cube.val_restrictZero`; the dead gates it removes are constants and
copies of earlier wires on the subcube, and a union-find run never merges at either). So the
restricted instance's pure classes are the original runs at points vanishing off `V`, with one
change: the restricted `top_w` is `V \ S_w` (`topIn V R`), not `top_w`. The restricted options, as
options of the original circuit (`RestrValid`):
* I1 `one Z` with `Z` vanishing off `V`: an original I1 option, same class;
* I0 `zero m` with `m_u ⊆ V`: zero point `(V \ S_w, 0)`, i.e. the original `zeroAt (topIn V R) m`;
* `zeroAt z m` with `z` vanishing off `V` and `m_u ⊆ V`: the same option.

**Results.**
* `restrValid_valid`, `restrictedMenu_subset_pureMenu`: every restricted option is a valid option of
  the original instance with the same class, so `restricted menu(w) ⊆ menu(w)` for `R = S_w ⊆ V`.
  This uses the general zero point `zeroAt` (`PureSDR.lean`).
* `oneAt` (`PureSDR.lean`: I1 atoms `({u} ∪ A_u, 1)`, `A_u ⊆ Z ∪ {u}`) does the same for the board
  integrator's restriction `x_O := 1` (50293a5: there I0 transfers and plain I1 does not, the
  restricted atoms being `{u} ∪ O`): `RestrValid1`, `restrOpt1`, `restrValid1_valid`,
  `restrictedMenu1_subset_pureMenu`, `restricted1_deficient`.
* `heredity_top_fails` (Lean-checked witness): with the top-only options (`one`, `zero`) the inclusion
  is FALSE. In scaffold's forced-h circuit fixh16_20 (`n = 4`, `K4` pairs, 16 gates), for
  `F = {S_1, S_2}`, `V = {0, 2, 3}`, `w = 2`, `S_w = {0, 3}`, the restricted I0 option `m_0 = {0, 2}`,
  `m_3 = {2, 3}` has class `{h}` (lifted wire `9`, the wire read by the NOT gate), and `h` is in no
  class of a valid `one` / `zero` option of the original (`C_0(h)(top_w) = 1`, `C_1(h)(e_0) =
  C_1(h)(e_3) = 0`). Data (`951/research/heredity/`): 144 such restricted I0 classes on the 26
  graph-system circuits of the repository corpus, 344 on all 63.
* General facts used: `pureI1_atom` (a wire of an I1 class is true at an atom `(e_u, 1)`),
  `pureI0At_zero` (a wire of an I0 class is false at its zero point).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section PureHeredity

variable {n : ℕ}

/-! ## Membership facts -/

theorem pureI1_atom {gates : List Gate} {p : ℕ} {R : Finset (Fin n)} {Z : Fin n → Bool} {i : ℕ}
    (hi : i ∈ pureI1 gates p R Z) :
    ∃ c ∈ liftSet R, val (lift n p gates) (atom1 c) i = true := by
  classical
  have h := run_sub_DT _ _ _ _ _ hi
  rw [DT, Finset.mem_filter] at h
  obtain ⟨-, -, u, -, -, hu, -, hui, -⟩ := h
  exact ⟨u, hu, hui⟩

theorem pureI0At_zero {gates : List Gate} {p : ℕ} {R : Finset (Fin n)} {z : Fin n → Bool}
    {m : Fin n → Finset (Fin n)} {i : ℕ} (hi : i ∈ pureI0At gates p R z m) :
    val (lift n p gates) (ext z false) i = false := by
  classical
  have h := run_sub_DT _ _ _ _ _ hi
  rw [DT, Finset.mem_filter] at h
  exact h.2.1

/-! ## Restricted options -/

/-- The restricted instance's `top_w` for `R ⊆ V`: true exactly on `V \ R`. -/
def topIn (V R : Finset (Fin n)) : Fin n → Bool := canonPt (V \ R)

/-- Options of the instance restricted to `V`, written as options of the original circuit (see the
module header): every point vanishes off `V`; the restricted `zero m` stands for
`zeroAt (topIn V R) m`. -/
def RestrValid (gates : List Gate) (p : ℕ) (V R : Finset (Fin n)) : PureOpt n → Prop
  | .one Z => PureValid gates p R (.one Z) ∧ ∀ v, v ∉ V → Z v = false
  | .zero m => PureValid gates p R (.zero m) ∧ ∀ u ∈ R, m u ⊆ V
  | .zeroAt z m => PureValid gates p R (.zeroAt z m) ∧ (∀ v, v ∉ V → z v = false) ∧ ∀ u ∈ R, m u ⊆ V
  | .oneAt Z A => PureValid gates p R (.oneAt Z A) ∧ (∀ v, v ∉ V → Z v = false) ∧ ∀ u ∈ R, A u ⊆ V

/-- The class of a restricted option, in the original circuit (lifted wires). -/
noncomputable def restrCls (gates : List Gate) (p : ℕ) (V R : Finset (Fin n)) : PureOpt n → Finset ℕ
  | .one Z => pureI1 gates p R Z
  | .zero m => pureI0At gates p R (topIn V R) m
  | .zeroAt z m => pureI0At gates p R z m
  | .oneAt Z A => pureI1At gates p R Z A

/-- The original option a restricted option stands for. -/
def restrOpt (V R : Finset (Fin n)) : PureOpt n → PureOpt n
  | .one Z => .one Z
  | .zero m => .zeroAt (topIn V R) m
  | .zeroAt z m => .zeroAt z m
  | .oneAt Z A => .oneAt Z A

theorem restrCls_eq (gates : List Gate) (p : ℕ) (V R : Finset (Fin n)) (c : PureOpt n) :
    restrCls gates p V R c = pureCls gates p R (restrOpt V R c) := by
  cases c <;> rfl

/-- **Heredity of options.** A restricted option is a valid option of the original instance. -/
theorem restrValid_valid (gates : List Gate) (p : ℕ) (V R : Finset (Fin n)) (c : PureOpt n)
    (hc : RestrValid gates p V R c) : PureValid gates p R (restrOpt V R c) := by
  cases c with
  | one Z => exact hc.1
  | zero m =>
    obtain ⟨⟨hmR, hmN⟩, hmV⟩ := hc
    refine ⟨fun v hv => ?_, fun u hu v hv => ?_, hmN⟩
    · simp [topIn, canonPt, hv]
    · by_cases hvu : v = u
      · exact Or.inl hvu
      · right
        have hvR : v ∉ R := fun h => hvu (hmR u hu v hv h)
        simp [topIn, canonPt, hmV u hu hv, hvR]
  | zeroAt z m => exact hc.1
  | oneAt Z A => exact hc.1

/-- Options as a finite sum type (for menus as `Finset`s). -/
def optOfSum : (Fin n → Bool) ⊕ (Fin n → Finset (Fin n)) ⊕ ((Fin n → Bool) × (Fin n → Finset (Fin n))) ⊕
    ((Fin n → Bool) × (Fin n → Finset (Fin n))) → PureOpt n
  | .inl Z => .one Z
  | .inr (.inl m) => .zero m
  | .inr (.inr (.inl zm)) => .zeroAt zm.1 zm.2
  | .inr (.inr (.inr ZA)) => .oneAt ZA.1 ZA.2

theorem optOfSum_surj (c : PureOpt n) : ∃ s, optOfSum s = c := by
  cases c with
  | one Z => exact ⟨.inl Z, rfl⟩
  | zero m => exact ⟨.inr (.inl m), rfl⟩
  | zeroAt z m => exact ⟨.inr (.inr (.inl (z, m))), rfl⟩
  | oneAt Z A => exact ⟨.inr (.inr (.inr (Z, A))), rfl⟩

open Classical in
/-- **The restricted menu** of `R`: the union of the classes of the restricted options. -/
noncomputable def restrictedMenu (gates : List Gate) (p : ℕ) (V R : Finset (Fin n)) : Finset ℕ :=
  (Finset.univ.filter fun s => RestrValid gates p V R (optOfSum s)).biUnion
    fun s => restrCls gates p V R (optOfSum s)

theorem mem_restrictedMenu {gates : List Gate} {p : ℕ} {V R : Finset (Fin n)} {g : ℕ} :
    g ∈ restrictedMenu gates p V R ↔ ∃ c, RestrValid gates p V R c ∧ g ∈ restrCls gates p V R c := by
  classical
  rw [restrictedMenu, Finset.mem_biUnion]
  constructor
  · rintro ⟨s, hs, hg⟩
    exact ⟨optOfSum s, (Finset.mem_filter.mp hs).2, hg⟩
  · rintro ⟨c, hc, hg⟩
    obtain ⟨s, rfl⟩ := optOfSum_surj c
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, hg⟩

/-- **Heredity of menus.** The restricted menu of `R` lies in the original pure menu of `R`. -/
theorem restrictedMenu_subset_pureMenu (gates : List Gate) (p : ℕ) (V R : Finset (Fin n)) :
    restrictedMenu gates p V R ⊆ pureMenu gates p R := by
  intro g hg
  obtain ⟨c, hc, hgc⟩ := mem_restrictedMenu.mp hg
  rw [restrCls_eq] at hgc
  exact mem_pureMenu.mpr ⟨restrOpt V R c, restrValid_valid gates p V R c hc, hgc⟩

/-- **Hall deficiency passes to the restriction.** If a family `F` of sets inside `V` has
`|⋃_{w ∈ F} menu(w)| < |F|` in the original instance, the same holds for the restricted menus. -/
theorem restricted_deficient {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ)
    (V : Finset (Fin n)) (F : Finset (Fin m))
    (hdef : (F.biUnion fun w => pureMenu gates p (S w)).card < F.card) :
    (F.biUnion fun w => restrictedMenu gates p V (S w)).card < F.card :=
  lt_of_le_of_lt (Finset.card_le_card (Finset.biUnion_mono fun w _ =>
    restrictedMenu_subset_pureMenu gates p V (S w))) hdef

/-- **Gate form** (desktop Coord / research 11:55): the union of the restricted menus of a family has
at most as many gates as the union of its original menus; so `|⋃_F menu| < base(F)` passes to the
restriction (any bound `k`, not only `|F|`). -/
theorem restricted_union_le {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ)
    (V : Finset (Fin n)) (F : Finset (Fin m)) :
    (F.biUnion fun w => restrictedMenu gates p V (S w)).card ≤
      (F.biUnion fun w => pureMenu gates p (S w)).card :=
  Finset.card_le_card (Finset.biUnion_mono fun w _ => restrictedMenu_subset_pureMenu gates p V (S w))

theorem restricted_gate_deficient {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ)
    (V : Finset (Fin n)) (F : Finset (Fin m)) (k : ℕ)
    (hdef : (F.biUnion fun w => pureMenu gates p (S w)).card < k) :
    (F.biUnion fun w => restrictedMenu gates p V (S w)).card < k :=
  lt_of_le_of_lt (restricted_union_le S gates p V F) hdef

/-! ## The restriction `x_O := 1` off `V` (board integrator's kill test, 50293a5) -/

/-- Options of the instance restricted by `x_v := 1` off `V`, as options of the original circuit:
every point is `1` off `V`; the restricted world-1 atoms `e_u` are `{u} ∪ Vᶜ` (`oneAt Z (· ∪ Vᶜ)`),
the restricted `top_w` is `top_w` itself (for `R ⊆ V`). -/
def RestrValid1 (gates : List Gate) (p : ℕ) (V R : Finset (Fin n)) : PureOpt n → Prop
  | .one Z => PureValid gates p R (.one Z) ∧ ∀ v, v ∉ V → Z v = true
  | .zero m => PureValid gates p R (.zero m) ∧ ∀ u ∈ R, Vᶜ ⊆ m u
  | .zeroAt z m => PureValid gates p R (.zeroAt z m) ∧ ∀ v, v ∉ V → z v = true
  | .oneAt Z A => PureValid gates p R (.oneAt Z A) ∧ ∀ v, v ∉ V → Z v = true

/-- The original option a `x_O := 1` restricted option stands for. -/
def restrOpt1 (V : Finset (Fin n)) : PureOpt n → PureOpt n
  | .one Z => .oneAt Z fun _ => Vᶜ
  | .zero m => .zero m
  | .zeroAt z m => .zeroAt z m
  | .oneAt Z A => .oneAt Z fun u => A u ∪ Vᶜ

/-- **Heredity of options under `x_O := 1`.** -/
theorem restrValid1_valid (gates : List Gate) (p : ℕ) (V R : Finset (Fin n)) (c : PureOpt n)
    (hc : RestrValid1 gates p V R c) : PureValid gates p R (restrOpt1 V c) := by
  cases c with
  | one Z =>
    obtain ⟨⟨hZR, hZ⟩, hV⟩ := hc
    exact ⟨hZR, hZ, fun u _ v hv => Or.inr (hV v (Finset.mem_compl.mp hv))⟩
  | zero m => exact hc.1
  | zeroAt z m => exact hc.1
  | oneAt Z A =>
    obtain ⟨⟨hZR, hZ, hA⟩, hV⟩ := hc
    refine ⟨hZR, hZ, fun u hu v hv => ?_⟩
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hA u hu v hv
    · exact Or.inr (hV v (Finset.mem_compl.mp hv))

open Classical in
/-- **The restricted menu under `x_O := 1`**: the union of the original classes of the restricted
options (each restricted option's class is the class of `restrOpt1`). -/
noncomputable def restrictedMenu1 (gates : List Gate) (p : ℕ) (V R : Finset (Fin n)) : Finset ℕ :=
  (Finset.univ.filter fun s => RestrValid1 gates p V R (optOfSum s)).biUnion
    fun s => pureCls gates p R (restrOpt1 V (optOfSum s))

/-- **Heredity of menus under `x_O := 1`.** -/
theorem restrictedMenu1_subset_pureMenu (gates : List Gate) (p : ℕ) (V R : Finset (Fin n)) :
    restrictedMenu1 gates p V R ⊆ pureMenu gates p R := by
  classical
  intro g hg
  rw [restrictedMenu1, Finset.mem_biUnion] at hg
  obtain ⟨s, hs, hgs⟩ := hg
  exact mem_pureMenu.mpr ⟨_, restrValid1_valid gates p V R _ (Finset.mem_filter.mp hs).2, hgs⟩

/-- Hall deficiency passes to the `x_O := 1` restriction. -/
theorem restricted1_deficient {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ)
    (V : Finset (Fin n)) (F : Finset (Fin m))
    (hdef : (F.biUnion fun w => pureMenu gates p (S w)).card < F.card) :
    (F.biUnion fun w => restrictedMenu1 gates p V (S w)).card < F.card :=
  lt_of_le_of_lt (Finset.card_le_card (Finset.biUnion_mono fun w _ =>
    restrictedMenu1_subset_pureMenu gates p V (S w))) hdef

/-- Gate form under `x_O := 1`. -/
theorem restricted1_union_le {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ)
    (V : Finset (Fin n)) (F : Finset (Fin m)) :
    (F.biUnion fun w => restrictedMenu1 gates p V (S w)).card ≤
      (F.biUnion fun w => pureMenu gates p (S w)).card :=
  Finset.card_le_card (Finset.biUnion_mono fun w _ => restrictedMenu1_subset_pureMenu gates p V (S w))

theorem restricted1_gate_deficient {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ)
    (V : Finset (Fin n)) (F : Finset (Fin m)) (k : ℕ)
    (hdef : (F.biUnion fun w => pureMenu gates p (S w)).card < k) :
    (F.biUnion fun w => restrictedMenu1 gates p V (S w)).card < k :=
  lt_of_le_of_lt (restricted1_union_le S gates p V F) hdef

/-- The options of the first definition (top-only I0, plain I1 atoms). -/
def PureOpt.IsTop : PureOpt n → Prop
  | .one _ => True
  | .zero _ => True
  | .zeroAt _ _ => False
  | .oneAt _ _ => False

/-- A wire that is `1` at `(top_w, 0)` and `0` at every atom `(e_u, 1)` lies in no class of a
`one` / `zero` option. -/
theorem not_mem_top_classes (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) (i : ℕ)
    (h0 : val (lift n p gates) (ext (Zof R) false) i = true)
    (h1 : ∀ c ∈ liftSet R, val (lift n p gates) (atom1 c) i = false) (c : PureOpt n)
    (hc : c.IsTop) : i ∉ pureCls gates p R c := by
  intro hi
  cases c with
  | one Z =>
    obtain ⟨u, hu, h⟩ := pureI1_atom (gates := gates) (p := p) (R := R) (Z := Z) hi
    rw [h1 u hu] at h
    exact absurd h (by decide)
  | zero m =>
    have h := pureI0At_zero (gates := gates) (p := p) (R := R) (z := Zof R) (m := m) hi
    rw [h0] at h
    exact absurd h (by decide)
  | zeroAt z m => exact hc.elim
  | oneAt Z A => exact hc.elim

theorem mem_restrictedMenu_of {gates : List Gate} {p : ℕ} {V R : Finset (Fin n)} {g : ℕ}
    (c : PureOpt n) (hc : RestrValid gates p V R c) (hg : g ∈ restrCls gates p V R c) :
    g ∈ restrictedMenu gates p V R :=
  mem_restrictedMenu.mpr ⟨c, hc, hg⟩

end PureHeredity

/-! ## Witness: with top-only I0 options heredity fails (scaffold's fixh16_20) -/

/-- The restricted I0 atoms of the witness: `m_0 = {0, 2}`, `m_3 = {2, 3}`. -/
def hfM : Fin 4 → Finset (Fin 4) := ![{0, 2}, ∅, ∅, {2, 3}]

/-- `F = {S_1, S_2} = {{0,2}, {0,3}}`, `V = {0, 2, 3}`, `w = 2`, `S_w = {0, 3}`. -/
def hfV : Finset (Fin 4) := {0, 2, 3}

theorem hf_restrValid : RestrValid sdrFixh20Gates 5 hfV (sdrFixh20S 2) (.zero hfM) := by
  refine ⟨⟨by decide, by decide⟩, by decide⟩

set_option maxRecDepth 100000 in
theorem hf_restrCls : restrCls sdrFixh20Gates 5 hfV (sdrFixh20S 2) (.zero hfM) = {9} := by decide

set_option maxRecDepth 100000 in
/-- In the original circuit, the lifted wire `9` (= `h`) is `1` at `(top_w, 0)` and `0` at both atoms
`(e_0, 1)`, `(e_3, 1)`. -/
theorem hf_values : val (lift 4 5 sdrFixh20Gates) (ext (Zof (sdrFixh20S 2)) false) 9 = true ∧
    ∀ c ∈ liftSet (sdrFixh20S 2), val (lift 4 5 sdrFixh20Gates) (atom1 c) 9 = false := by
  decide

theorem hf_mem9 : 9 ∈ restrCls sdrFixh20Gates 5 hfV (sdrFixh20S 2) (.zero hfM) := by
  rw [hf_restrCls]; exact Finset.mem_singleton_self 9

theorem hf_notTop :
    ∀ c : PureOpt 4, c.IsTop → 9 ∉ pureCls sdrFixh20Gates 5 (sdrFixh20S 2) c :=
  not_mem_top_classes sdrFixh20Gates 5 (sdrFixh20S 2) 9 hf_values.1 hf_values.2

/-- **Heredity fails for the top-only options.** The restricted instance of fixh16_20 to
`F = {S_1, S_2}` has, for `w = 2`, a class `{9}` whose wire lies in no class of a `one` / `zero`
option of the original instance (it IS in the original `zeroAt` menu, `restrictedMenu_subset_pureMenu`). -/
theorem heredity_top_fails :
    9 ∈ restrictedMenu sdrFixh20Gates 5 hfV (sdrFixh20S 2) ∧
      ∀ c : PureOpt 4, c.IsTop → 9 ∉ pureCls sdrFixh20Gates 5 (sdrFixh20S 2) c :=
  ⟨@mem_restrictedMenu_of 4 sdrFixh20Gates 5 hfV (sdrFixh20S 2) 9 (.zero hfM) hf_restrValid hf_mem9,
    hf_notTop⟩

end PEqualNP.Outside.L_meta_951_aux
