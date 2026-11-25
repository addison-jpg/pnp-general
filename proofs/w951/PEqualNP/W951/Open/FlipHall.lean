import Mathlib

/-!
# FlipHall: S3(b) for two sets of size at most 3, the function-level core (B5)

S3(b) in Hall form (`research/notes/beyond-one-not.md`): for every family `W` of sets, the flip classes serving
`W` number at least `base(W)`. Notation as in `Open/FlipLemma.lean`: `D(f)` at a zero point `Z` of `S` is
`{u ∈ S : f(Z + e_u) ≠ f(Z)}`; `f` is `S`-thin if `|D(f)| ≤ 1` at every zero point of `S`.

* `dset_orS_le`: the output of a set `T` is thin for every other set `S` with `|S ∩ T| ≤ 1`
  (output classes are private, so Hall holds with `|W|` in place of `base(W)`, and exactly for pairs).
* `const_on_face`: if `±OR(S) = A op B` with `B` `S`-thin, `|S| ≥ 2`, and `A` is not `±OR(S)`, then `A` is
  constant on the zero face of `S`.
* `no_sole_partner`: no function `A` can be the partner of two sets `S`, `T` (`|S|, |T| ≥ 3`,
  `|S ∩ T| ≤ 1`) in this way, the other gate input being thin each time.

The reduction from circuits (the first wire of the output class of a triple is `A op B` with one input
thin when the triple has a single non-output class) is on paper in
`research/one-not/research/open/B5_flip_hall.md`; with it, these give S3(b) for every system of two sets of size
at most 3, for every circuit with any number of NOT gates.
-/

namespace PEqualNP.W951.FlipHall

open Finset

variable {n : ℕ}

/-- the OR of the inputs in `S` -/
def orS (S : Finset (Fin n)) (x : Fin n → Bool) : Bool := decide (∃ u ∈ S, x u = true)

/-- `Z` is a zero point of `S` -/
def IsZero (S : Finset (Fin n)) (Z : Fin n → Bool) : Prop := ∀ u ∈ S, Z u = false

/-- the point `Z + e_u` -/
def flip (Z : Fin n → Bool) (u : Fin n) : Fin n → Bool := Function.update Z u true

/-- `D(f)` at `Z` for the set `S` -/
def dset (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (Z : Fin n → Bool) : Finset (Fin n) :=
  S.filter (fun u => f (flip Z u) ≠ f Z)

/-- `f` is `S`-thin: `|D(f)| ≤ 1` at every zero point of `S` -/
def Thin (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ Z, IsZero S Z → (dset S f Z).card ≤ 1

/-- a binary gate: `true` is OR, `false` is AND -/
def opB (op : Bool) (a b : Bool) : Bool := if op then (a || b) else (a && b)

lemma orS_eq_true_iff (S : Finset (Fin n)) (x : Fin n → Bool) : orS S x = true ↔ ¬ IsZero S x := by
  simp [orS, IsZero]

lemma orS_flip (S : Finset (Fin n)) (Z : Fin n → Bool) {u : Fin n} (hu : u ∈ S) :
    orS S (flip Z u) = true := by
  simp only [orS, decide_eq_true_eq]
  exact ⟨u, hu, by simp [flip]⟩

lemma orS_zero {S : Finset (Fin n)} {Z : Fin n → Bool} (hZ : IsZero S Z) : orS S Z = false := by
  cases h : orS S Z
  · rfl
  · exact absurd hZ ((orS_eq_true_iff S Z).mp h)

lemma isZero_flip {S : Finset (Fin n)} {Z : Fin n → Bool} (hZ : IsZero S Z) {u : Fin n} (hu : u ∉ S) :
    IsZero S (flip Z u) := by
  intro v hv
  have : v ≠ u := fun h => hu (h ▸ hv)
  simp [flip, Function.update_of_ne this, hZ v hv]

lemma not_isZero_flip (S : Finset (Fin n)) (Z : Fin n → Bool) {u : Fin n} (hu : u ∈ S) :
    ¬ IsZero S (flip Z u) := by
  intro h
  have := h u hu
  simp [flip] at this

/-- **Output classes are private.** The output of `T` has `|D| ≤ 1` at every zero point of a set `S`
meeting `T` in at most one point. -/
theorem dset_orS_le (S T : Finset (Fin n)) (hST : (S ∩ T).card ≤ 1) (Z : Fin n → Bool) :
    (dset S (orS T) Z).card ≤ 1 := by
  refine le_trans (card_le_card ?_) hST
  intro u hu
  simp only [dset, mem_filter] at hu
  refine mem_inter.mpr ⟨hu.1, ?_⟩
  by_contra hT
  apply hu.2
  simp only [orS]
  congr 1
  apply propext
  constructor <;> rintro ⟨v, hv, h⟩ <;> refine ⟨v, hv, ?_⟩
  · have : v ≠ u := fun e => hT (e ▸ hv)
    simpa [flip, Function.update_of_ne this] using h
  · have : v ≠ u := fun e => hT (e ▸ hv)
    simpa [flip, Function.update_of_ne this] using h

/-- at a zero point, every point of `S` flips `A` or `B` when `A op B = ±OR(S)` -/
lemma cover (S : Finset (Fin n)) (A B : (Fin n → Bool) → Bool) (op s : Bool)
    (hAB : ∀ x, opB op (A x) (B x) = (orS S x ^^ s)) {Z : Fin n → Bool} (hZ : IsZero S Z) :
    S ⊆ dset S A Z ∪ dset S B Z := by
  intro u hu
  simp only [dset, mem_union, mem_filter]
  by_contra hc
  push Not at hc
  have h1 := hAB (flip Z u)
  have h2 := hAB Z
  rw [hc.1 hu, hc.2 hu, orS_flip S Z hu] at h1
  rw [orS_zero hZ] at h2
  rw [h1] at h2
  cases s <;> simp at h2

/-- a gate input that is constant off the zero face of `S`, next to a thin input, is `±OR(S)` -/
lemma off_face (S : Finset (Fin n)) (hS : 2 ≤ S.card) (A B : (Fin n → Bool) → Bool) (op s c : Bool)
    (hAB : ∀ x, opB op (A x) (B x) = (orS S x ^^ s)) (hB : Thin S B)
    (hoff : ∀ x, ¬ IsZero S x → A x = c) :
    (∀ x, A x = orS S x) ∨ (∀ x, A x = !orS S x) := by
  have hface : ∀ Z, IsZero S Z → A Z = !c := by
    intro Z hZ
    by_contra hne
    have hAZ : A Z = c := by cases c <;> cases h : A Z <;> simp_all
    have hD : dset S A Z = ∅ := by
      apply filter_false_of_mem
      intro u hu
      rw [hoff _ (not_isZero_flip S Z hu), hAZ]
      simp
    have hsub := cover S A B op s hAB hZ
    rw [hD, empty_union] at hsub
    have := card_le_card hsub
    have := hB Z hZ
    simp only [dset] at *
    omega
  cases c
  · right
    intro x
    by_cases hx : IsZero S x
    · rw [hface x hx, orS_zero hx]
    · rw [hoff x hx, (orS_eq_true_iff S x).mpr hx]; rfl
  · left
    intro x
    by_cases hx : IsZero S x
    · rw [hface x hx, orS_zero hx]; rfl
    · rw [hoff x hx, (orS_eq_true_iff S x).mpr hx]

/-- **The partner is constant on the zero face.** If `±OR(S) = A op B`, `B` is `S`-thin, `|S| ≥ 2` and
`A` is not `±OR(S)`, then `A` is constant on the zero face of `S`. -/
theorem const_on_face (S : Finset (Fin n)) (hS : 2 ≤ S.card) (A B : (Fin n → Bool) → Bool)
    (op s : Bool) (hAB : ∀ x, opB op (A x) (B x) = (orS S x ^^ s)) (hB : Thin S B)
    (hA1 : ¬ ∀ x, A x = orS S x) (hA2 : ¬ ∀ x, A x = !orS S x) :
    ∃ c, ∀ Z, IsZero S Z → A Z = c := by
  have notII : ∀ c, ¬ ∀ x, ¬ IsZero S x → A x = c := by
    intro c hoff
    rcases off_face S hS A B op s c hAB hB hoff with h | h
    · exact hA1 h
    · exact hA2 h
  cases op <;> cases s
  · -- AND, +OR(S): A = 1 off the face
    exact absurd (fun x hx => by
      have h := hAB x
      rw [(orS_eq_true_iff S x).mpr hx] at h
      simp only [opB] at h
      cases hA : A x <;> simp_all) (notII true)
  · -- AND, -OR(S): A = 1 on the face
    refine ⟨true, fun Z hZ => ?_⟩
    have h := hAB Z
    rw [orS_zero hZ] at h
    simp only [opB] at h
    cases hA : A Z <;> simp_all
  · -- OR, +OR(S): A = 0 on the face
    refine ⟨false, fun Z hZ => ?_⟩
    have h := hAB Z
    rw [orS_zero hZ] at h
    simp only [opB] at h
    cases hA : A Z <;> simp_all
  · -- OR, -OR(S): A = 0 off the face
    exact absurd (fun x hx => by
      have h := hAB x
      rw [(orS_eq_true_iff S x).mpr hx] at h
      simp only [opB] at h
      cases hA : A x <;> simp_all) (notII false)

/-- **No sole partner for two sets.** Let `|S|, |T| ≥ 3` and `|S ∩ T| ≤ 1`. There is no function `A`
with `±OR(S) = A op B`, `B` `S`-thin, `A` not `±OR(S)`, and `±OR(T) = (±A) op' B'`, `B'` `T`-thin. -/
theorem no_sole_partner (S T : Finset (Fin n)) (hS : 3 ≤ S.card) (hT : 3 ≤ T.card)
    (hST : (S ∩ T).card ≤ 1) (A B B' : (Fin n → Bool) → Bool) (op s op' s' σ : Bool)
    (h1 : ∀ x, opB op (A x) (B x) = (orS S x ^^ s)) (hB : Thin S B)
    (hA1 : ¬ ∀ x, A x = orS S x) (hA2 : ¬ ∀ x, A x = !orS S x)
    (h2 : ∀ x, opB op' (A x ^^ σ) (B' x) = (orS T x ^^ s')) (hB' : Thin T B') : False := by
  obtain ⟨c, hc⟩ := const_on_face S (by omega) A B op s h1 hB hA1 hA2
  set Z0 : Fin n → Bool := fun _ => false with hZ0
  have hzS : IsZero S Z0 := fun _ _ => rfl
  have hzT : IsZero T Z0 := fun _ _ => rfl
  have hcov := cover T (fun x => A x ^^ σ) B' op' s' h2 hzT
  have hsub : dset T (fun x => A x ^^ σ) Z0 ⊆ S ∩ T := by
    intro u hu
    simp only [dset, mem_filter] at hu
    refine mem_inter.mpr ⟨?_, hu.1⟩
    by_contra huS
    apply hu.2
    rw [hc _ (isZero_flip hzS huS), hc _ hzS]
  have hle : T.card ≤ (S ∩ T).card + 1 := by
    calc T.card ≤ (dset T (fun x => A x ^^ σ) Z0 ∪ dset T B' Z0).card := card_le_card hcov
      _ ≤ (dset T (fun x => A x ^^ σ) Z0).card + (dset T B' Z0).card := card_union_le _ _
      _ ≤ (S ∩ T).card + 1 := Nat.add_le_add (card_le_card hsub) (hB' Z0 hzT)
  omega

#print axioms no_sole_partner
#print axioms dset_orS_le

end PEqualNP.W951.FlipHall
