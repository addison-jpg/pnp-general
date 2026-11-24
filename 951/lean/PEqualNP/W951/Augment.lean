import PEqualNP.W951.MergeSDR

/-!
# Augment: `LAvoid ∧ LAugment ⇒ MergeSDR` by descent on the number of colliding pairs

The referee's proof plan for `no_minCE`, with the two open lemmas kept as HYPOTHESES (`Prop`
definitions; nothing here proves them).

## Statements

* `univMergeSet S gates w`: the *universal merges* of set `w`, the gates lying in the merge set
  `mergeSet gates (S w) z` of EVERY zero point `z` of `S w` (`mem_univMergeSet`).
* `AvoidOpt S gates w z`: `z` is an *avoiding option* of `w`: a zero point of `S w` whose merge set
  is disjoint from the universal merges of every other set `w' ≠ w`.
* `LAvoid S gates`: every set has an avoiding option.
* `LAugment S gates`: from any choice `z` of avoiding options with a colliding pair, there are
  `k + 1 ≥ 1` distinct sets `ws 0, …, ws k` (the referee's `w_1 … w_k`, as an injective map on
  `Fin (k + 1)`) and avoiding options `o i` of `ws i` with the referee's (i)-(iv); see the
  docstring of `LAugment` for the exact dictionary.
* `collPairs P`: the unordered colliding pairs of a family `P` of gate sets, as the pairs
  `(a, b)` with `a < b` and `¬ Disjoint (P a) (P b)`. The potential is `Φ = (collPairs P).card`.

## The descent

* `collPairs_card_lt` (pure combinatorics): if a new family `P'` agrees with `P` outside a set
  `W` of indices, has no collision involving an index of `W`, and `P` has a collision touching
  `W`, then `Φ(P') < Φ(P)`.
* `repick_step`: re-picking `z' (ws i) := o i`, all other sets unchanged, keeps a choice of
  avoiding options and strictly lowers `Φ`. It needs only: (i), (iv), and that every new merge
  set is disjoint from the current pick of every set OUTSIDE `W = {ws i}` (`hout`).
* `augment_step`: `LAugment` gives `hout` (from (ii) for `i < k` and (iii) for `i = k`), hence a
  strictly better choice.
* `mergeSDR_of_avoid_augment`: `LAvoid ∧ LAugment ⇒ MergeSDR`, by strong induction on `Φ`. A
  choice with no colliding pair is a `MergeSDR`, because avoiding options are zero points.
* `no_minCE_of_augment`: if every minimal counterexample satisfies `LAvoid ∧ LAugment`, there is
  none (via `no_minCE_of_mergeSDR`).

## Reading of the referee's statement

(ii) is used only through its consequence "the merge set of `o i` is disjoint from the current
pick of every set outside `W`". The chain shape of (ii) (the new merge set of `ws i` may meet the
current pick of `ws (i + 1)`, and nothing is said about the current picks of `ws j`, `j ≤ i`) is
harmless: those sets are all re-picked, and collisions among the new picks are excluded by (iv).
So (i)-(iv) as stated do give the strict decrease, and no extra condition is needed.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- The unordered colliding pairs of a family of gate sets: `a < b` with `P a`, `P b` not
disjoint. The descent potential is the cardinality of this set. -/
def collPairs {m : ℕ} (P : Fin m → Finset ℕ) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ ¬ Disjoint (P p.1) (P p.2)

theorem mem_collPairs {m : ℕ} {P : Fin m → Finset ℕ} {p : Fin m × Fin m} :
    p ∈ collPairs P ↔ p.1 < p.2 ∧ ¬ Disjoint (P p.1) (P p.2) := by
  simp [collPairs]

/-- **Potential drop.** If `P'` agrees with `P` outside `W`, no collision of `P'` involves an
index of `W`, and some collision of `P` touches `W`, then `P'` has strictly fewer colliding
pairs. -/
theorem collPairs_card_lt {m : ℕ} (P P' : Fin m → Finset ℕ) (W : Fin m → Prop)
    (hout : ∀ a, ¬ W a → P' a = P a)
    (hW : ∀ a, W a → ∀ b, b ≠ a → Disjoint (P' a) (P' b))
    (hold : ∃ a, W a ∧ ∃ b, b ≠ a ∧ ¬ Disjoint (P a) (P b)) :
    (collPairs P').card < (collPairs P).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · obtain ⟨a, ha, b, hba, hnd⟩ := hold
    rcases lt_or_gt_of_ne hba with h | h
    · refine ⟨(b, a), mem_collPairs.mpr ⟨h, fun hd => hnd hd.symm⟩, fun hmem => ?_⟩
      exact (mem_collPairs.mp hmem).2 (hW a ha b hba).symm
    · refine ⟨(a, b), mem_collPairs.mpr ⟨h, hnd⟩, fun hmem => ?_⟩
      exact (mem_collPairs.mp hmem).2 (hW a ha b hba)
  · intro p hp
    obtain ⟨hlt, hnd⟩ := mem_collPairs.mp hp
    by_cases h1 : W p.1
    · exact absurd (hW _ h1 _ (ne_of_gt hlt)) hnd
    by_cases h2 : W p.2
    · exact absurd (hW _ h2 _ (ne_of_lt hlt)).symm hnd
    rw [hout _ h1, hout _ h2] at hnd
    exact mem_collPairs.mpr ⟨hlt, hnd⟩

section Augment

variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)

/-- The **universal merges** of set `w`: gates in the merge set of every zero point of `S w`. -/
def univMergeSet (w : Fin m) : Finset ℕ :=
  (Finset.range (n + gates.length)).filter fun g =>
    ∀ z ∈ zeroPts (S w), g ∈ mergeSet gates (S w) z

theorem mem_univMergeSet {w : Fin m} {g : ℕ} :
    g ∈ univMergeSet S gates w ↔ ∀ z ∈ zeroPts (S w), g ∈ mergeSet gates (S w) z := by
  simp only [univMergeSet, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro h
  obtain ⟨z, hz⟩ := zeroPts_nonempty (S w)
  exact (Finset.mem_Ico.mp (mergeSet_subset gates (S w) z (h z hz))).2

/-- `z` is an **avoiding option** of set `w`: a zero point of `S w` whose merge set is disjoint
from the universal merges of every other set. -/
def AvoidOpt (w : Fin m) (z : Fin n → Bool) : Prop :=
  z ∈ zeroPts (S w) ∧
    ∀ w' : Fin m, w' ≠ w → Disjoint (mergeSet gates (S w) z) (univMergeSet S gates w')

/-- **LAvoid** (open; a hypothesis here): every set has an avoiding option. -/
def LAvoid : Prop := ∀ w : Fin m, ∃ z, AvoidOpt S gates w z

/-- **LAugment** (open; a hypothesis here). For every choice `z` of avoiding options with a
colliding pair, there are `k + 1` distinct sets `ws 0, …, ws k` (the referee's `w_1, …, w_k`
with `k ≥ 1`; `ws` injective) and avoiding options `o i` of `ws i` such that, in this order:
* (i) `ws 0` is in a colliding pair of the current choice `z`;
* (ii) for `i < k`, the merge set of `o i` is disjoint from the current pick `z v` of every set
  `v ∉ {ws 0, …, ws i}` with `v ≠ ws (i + 1)`;
* (iii) the merge set of `o k` is disjoint from the current pick of every set outside
  `{ws 0, …, ws k}`;
* (iv) the merge sets of the `o i` are pairwise disjoint. -/
def LAugment : Prop :=
  ∀ z : Fin m → (Fin n → Bool), (∀ w, AvoidOpt S gates w (z w)) →
    (∃ a b : Fin m, a ≠ b ∧
      ¬ Disjoint (mergeSet gates (S a) (z a)) (mergeSet gates (S b) (z b))) →
    ∃ (k : ℕ) (ws : Fin (k + 1) → Fin m) (o : Fin (k + 1) → (Fin n → Bool)),
      Function.Injective ws ∧ (∀ i, AvoidOpt S gates (ws i) (o i)) ∧
      (∃ b, b ≠ ws 0 ∧
        ¬ Disjoint (mergeSet gates (S (ws 0)) (z (ws 0))) (mergeSet gates (S b) (z b))) ∧
      (∀ (i : Fin (k + 1)) (hi : (i : ℕ) < k) (v : Fin m),
        (∀ j : Fin (k + 1), j ≤ i → v ≠ ws j) → v ≠ ws ⟨(i : ℕ) + 1, by omega⟩ →
        Disjoint (mergeSet gates (S (ws i)) (o i)) (mergeSet gates (S v) (z v))) ∧
      (∀ v : Fin m, (∀ j, v ≠ ws j) →
        Disjoint (mergeSet gates (S (ws (Fin.last k))) (o (Fin.last k)))
          (mergeSet gates (S v) (z v))) ∧
      (∀ i j, i ≠ j →
        Disjoint (mergeSet gates (S (ws i)) (o i)) (mergeSet gates (S (ws j)) (o j)))

/-- **Re-pick step.** Given a choice `z` of avoiding options, distinct sets `ws i` with avoiding
options `o i` such that `ws 0` is in a colliding pair of `z` (i), every new merge set is disjoint
from the current pick of every set outside `{ws i}` (`hout`), and the new merge sets are pairwise
disjoint (iv): the re-picked choice (`z' (ws i) = o i`, unchanged elsewhere) is a choice of
avoiding options with strictly fewer colliding pairs. -/
theorem repick_step (z : Fin m → (Fin n → Bool)) (hz : ∀ w, AvoidOpt S gates w (z w))
    {k : ℕ} (ws : Fin (k + 1) → Fin m) (o : Fin (k + 1) → (Fin n → Bool))
    (hinj : Function.Injective ws) (ho : ∀ i, AvoidOpt S gates (ws i) (o i))
    (h1 : ∃ b, b ≠ ws 0 ∧
      ¬ Disjoint (mergeSet gates (S (ws 0)) (z (ws 0))) (mergeSet gates (S b) (z b)))
    (hout : ∀ i v, (∀ j, v ≠ ws j) →
      Disjoint (mergeSet gates (S (ws i)) (o i)) (mergeSet gates (S v) (z v)))
    (h4 : ∀ i j, i ≠ j →
      Disjoint (mergeSet gates (S (ws i)) (o i)) (mergeSet gates (S (ws j)) (o j))) :
    ∃ z' : Fin m → (Fin n → Bool), (∀ w, AvoidOpt S gates w (z' w)) ∧
      (∀ i, z' (ws i) = o i) ∧ (∀ v, (∀ j, v ≠ ws j) → z' v = z v) ∧
      (collPairs fun w => mergeSet gates (S w) (z' w)).card <
        (collPairs fun w => mergeSet gates (S w) (z w)).card := by
  classical
  let z' : Fin m → (Fin n → Bool) := fun v => if h : ∃ i, ws i = v then o h.choose else z v
  have hzW : ∀ i, z' (ws i) = o i := by
    intro i
    show (if h : ∃ j, ws j = ws i then o h.choose else z (ws i)) = o i
    split_ifs with h
    · rw [hinj h.choose_spec]
    · exact absurd ⟨i, rfl⟩ h
  have hzO : ∀ v, (∀ j, v ≠ ws j) → z' v = z v := by
    intro v hv
    show (if h : ∃ j, ws j = v then o h.choose else z v) = z v
    split_ifs with h
    · obtain ⟨j, hj⟩ := h
      exact absurd hj.symm (hv j)
    · rfl
  refine ⟨z', fun v => ?_, hzW, hzO, ?_⟩
  · by_cases h : ∃ i, ws i = v
    · obtain ⟨i, rfl⟩ := h
      rw [hzW]
      exact ho i
    · rw [hzO v fun j hj => h ⟨j, hj.symm⟩]
      exact hz v
  · refine collPairs_card_lt (fun w => mergeSet gates (S w) (z w))
      (fun w => mergeSet gates (S w) (z' w)) (fun v => ∃ i, ws i = v) ?_ ?_ ?_
    · intro a ha
      show mergeSet gates (S a) (z' a) = mergeSet gates (S a) (z a)
      rw [hzO a fun j hj => ha ⟨j, hj.symm⟩]
    · rintro a ⟨i, rfl⟩ b hb
      show Disjoint (mergeSet gates (S (ws i)) (z' (ws i))) (mergeSet gates (S b) (z' b))
      rw [hzW]
      by_cases h : ∃ j, ws j = b
      · obtain ⟨j, rfl⟩ := h
        rw [hzW]
        exact h4 i j fun hij => hb (by rw [hij])
      · rw [hzO b fun j hj => h ⟨j, hj.symm⟩]
        exact hout i b fun j hj => h ⟨j, hj.symm⟩
    · obtain ⟨b, hb, hnd⟩ := h1
      exact ⟨ws 0, ⟨0, rfl⟩, b, hb, hnd⟩

/-- **Augmentation step.** Under `LAugment`, a choice of avoiding options with a colliding pair
can be replaced by one with strictly fewer colliding pairs. -/
theorem augment_step (hA : LAugment S gates) (z : Fin m → (Fin n → Bool))
    (hz : ∀ w, AvoidOpt S gates w (z w))
    (hc : ∃ a b : Fin m, a ≠ b ∧
      ¬ Disjoint (mergeSet gates (S a) (z a)) (mergeSet gates (S b) (z b))) :
    ∃ z' : Fin m → (Fin n → Bool), (∀ w, AvoidOpt S gates w (z' w)) ∧
      (collPairs fun w => mergeSet gates (S w) (z' w)).card <
        (collPairs fun w => mergeSet gates (S w) (z w)).card := by
  obtain ⟨k, ws, o, hinj, ho, h1, h2, h3, h4⟩ := hA z hz hc
  have hout : ∀ i v, (∀ j, v ≠ ws j) →
      Disjoint (mergeSet gates (S (ws i)) (o i)) (mergeSet gates (S v) (z v)) := by
    intro i v hv
    by_cases hi : (i : ℕ) < k
    · exact h2 i hi v (fun j _ => hv j) (hv _)
    · have hil : i = Fin.last k := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
      subst hil
      exact h3 v hv
  obtain ⟨z', hz', -, -, hlt⟩ := repick_step S gates z hz ws o hinj ho h1 hout h4
  exact ⟨z', hz', hlt⟩

/-- **LAvoid ∧ LAugment ⇒ MergeSDR**, by descent on the number of colliding pairs. -/
theorem mergeSDR_of_avoid_augment (hV : LAvoid S gates) (hA : LAugment S gates) :
    MergeSDR S gates := by
  have key : ∀ N : ℕ, ∀ z : Fin m → (Fin n → Bool), (∀ w, AvoidOpt S gates w (z w)) →
      (collPairs fun w => mergeSet gates (S w) (z w)).card = N → MergeSDR S gates := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro z hz hN
      by_cases hc : ∃ a b : Fin m, a ≠ b ∧
          ¬ Disjoint (mergeSet gates (S a) (z a)) (mergeSet gates (S b) (z b))
      · obtain ⟨z', hz', hlt⟩ := augment_step S gates hA z hz hc
        exact ih _ (hN ▸ hlt) z' hz' rfl
      · refine ⟨z, fun w => mem_zeroPts.mp (hz w).1, fun a b hab => ?_⟩
        by_contra hnd
        exact hc ⟨a, b, hab, hnd⟩
  choose z hz using hV
  exact key _ z hz rfl

end Augment

/-- **951 from LAvoid and LAugment**: if every minimal counterexample satisfies both, there is
none. -/
theorem no_minCE_of_augment
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → LAvoid S gates ∧ LAugment S gates) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergeSDR fun n m S gates out M =>
    mergeSDR_of_avoid_augment S gates (H n m S gates out M).1 (H n m S gates out M).2

end PEqualNP.Outside.L_meta_951_aux
