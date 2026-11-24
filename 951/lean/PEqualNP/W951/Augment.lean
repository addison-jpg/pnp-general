import PEqualNP.W951.MergeSDR

/-!
# Augment: `LAvoid ∧ LAugment ⇒ MergeSDR` by descent on the number of colliding pairs

The referee's proof plan for `no_minCE`. `LAvoid` is PROVED (`lAvoid`, zero point `0`; scaffold 10:35); `LAugment` (`Prop`
definitions; nothing here proves them). Without a size bound the loose form is MergeSDR itself
(`mergeSDR_iff_avoid_augmentLoose`, the referee's catch), so the OFFICIAL open target is
`LAvoid ∧ LAugmentK K` with re-picked groups of at most `K` sets (`no_minCE_of_augmentK`; data:
`K = 2` suffices). The chain: `LAugmentK K → LAugmentLoose → (with LAvoid) MergeSDR → no_minCE`; the
referee's `LAugment` implies `LAugmentLoose` (`lAugmentLoose_of_lAugment`).

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

/-- **LAvoid**: every set has an avoiding option. PROVED for every (1,1)-disjoint family: `lAvoid`. -/
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

/-- **LAugmentLoose** (open; the WEAKEST form of the augmenting hypothesis, coord 10:13). For every
choice `z` of avoiding options with a colliding pair there are distinct sets `ws 0, ..., ws k` and
avoiding options `o i` such that (i) `ws 0` is in a colliding pair of `z`, every new merge set misses
the current pick of every set outside `{ws i}`, and (iv) the new merge sets are pairwise disjoint.
The chain shape of the referee's (ii) is dropped: `repick_step` never uses it. -/
def LAugmentLoose : Prop :=
  ∀ z : Fin m → (Fin n → Bool), (∀ w, AvoidOpt S gates w (z w)) →
    (∃ a b : Fin m, a ≠ b ∧
      ¬ Disjoint (mergeSet gates (S a) (z a)) (mergeSet gates (S b) (z b))) →
    ∃ (k : ℕ) (ws : Fin (k + 1) → Fin m) (o : Fin (k + 1) → (Fin n → Bool)),
      Function.Injective ws ∧ (∀ i, AvoidOpt S gates (ws i) (o i)) ∧
      (∃ b, b ≠ ws 0 ∧
        ¬ Disjoint (mergeSet gates (S (ws 0)) (z (ws 0))) (mergeSet gates (S b) (z b))) ∧
      (∀ i v, (∀ j, v ≠ ws j) →
        Disjoint (mergeSet gates (S (ws i)) (o i)) (mergeSet gates (S v) (z v))) ∧
      (∀ i j, i ≠ j →
        Disjoint (mergeSet gates (S (ws i)) (o i)) (mergeSet gates (S (ws j)) (o j)))

/-- The referee's LAugment implies the loose form ((ii) for `i < k` and (iii) give the outside
disjointness). -/
theorem lAugmentLoose_of_lAugment (hA : LAugment S gates) : LAugmentLoose S gates := by
  intro z hz hc
  obtain ⟨k, ws, o, hinj, ho, h1, h2, h3, h4⟩ := hA z hz hc
  refine ⟨k, ws, o, hinj, ho, h1, fun i v hv => ?_, h4⟩
  by_cases hi : (i : ℕ) < k
  · exact h2 i hi v (fun j _ => hv j) (hv _)
  · have hil : i = Fin.last k := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
    subst hil
    exact h3 v hv

/-- One augmentation step under the loose hypothesis. -/
theorem augmentLoose_step (hA : LAugmentLoose S gates) (z : Fin m → (Fin n → Bool))
    (hz : ∀ w, AvoidOpt S gates w (z w))
    (hc : ∃ a b : Fin m, a ≠ b ∧
      ¬ Disjoint (mergeSet gates (S a) (z a)) (mergeSet gates (S b) (z b))) :
    ∃ z' : Fin m → (Fin n → Bool), (∀ w, AvoidOpt S gates w (z' w)) ∧
      (collPairs fun w => mergeSet gates (S w) (z' w)).card <
        (collPairs fun w => mergeSet gates (S w) (z w)).card := by
  obtain ⟨k, ws, o, hinj, ho, h1, hout, h4⟩ := hA z hz hc
  obtain ⟨z', hz', -, -, hlt⟩ := repick_step S gates z hz ws o hinj ho h1 hout h4
  exact ⟨z', hz', hlt⟩

/-- **Augmentation step.** Under `LAugment`, a choice of avoiding options with a colliding pair
can be replaced by one with strictly fewer colliding pairs. -/
theorem augment_step (hA : LAugment S gates) (z : Fin m → (Fin n → Bool))
    (hz : ∀ w, AvoidOpt S gates w (z w))
    (hc : ∃ a b : Fin m, a ≠ b ∧
      ¬ Disjoint (mergeSet gates (S a) (z a)) (mergeSet gates (S b) (z b))) :
    ∃ z' : Fin m → (Fin n → Bool), (∀ w, AvoidOpt S gates w (z' w)) ∧
      (collPairs fun w => mergeSet gates (S w) (z' w)).card <
        (collPairs fun w => mergeSet gates (S w) (z w)).card :=
  augmentLoose_step S gates (lAugmentLoose_of_lAugment S gates hA) z hz hc

/-- **LAvoid ∧ LAugmentLoose ⇒ MergeSDR**, by descent on the number of colliding pairs. -/
theorem mergeSDR_of_avoid_augmentLoose (hV : LAvoid S gates) (hA : LAugmentLoose S gates) :
    MergeSDR S gates := by
  have key : ∀ N : ℕ, ∀ z : Fin m → (Fin n → Bool), (∀ w, AvoidOpt S gates w (z w)) →
      (collPairs fun w => mergeSet gates (S w) (z w)).card = N → MergeSDR S gates := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro z hz hN
      by_cases hc : ∃ a b : Fin m, a ≠ b ∧
          ¬ Disjoint (mergeSet gates (S a) (z a)) (mergeSet gates (S b) (z b))
      · obtain ⟨z', hz', hlt⟩ := augmentLoose_step S gates hA z hz hc
        exact ih _ (hN ▸ hlt) z' hz' rfl
      · refine ⟨z, fun w => mem_zeroPts.mp (hz w).1, fun a b hab => ?_⟩
        by_contra hnd
        exact hc ⟨a, b, hab, hnd⟩
  choose z hz using hV
  exact key _ z hz rfl

/-! ### The size bound is the content (referee's catch, coord 10:14) -/

/-- The points of a MergeSDR are avoiding options: another set's universal merges lie inside its
own SDR merge set, which is disjoint from this one. -/
theorem avoidOpt_of_sdr (z : Fin m → (Fin n → Bool)) (hz : ∀ w, ∀ v ∈ S w, z w v = false)
    (hd : ∀ a b : Fin m, a ≠ b →
      Disjoint (mergeSet gates (S a) (z a)) (mergeSet gates (S b) (z b))) (w : Fin m) :
    AvoidOpt S gates w (z w) := by
  refine ⟨mem_zeroPts.mpr (hz w), fun w' hw' => (hd w w' (Ne.symm hw')).mono_right ?_⟩
  intro g hg
  exact (mem_univMergeSet S gates).mp hg (z w') (mem_zeroPts.mpr (hz w'))

theorem lAvoid_of_mergeSDR (h : MergeSDR S gates) : LAvoid S gates := by
  obtain ⟨z, hz, hd⟩ := h
  exact fun w => ⟨z w, avoidOpt_of_sdr S gates z hz hd w⟩

/-- **Without a size bound the loose hypothesis is MergeSDR itself**: from a MergeSDR, re-pick ALL
sets (listed starting with a colliding one) at their SDR points. -/
theorem lAugmentLoose_of_mergeSDR (h : MergeSDR S gates) : LAugmentLoose S gates := by
  obtain ⟨zs, hzs, hds⟩ := h
  rintro z - ⟨a, b, hab, hnd⟩
  have hm : m - 1 + 1 = m := by have := a.2; omega
  let σ : Equiv.Perm (Fin m) := Equiv.swap (Fin.cast hm 0) a
  let ws : Fin (m - 1 + 1) → Fin m := fun i => σ (Fin.cast hm i)
  have hws_inj : Function.Injective ws := fun i j hij =>
    Fin.cast_injective hm (σ.injective hij)
  have hws_surj : ∀ v, ∃ j, ws j = v := fun v =>
    ⟨Fin.cast hm.symm (σ.symm v), by simp [ws]⟩
  refine ⟨m - 1, ws, fun i => zs (ws i), hws_inj,
    fun i => avoidOpt_of_sdr S gates zs hzs hds (ws i), ⟨b, ?_, ?_⟩, fun i v hv => ?_,
    fun i j hij => hds _ _ (fun h => hij (hws_inj h))⟩
  · have h0 : ws 0 = a := by simp [ws, σ]
    rw [h0]
    exact Ne.symm hab
  · have h0 : ws 0 = a := by simp [ws, σ]
    rw [h0]
    exact hnd
  · obtain ⟨j, hj⟩ := hws_surj v
    exact absurd hj.symm (hv j)

/-- **MergeSDR ⇔ LAvoid ∧ LAugmentLoose** (referee): the unbounded loose form adds nothing. -/
theorem mergeSDR_iff_avoid_augmentLoose :
    MergeSDR S gates ↔ LAvoid S gates ∧ LAugmentLoose S gates :=
  ⟨fun h => ⟨lAvoid_of_mergeSDR S gates h, lAugmentLoose_of_mergeSDR S gates h⟩,
    fun h => mergeSDR_of_avoid_augmentLoose S gates h.1 h.2⟩

/-- **LAugmentK K** (open; the OFFICIAL target, with the size bound that carries the content):
`LAugmentLoose` with re-picked groups of at most `K` sets. Data (scaffold, via coord 10:14; not
checked here): `K = 2` suffices on all 75,619 circuits of the corpus, and `K = 1` in 100,116 of the
100,174 collision states. -/
def LAugmentK (K : ℕ) : Prop :=
  ∀ z : Fin m → (Fin n → Bool), (∀ w, AvoidOpt S gates w (z w)) →
    (∃ a b : Fin m, a ≠ b ∧
      ¬ Disjoint (mergeSet gates (S a) (z a)) (mergeSet gates (S b) (z b))) →
    ∃ (k : ℕ) (ws : Fin (k + 1) → Fin m) (o : Fin (k + 1) → (Fin n → Bool)), k + 1 ≤ K ∧
      Function.Injective ws ∧ (∀ i, AvoidOpt S gates (ws i) (o i)) ∧
      (∃ b, b ≠ ws 0 ∧
        ¬ Disjoint (mergeSet gates (S (ws 0)) (z (ws 0))) (mergeSet gates (S b) (z b))) ∧
      (∀ i v, (∀ j, v ≠ ws j) →
        Disjoint (mergeSet gates (S (ws i)) (o i)) (mergeSet gates (S v) (z v))) ∧
      (∀ i j, i ≠ j →
        Disjoint (mergeSet gates (S (ws i)) (o i)) (mergeSet gates (S (ws j)) (o j)))

theorem lAugmentLoose_of_lAugmentK (K : ℕ) (h : LAugmentK S gates K) : LAugmentLoose S gates := by
  intro z hz hc
  obtain ⟨k, ws, o, -, rest⟩ := h z hz hc
  exact ⟨k, ws, o, rest⟩

/-- A larger bound is weaker. -/
theorem lAugmentK_mono {K K' : ℕ} (hKK : K ≤ K') (h : LAugmentK S gates K) :
    LAugmentK S gates K' := by
  intro z hz hc
  obtain ⟨k, ws, o, hk, rest⟩ := h z hz hc
  exact ⟨k, ws, o, hk.trans hKK, rest⟩

/-- **LAvoid ∧ LAugmentK K ⇒ MergeSDR.** -/
theorem mergeSDR_of_avoid_augmentK (K : ℕ) (hV : LAvoid S gates) (hA : LAugmentK S gates K) :
    MergeSDR S gates :=
  mergeSDR_of_avoid_augmentLoose S gates hV (lAugmentLoose_of_lAugmentK S gates K hA)

/-! ### Moves only along reachable states (951/PROOF_PLAN_SUGGESTIONS.md, rule 4) -/

open Classical in
/-- An **improving move** of at most `K` sets: `z'` is a choice of avoiding options that differs from
`z` on at most `K` sets and has strictly fewer colliding pairs. -/
def ImprovingMove (K : ℕ) (z z' : Fin m → (Fin n → Bool)) : Prop :=
  (∀ w, AvoidOpt S gates w (z' w)) ∧ (Finset.univ.filter fun w => z' w ≠ z w).card ≤ K ∧
    (collPairs fun w => mergeSet gates (S w) (z' w)).card <
      (collPairs fun w => mergeSet gates (S w) (z w)).card

/-- The states reachable from `z0` by improving moves of at most `K` sets. -/
inductive Reach (K : ℕ) (z0 : Fin m → (Fin n → Bool)) : (Fin m → (Fin n → Bool)) → Prop
  | refl : Reach K z0 z0
  | step {z z' : Fin m → (Fin n → Bool)} : Reach K z0 z → ImprovingMove S gates K z z' →
      Reach K z0 z'

/-- **LAugmentReach K** (open; weaker than `LAvoid ∧ LAugmentK K`): there is a start `z0` of
avoiding options such that every state reachable from it by improving moves of at most `K` sets
that still has a colliding pair admits a further such move. Only the visited states matter, so a
proof may use a canonical start (PROOF_PLAN_SUGGESTIONS.md §3). -/
def LAugmentReach (K : ℕ) : Prop :=
  ∃ z0 : Fin m → (Fin n → Bool), (∀ w, AvoidOpt S gates w (z0 w)) ∧
    ∀ z, Reach S gates K z0 z →
      (∃ a b : Fin m, a ≠ b ∧
        ¬ Disjoint (mergeSet gates (S a) (z a)) (mergeSet gates (S b) (z b))) →
      ∃ z', ImprovingMove S gates K z z'

theorem reach_avoid {K : ℕ} {z0 z : Fin m → (Fin n → Bool)} (h0 : ∀ w, AvoidOpt S gates w (z0 w))
    (h : Reach S gates K z0 z) : ∀ w, AvoidOpt S gates w (z w) := by
  induction h with
  | refl => exact h0
  | step _ hm _ => exact hm.1

/-- **LAugmentReach K ⇒ MergeSDR**, by descent on the number of colliding pairs along reachable
states. -/
theorem mergeSDR_of_augmentReach (K : ℕ) (h : LAugmentReach S gates K) : MergeSDR S gates := by
  obtain ⟨z0, h0, hstep⟩ := h
  have key : ∀ N : ℕ, ∀ z, Reach S gates K z0 z →
      (collPairs fun w => mergeSet gates (S w) (z w)).card = N → MergeSDR S gates := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro z hz hN
      by_cases hc : ∃ a b : Fin m, a ≠ b ∧
          ¬ Disjoint (mergeSet gates (S a) (z a)) (mergeSet gates (S b) (z b))
      · obtain ⟨z', hm⟩ := hstep z hz hc
        exact ih _ (hN ▸ hm.2.2) z' (Reach.step hz hm) rfl
      · refine ⟨z, fun w => mem_zeroPts.mp (reach_avoid S gates h0 hz w).1, fun a b hab => ?_⟩
        by_contra hnd
        exact hc ⟨a, b, hab, hnd⟩
  exact key _ z0 Reach.refl rfl

/-- `LAvoid ∧ LAugmentK K ⇒ LAugmentReach K`: the reachable form is the weaker target. -/
theorem lAugmentReach_of_avoid_augmentK (K : ℕ) (hV : LAvoid S gates)
    (hA : LAugmentK S gates K) : LAugmentReach S gates K := by
  classical
  choose z0 hz0 using hV
  refine ⟨z0, hz0, fun z hz hc => ?_⟩
  have hav := reach_avoid S gates hz0 hz
  obtain ⟨k, ws, o, hk, hinj, ho, h1, hout, h4⟩ := hA z hav hc
  obtain ⟨z', hz', -, hsame, hlt⟩ := repick_step S gates z hav ws o hinj ho h1 hout h4
  refine ⟨z', hz', ?_, hlt⟩
  have hsub : (Finset.univ.filter fun w => z' w ≠ z w) ⊆ Finset.univ.image ws := by
    intro w hw
    rw [Finset.mem_filter] at hw
    by_contra hni
    exact hw.2 (hsame w fun j hj => hni (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩))
  calc (Finset.univ.filter fun w => z' w ≠ z w).card ≤ (Finset.univ.image ws).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin (k + 1))).card := Finset.card_image_le
    _ = k + 1 := by simp
    _ ≤ K := hk

/-- **LAvoid ∧ LAugment ⇒ MergeSDR** (the referee's form, through `lAugmentLoose_of_lAugment`). -/
theorem mergeSDR_of_avoid_augment (hV : LAvoid S gates) (hA : LAugment S gates) :
    MergeSDR S gates :=
  mergeSDR_of_avoid_augmentLoose S gates hV (lAugmentLoose_of_lAugment S gates hA)

/-- **LAvoid is PROVED** (scaffold 10:35; any circuit, no minimality): the zero point `0` is an
avoiding option of every set. A gate in the merge set of `S w` at `0` is true at two units
`e_u, e_v` of `S w`; a universal merge of `w' ≠ w` vanishes at every unit `e_x` with `x ∉ S w'`
(those are zero points of `S w'`), so `u, v ∈ S w ∩ S w'`, against `|S w ∩ S w'| ≤ 1`.
The argument of `univMerge_disjoint`, with `S w` used only at the zero point `0`. -/
theorem avoidOpt_zero (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) (w : Fin m) :
    AvoidOpt S gates w (fun _ => false) := by
  classical
  refine ⟨by simp [mem_zeroPts], fun w' hw' => Finset.disjoint_left.mpr fun g hg hg' => ?_⟩
  have hb := (mem_univMergeSet S gates).mp hg'
  set z0 : Fin n → Bool := fun _ => false with hz0
  have h0 := mergeSet_subset_DT gates (S w) z0 hg
  simp only [DT, Finset.mem_filter] at h0
  obtain ⟨-, -, u, v, huv, hu, hv, hgu, hgv⟩ := h0
  have key : ∀ x, val gates (upPt z0 x) g = true → x ∈ S w' := by
    intro x hx
    by_contra hxb
    have hz : upPt z0 x ∈ zeroPts (S w') := by
      rw [mem_zeroPts]
      intro c hc
      have hne : c ≠ x := fun h => hxb (h ▸ hc)
      simp [upPt, Function.update_of_ne hne, hz0]
    have h1 := mergeSet_subset_DT gates (S w') _ (hb _ hz)
    simp only [DT, Finset.mem_filter] at h1
    rw [h1.2.1] at hx
    exact absurd hx (by simp)
  have h2 : ({u, v} : Finset (Fin n)) ⊆ S w ∩ S w' := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hu, key _ hgu⟩
    · exact Finset.mem_inter.mpr ⟨hv, key _ hgv⟩
  have h3 := Finset.card_le_card h2
  rw [Finset.card_pair huv] at h3
  have := hS w w' (Ne.symm hw')
  omega

/-- **LAvoid** holds for every (1,1)-disjoint family (`avoidOpt_zero`). -/
theorem lAvoid (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) : LAvoid S gates :=
  fun w => ⟨_, avoidOpt_zero S gates hS w⟩

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

/-- **951 from LAvoid and LAugmentLoose** (the weakest form, the official open target): if every
minimal counterexample satisfies both, there is none. -/
theorem no_minCE_of_augmentLoose
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → LAvoid S gates ∧ LAugmentLoose S gates) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergeSDR fun n m S gates out M =>
    mergeSDR_of_avoid_augmentLoose S gates (H n m S gates out M).1 (H n m S gates out M).2

/-- **951 from LAvoid and LAugmentK K** (the OFFICIAL open target, for a fixed bound `K`; data:
`K = 2`). -/
theorem no_minCE_of_augmentK (K : ℕ)
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → LAvoid S gates ∧ LAugmentK S gates K) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergeSDR fun n m S gates out M =>
    mergeSDR_of_avoid_augmentK S gates K (H n m S gates out M).1 (H n m S gates out M).2

/-- **951 from LAugmentReach K** (PROOF_PLAN rule 4: improving moves only along reachable states). -/
theorem no_minCE_of_augmentReach (K : ℕ)
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → LAugmentReach S gates K) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergeSDR fun n m S gates out M =>
    mergeSDR_of_augmentReach S gates K (H n m S gates out M)

/-- **951 from LAugmentK K alone** (`LAvoid` is proved: `lAvoid`). The open target is now only the
augmentation step. -/
theorem no_minCE_of_augmentK_only (K : ℕ)
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → LAugmentK S gates K) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_augmentK K fun n m S gates out M =>
    ⟨lAvoid S gates M.ce.hS, H n m S gates out M⟩

end PEqualNP.Outside.L_meta_951_aux
