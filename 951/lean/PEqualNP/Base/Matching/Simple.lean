import PEqualNP.Base.Matching.Hall

/-!
# Simple b-matchings (integral max-flow/min-cut for a bipartite network)

Helper module (proofs only). A *simple* b-matching is a b-matching in which every vertex uses
every item at most once.

* `HasSimpleBMatching t d c`: a b-matching whose slots of one vertex go to distinct items.
* `hasSimpleBMatching_iff`: it exists exactly when, for every finite set `s` of vertices,
  `∑ i ∈ s, d i ≤ ∑ a ∈ s.biUnion t, min (c a) #{i ∈ s | a ∈ t i}`.
  Proof: Tutte's gadget. The edges `(i, a)` with `a ∈ t i` are matched, by Mathlib's Hall theorem,
  into the copies of `a` together with `#(t i) - d i` "unused" tokens of `i`.
* `hasSimpleBMatching_one_iff`: with every capacity `1`, simple and plain b-matchings agree.
* `hasSimpleBMatching_const_iff`, `hasSimpleBMatching_sigmaProd_iff`,
  `exists_simple_injective_sigmaProd_iff_hall`: constant capacity (target `α × Fin c`) and slots
  `Σ w, κ × Fin (d w)`, the shape of W951's `MatchG2`.
* `HasSimpleBMatching.exists_image_props`: a simple b-matching of constant capacity is a
  fractional matching with weights `1 / c`.
-/

namespace PEqualNP.Base.Matching

open Finset

variable {ι α : Type*} [DecidableEq α]

/-- A simple b-matching: a b-matching in which the slots of one vertex go to distinct items. -/
def HasSimpleBMatching (t : ι → Finset α) (d : ι → ℕ) (c : α → ℕ) : Prop :=
  ∃ f : (Σ i, Fin (d i)) → (Σ a, Fin (c a)), Function.Injective f ∧ (∀ x, (f x).1 ∈ t x.1) ∧
    ∀ i, Function.Injective fun k : Fin (d i) => (f ⟨i, k⟩).1

omit [DecidableEq α] in
theorem HasSimpleBMatching.hasBMatching {t : ι → Finset α} {d : ι → ℕ} {c : α → ℕ}
    (h : HasSimpleBMatching t d c) : HasBMatching t d c :=
  let ⟨f, hf, hft, _⟩ := h
  ⟨f, hf, hft⟩

/-- The easy direction: a simple b-matching gives the cut inequality for every `s`. -/
theorem HasSimpleBMatching.sum_le {t : ι → Finset α} {d : ι → ℕ} {c : α → ℕ}
    (h : HasSimpleBMatching t d c) (s : Finset ι) :
    ∑ i ∈ s, d i ≤ ∑ a ∈ s.biUnion t, min (c a) (s.filter (fun i => a ∈ t i)).card := by
  classical
  obtain ⟨f, hf, hft, hinj⟩ := h
  have hS : (s.sigma fun i => (univ : Finset (Fin (d i)))).card = ∑ i ∈ s, d i := by
    simp [card_sigma]
  have hmaps : ∀ x ∈ s.sigma fun i => (univ : Finset (Fin (d i))), (f x).1 ∈ s.biUnion t :=
    fun x hx => mem_biUnion.2 ⟨x.1, (mem_sigma.1 hx).1, hft x⟩
  rw [← hS, card_eq_sum_card_fiberwise hmaps]
  refine sum_le_sum fun a _ => le_min ?_ ?_
  · have hc : (blow c {a}).card = c a := by simp [card_blow]
    rw [← hc]
    refine card_le_card_of_injOn f ?_ hf.injOn
    intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq] at hx
    simp only [mem_coe]
    rw [mem_blow]
    simp [hx.2]
  · refine card_le_card_of_injOn Sigma.fst ?_ ?_
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq, mem_sigma] at hx
      simp only [mem_coe, mem_filter]
      exact ⟨hx.1.1, hx.2 ▸ hft x⟩
    · rintro ⟨i, k⟩ hx ⟨i', k'⟩ hy (hii : i = i')
      subst hii
      simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
      have : k = k' := hinj i (hx.2.trans hy.2.symm)
      rw [this]

/-- The Hall count for Tutte's gadget. -/
private theorem gadget_count (t : ι → Finset α) (d : ι → ℕ) (c : α → ℕ)
    (h : ∀ s : Finset ι,
      ∑ i ∈ s, d i ≤ ∑ a ∈ s.biUnion t, min (c a) (s.filter (fun i => a ∈ t i)).card)
    (hdt : ∀ i, d i ≤ (t i).card) [DecidableEq ι]
    (X : Finset (Σ i, {a // a ∈ t i})) :
    X.card ≤ ∑ a ∈ X.image (fun e => e.2.1), c a
      + ∑ i ∈ X.image Sigma.fst, ((t i).card - d i) := by
  set s := X.image Sigma.fst with hs
  set H := X.image (fun e : (Σ i, {a // a ∈ t i}) => e.2.1) with hH
  set U := s.biUnion t with hU
  have hmaps : ∀ e ∈ X, (fun e : (Σ i, {a // a ∈ t i}) => e.2.1) e ∈ U := fun e he =>
    mem_biUnion.2 ⟨e.1, mem_image_of_mem _ he, e.2.2⟩
  have hHU : H ⊆ U := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := mem_image.1 ha
    exact hmaps e he
  have hX := card_eq_sum_card_fiberwise hmaps
  -- double counting
  have hdc : ∑ i ∈ s, (t i).card = ∑ a ∈ U, (s.filter (fun i => a ∈ t i)).card := by
    have h1 : ∀ i ∈ s, (t i).card = ∑ a ∈ U, if a ∈ t i then 1 else 0 := by
      intro i hi
      rw [← sum_filter, ← card_eq_sum_ones]
      congr 1
      ext a
      simp only [mem_filter, hU, mem_biUnion]
      exact ⟨fun ha => ⟨⟨i, hi, ha⟩, ha⟩, fun ha => ha.2⟩
    rw [sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [card_filter]
  have hsub : ∑ i ∈ s, ((t i).card - d i) + ∑ i ∈ s, d i = ∑ i ∈ s, (t i).card := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => Nat.sub_add_cancel (hdt i)
  have hHsum : ∑ a ∈ H, c a = ∑ a ∈ U, if a ∈ H then c a else 0 := by
    rw [← sum_filter]
    congr 1
    ext a
    simp only [mem_filter]
    exact ⟨fun ha => ⟨hHU ha, ha⟩, fun ha => ha.2⟩
  have hpt : ∀ a ∈ U, (X.filter (fun e => e.2.1 = a)).card
      + min (c a) (s.filter (fun i => a ∈ t i)).card
      ≤ (if a ∈ H then c a else 0) + (s.filter (fun i => a ∈ t i)).card := by
    intro a _
    have hdeg : (X.filter (fun e => e.2.1 = a)).card ≤ (s.filter (fun i => a ∈ t i)).card := by
      refine card_le_card_of_injOn Sigma.fst ?_ ?_
      · intro e he
        simp only [coe_filter, Set.mem_ofPred_eq] at he
        simp only [mem_coe, mem_filter]
        exact ⟨mem_image_of_mem _ he.1, he.2 ▸ e.2.2⟩
      · rintro ⟨i, a1, h1⟩ hx ⟨i', a2, h2⟩ hy (hii : i = i')
        subst hii
        simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
        obtain rfl : a1 = a2 := hx.2.trans hy.2.symm
        rfl
    by_cases haH : a ∈ H
    · simp only [haH, ite_true]
      have := min_le_left (c a) (s.filter (fun i => a ∈ t i)).card
      omega
    · simp only [haH, ite_false]
      have h0 : (X.filter (fun e => e.2.1 = a)).card = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro e he hea
        exact haH (mem_image.2 ⟨e, he, hea⟩)
      have := min_le_right (c a) (s.filter (fun i => a ∈ t i)).card
      omega
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, sum_add_distrib, ← hX, ← hHsum, ← hdc] at hsum
  have hh : ∑ i ∈ s, d i ≤ ∑ a ∈ U, min (c a) (s.filter (fun i => a ∈ t i)).card := h s
  omega

/-- **Hall's theorem for simple b-matchings** (integral max-flow/min-cut for the bipartite
network `source → i` (capacity `d i`), `i → a` for `a ∈ t i` (capacity `1`), `a → sink`
(capacity `c a`)). -/
theorem hasSimpleBMatching_iff (t : ι → Finset α) (d : ι → ℕ) (c : α → ℕ) :
    HasSimpleBMatching t d c ↔ ∀ s : Finset ι,
      ∑ i ∈ s, d i ≤ ∑ a ∈ s.biUnion t, min (c a) (s.filter (fun i => a ∈ t i)).card := by
  classical
  refine ⟨fun h s => h.sum_le s, fun h => ?_⟩
  have hdt : ∀ i, d i ≤ (t i).card := by
    intro i
    have h1 := h {i}
    rw [sum_singleton, singleton_biUnion] at h1
    refine h1.trans ?_
    rw [card_eq_sum_ones]
    refine sum_le_sum fun a _ => (min_le_right _ _).trans ?_
    exact (card_filter_le _ _).trans (by simp)
  -- Tutte's gadget
  let N : (Σ i, {a // a ∈ t i}) →
      Finset ((Σ a, Fin (c a)) ⊕ (Σ i, Fin ((t i).card - d i))) := fun e =>
    (blow c {e.2.1}).disjSum
      (({e.1} : Finset ι).sigma fun i => (univ : Finset (Fin ((t i).card - d i))))
  have key : ∀ X : Finset (Σ i, {a // a ∈ t i}), X.biUnion N =
      (blow c (X.image fun e => e.2.1)).disjSum
        ((X.image Sigma.fst).sigma fun i => (univ : Finset (Fin ((t i).card - d i)))) := by
    intro X
    ext y
    rcases y with y | y
    · simp only [N, mem_biUnion, inl_mem_disjSum, mem_blow, mem_singleton, mem_image]
      constructor
      · rintro ⟨e, he, hy⟩
        exact ⟨e, he, hy.symm⟩
      · rintro ⟨e, he, hy⟩
        exact ⟨e, he, hy.symm⟩
    · simp only [N, mem_biUnion, inr_mem_disjSum, mem_sigma, mem_singleton, mem_univ, and_true,
        mem_image]
      constructor
      · rintro ⟨e, he, hy⟩
        exact ⟨e, he, hy.symm⟩
      · rintro ⟨e, he, hy⟩
        exact ⟨e, he, hy.symm⟩
  have hall : ∀ X : Finset (Σ i, {a // a ∈ t i}), X.card ≤ (X.biUnion N).card := by
    intro X
    rw [key, card_disjSum, card_blow, card_sigma]
    simpa using gadget_count t d c h hdt X
  obtain ⟨g, hg, hgN⟩ := (all_card_le_biUnion_card_iff_exists_injective N).1 hall
  -- every vertex has at least `d i` edges matched to item copies
  have hused : ∀ i, ∃ e : Fin (d i) → {a // a ∈ t i}, Function.Injective e ∧
      ∀ k, ∃ y, g ⟨i, e k⟩ = Sum.inl y := by
    intro i
    have hun : ((univ : Finset {a // a ∈ t i}).filter
        (fun a => ¬ (g ⟨i, a⟩).isLeft)).card ≤ (t i).card - d i := by
      calc _ ≤ ((univ : Finset (Fin ((t i).card - d i))).image
              (fun k => (Sum.inr ⟨i, k⟩ : (Σ a, Fin (c a)) ⊕ (Σ i, Fin ((t i).card - d i))))).card := by
            refine card_le_card_of_injOn (fun a => g ⟨i, a⟩) ?_ ?_
            · intro a ha
              simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at ha
              have hm := hgN ⟨i, a⟩
              rcases hy : g ⟨i, a⟩ with y | ⟨j, k⟩
              · rw [hy] at ha; simp at ha
              · rw [hy] at hm
                simp only [N, inr_mem_disjSum, mem_sigma, mem_singleton, mem_univ, and_true] at hm
                change j = i at hm
                subst hm
                exact mem_image.2 ⟨k, mem_univ _, hy.symm⟩
            · intro a _ b _ hab
              have := hg hab
              simpa using this
        _ ≤ _ := card_image_le.trans (by simp)
    have htot := card_filter_add_card_filter_not (s := (univ : Finset {a // a ∈ t i}))
      (fun a => (g ⟨i, a⟩).isLeft)
    have hcard : (univ : Finset {a // a ∈ t i}).card = (t i).card := by simp
    have hge : d i ≤ ((univ : Finset {a // a ∈ t i}).filter
        (fun a => (g ⟨i, a⟩).isLeft)).card := by
      have := hdt i
      omega
    obtain ⟨V, hV, hVc⟩ := exists_subset_card_eq hge
    refine ⟨fun k => ((V.equivFinOfCardEq hVc).symm k).1, fun k k' hkk => ?_, fun k => ?_⟩
    · exact (V.equivFinOfCardEq hVc).symm.injective (Subtype.ext hkk)
    · have := hV ((V.equivFinOfCardEq hVc).symm k).2
      simp only [mem_filter, mem_univ, true_and] at this
      exact Sum.isLeft_iff.1 this
  choose e he hy using hused
  choose y hy using hy
  have hfst : ∀ i k, (y i k).1 = (e i k).1 := by
    intro i k
    have hm := hgN ⟨i, e i k⟩
    rw [hy] at hm
    simp only [N, inl_mem_disjSum, mem_blow, mem_singleton] at hm
    exact hm
  refine ⟨fun x => y x.1 x.2, ?_, ?_, ?_⟩
  · rintro ⟨i, k⟩ ⟨i', k'⟩ hxy
    have h1 : g ⟨i, e i k⟩ = g ⟨i', e i' k'⟩ := by
      rw [hy, hy]; exact congrArg Sum.inl hxy
    have h2 := hg h1
    obtain rfl : i = i' := congrArg Sigma.fst h2
    have h3 : e i k = e i k' := by simpa using h2
    rw [he i h3]
  · rintro ⟨i, k⟩
    change (y i k).1 ∈ t i
    rw [hfst]
    exact (e i k).2
  · intro i k k' hkk
    change (y i k).1 = (y i k').1 at hkk
    rw [hfst, hfst] at hkk
    exact he i (Subtype.ext hkk)

omit [DecidableEq α] in
/-- With every capacity `1`, a b-matching is automatically simple. -/
theorem hasSimpleBMatching_one_iff (t : ι → Finset α) (d : ι → ℕ) :
    HasSimpleBMatching t d (fun _ => 1) ↔ HasBMatching t d (fun _ => 1) := by
  refine ⟨fun h => h.hasBMatching, ?_⟩
  rintro ⟨f, hf, hft⟩
  refine ⟨f, hf, hft, fun i k k' hkk => ?_⟩
  have h1 : f ⟨i, k⟩ = f ⟨i, k'⟩ := Sigma.ext hkk (heq_of_eq (Subsingleton.elim _ _))
  simpa using hf h1

omit [DecidableEq α] in
/-- With a constant capacity `c`, the copies of the items are `α × Fin c`. -/
theorem hasSimpleBMatching_const_iff (t : ι → Finset α) (d : ι → ℕ) (c : ℕ) :
    HasSimpleBMatching t d (fun _ => c) ↔
      ∃ f : (Σ i, Fin (d i)) → α × Fin c, Function.Injective f ∧ (∀ x, (f x).1 ∈ t x.1) ∧
        ∀ i, Function.Injective fun k : Fin (d i) => (f ⟨i, k⟩).1 :=
  ⟨fun ⟨f, hf, hft, hloc⟩ => ⟨fun x => Equiv.sigmaEquivProd α (Fin c) (f x),
      (Equiv.injective _).comp hf, hft, hloc⟩,
    fun ⟨f, hf, hft, hloc⟩ => ⟨fun x => (Equiv.sigmaEquivProd α (Fin c)).symm (f x),
      (Equiv.injective _).comp hf, hft, hloc⟩⟩

omit [DecidableEq α] in
/-- Constant capacity, vertices `(w, j)` with demand `d w`: the slots are `Σ w, κ × Fin (d w)`.
This is the shape of W951's `MatchG2` (`κ = Fin 2`, `c = 2`). -/
theorem hasSimpleBMatching_sigmaProd_iff {κ : Type*} (t : ι → κ → Finset α) (d : ι → ℕ)
    (c : ℕ) :
    HasSimpleBMatching (fun i : ι × κ => t i.1 i.2) (fun i => d i.1) (fun _ => c) ↔
      ∃ f : (Σ w : ι, κ × Fin (d w)) → α × Fin c, Function.Injective f ∧
        (∀ x, (f x).1 ∈ t x.1 x.2.1) ∧
        ∀ w j, Function.Injective fun k : Fin (d w) => (f ⟨w, (j, k)⟩).1 := by
  rw [hasSimpleBMatching_const_iff]
  exact ⟨fun ⟨f, hf, hft, hloc⟩ => ⟨fun x => f (sigmaProdEquiv κ d x),
      hf.comp (Equiv.injective _), fun x => hft (sigmaProdEquiv κ d x), fun w j => hloc (w, j)⟩,
    fun ⟨f, hf, hft, hloc⟩ => ⟨fun x => f ((sigmaProdEquiv κ d).symm x),
      hf.comp (Equiv.injective _), fun x => hft ((sigmaProdEquiv κ d).symm x),
      fun i => hloc i.1 i.2⟩⟩

/-- Simple Hall for the `MatchG2` shape: slots `Σ w, κ × Fin (d w)`, constant capacity `c`. -/
theorem exists_simple_injective_sigmaProd_iff_hall {κ : Type*} (t : ι → κ → Finset α)
    (d : ι → ℕ) (c : ℕ) :
    (∃ f : (Σ w : ι, κ × Fin (d w)) → α × Fin c, Function.Injective f ∧
        (∀ x, (f x).1 ∈ t x.1 x.2.1) ∧
        ∀ w j, Function.Injective fun k : Fin (d w) => (f ⟨w, (j, k)⟩).1) ↔
      ∀ s : Finset (ι × κ), ∑ i ∈ s, d i.1 ≤
        ∑ a ∈ s.biUnion (fun i => t i.1 i.2), min c (s.filter fun i => a ∈ t i.1 i.2).card := by
  rw [← hasSimpleBMatching_sigmaProd_iff, hasSimpleBMatching_iff]

/-- A simple b-matching with constant capacity is a fractional matching with weights `1 / c`:
item sets `M i ⊆ t i` of size `d i` with load at most `1`. -/
theorem HasSimpleBMatching.exists_image_props
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {t : ι → Finset α} {d : ι → ℕ} {c : ℕ}
    (h : HasSimpleBMatching t d (fun _ => c)) :
    ∃ M : ι → Finset α, (∀ i, M i ⊆ t i) ∧ (∀ i, (M i).card = d i) ∧
      ∀ (s : Finset ι) (g : α), ∑ i ∈ s, (if g ∈ M i then (1 / c : K) else 0) ≤ 1 := by
  obtain ⟨f, hf, hmem, hloc⟩ := (hasSimpleBMatching_const_iff t d c).1 h
  exact ⟨_, image_props_of_injective (K := K) f hf hmem hloc⟩

end PEqualNP.Base.Matching
