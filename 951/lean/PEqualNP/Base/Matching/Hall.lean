import Mathlib

/-!
# Capacitated bipartite matching from Hall's theorem, and one weak-duality count

Helper module (proofs only). Circuit-free: everything is stated over an arbitrary family
`t : ι → Finset α` (demand vertex `i` may use the items in `t i`).

* `HasBMatching t d c`: vertex `i` gets `d i` slots, item `a` has `c a` copies, and an injective
  map sends every slot of `i` to a copy of an item of `t i`.
* `hasBMatching_iff`: such a map exists exactly when, for every finite set `s` of vertices,
  `∑ i ∈ s, d i ≤ ∑ a ∈ s.biUnion t, c a`. This is Mathlib's Hall theorem
  (`Finset.all_card_le_biUnion_card_iff_exists_injective`) on the blown-up graph.
* `hasBMatching_one_iff`: with every capacity `1`, the matching is an injective map of slots
  into items, the shape of W951's `MatchG`.
* `sum_mul_card_le_card_biUnion`: weak duality. If every item carries total weight at most `1`,
  then `∑ j, lam j * #(M j) ≤ #(⋃ j, M j)`. The counting step of every `bound_of_*` lemma.
* `sum_le_card_of_frac`: the fractional-matching corollary (the shape of W951's `FracMatch`).
* Shapes. `hasBMatching_const_iff`: constant capacity `c`, target `α × Fin c`.
  `sigmaProdEquiv`: slots `Σ w, κ × Fin (d w)` are the slots of the vertices `(w, j)`;
  `hasBMatching_sigmaProd_iff`, `load_le_one_of_injective_sigmaProd` work through it.
* `image_props_of_injective` (`_sigmaProd`, `_one`): an injection of slots yields item sets
  `M i ⊆ t i` of size `d i` with load at most `1` under weights `1 / c`, the input of
  `sum_le_card_of_frac`.
-/

namespace PEqualNP.Base.Matching

open Finset

variable {ι α : Type*} [DecidableEq α]

/-- The copies of the items of `T`, item `a` with `c a` copies. -/
def blow (c : α → ℕ) (T : Finset α) : Finset (Σ a, Fin (c a)) :=
  T.sigma fun _ => univ

omit [DecidableEq α] in
theorem mem_blow {c : α → ℕ} {T : Finset α} {y : Σ a, Fin (c a)} : y ∈ blow c T ↔ y.1 ∈ T := by
  simp [blow, mem_sigma]

omit [DecidableEq α] in
theorem card_blow (c : α → ℕ) (T : Finset α) : (blow c T).card = ∑ a ∈ T, c a := by
  simp [blow, card_sigma]

/-- A b-matching: `d i` slots for vertex `i`, `c a` copies of item `a`, and an injective map from
slots to copies that sends each slot of `i` to a copy of an item in `t i`. -/
def HasBMatching (t : ι → Finset α) (d : ι → ℕ) (c : α → ℕ) : Prop :=
  ∃ f : (Σ i, Fin (d i)) → (Σ a, Fin (c a)), Function.Injective f ∧ ∀ x, (f x).1 ∈ t x.1

/-- **Hall's theorem for b-matchings.** -/
theorem hasBMatching_iff (t : ι → Finset α) (d : ι → ℕ) (c : α → ℕ) :
    HasBMatching t d c ↔ ∀ s : Finset ι, ∑ i ∈ s, d i ≤ ∑ a ∈ s.biUnion t, c a := by
  classical
  let t' : (Σ i, Fin (d i)) → Finset (Σ a, Fin (c a)) := fun x => blow c (t x.1)
  have key : ∀ s' : Finset (Σ i, Fin (d i)),
      s'.biUnion t' = blow c ((s'.image Sigma.fst).biUnion t) := by
    intro s'
    ext y
    simp only [t', mem_biUnion, mem_blow, mem_image]
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨x.1, ⟨x, hx, rfl⟩, hy⟩
    · rintro ⟨i, ⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, hx, hy⟩
  constructor
  · rintro ⟨f, hf, hft⟩ s
    have h1 : (s.sigma fun i => (univ : Finset (Fin (d i)))).card = ∑ i ∈ s, d i := by
      simp [card_sigma]
    rw [← h1, ← card_blow]
    refine card_le_card_of_injOn f ?_ hf.injOn
    intro x hx
    simp only [mem_coe] at hx ⊢
    rw [mem_blow]
    exact mem_biUnion.2 ⟨x.1, (mem_sigma.1 hx).1, hft x⟩
  · intro h
    have hh : ∀ s' : Finset (Σ i, Fin (d i)), s'.card ≤ (s'.biUnion t').card := by
      intro s'
      rw [key, card_blow]
      calc s'.card ≤ ((s'.image Sigma.fst).sigma fun i => (univ : Finset (Fin (d i)))).card := by
            apply card_le_card
            intro x hx
            simp only [mem_sigma, mem_image, mem_univ, and_true]
            exact ⟨x, hx, rfl⟩
        _ = ∑ i ∈ s'.image Sigma.fst, d i := by simp [card_sigma]
        _ ≤ _ := h _
    obtain ⟨f, hf, hft⟩ := (all_card_le_biUnion_card_iff_exists_injective t').1 hh
    exact ⟨f, hf, fun x => mem_blow.1 (hft x)⟩

/-- The easy direction, as a bound: a b-matching gives the Hall inequality for every `s`. -/
theorem HasBMatching.sum_le {t : ι → Finset α} {d : ι → ℕ} {c : α → ℕ}
    (h : HasBMatching t d c) (s : Finset ι) : ∑ i ∈ s, d i ≤ ∑ a ∈ s.biUnion t, c a :=
  (hasBMatching_iff t d c).1 h s

omit [DecidableEq α] in
/-- With every capacity `1`, a b-matching is an injective map from slots to items. -/
theorem hasBMatching_one_iff (t : ι → Finset α) (d : ι → ℕ) :
    HasBMatching t d (fun _ => 1) ↔
      ∃ f : (Σ i, Fin (d i)) → α, Function.Injective f ∧ ∀ x, f x ∈ t x.1 := by
  constructor
  · rintro ⟨f, hf, hft⟩
    refine ⟨fun x => (f x).1, fun x y hxy => hf ?_, hft⟩
    exact Sigma.ext hxy (heq_of_eq (Subsingleton.elim _ _))
  · rintro ⟨f, hf, hft⟩
    refine ⟨fun x => ⟨f x, 0⟩, fun x y hxy => hf ?_, hft⟩
    simpa using congrArg Sigma.fst hxy

/-- **Weak duality.** If every item carries total weight at most `1`, the weighted sizes of the
sets add up to at most the size of their union. No sign condition on the weights is needed. -/
theorem sum_mul_card_le_card_biUnion {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {κ : Type*} (s : Finset κ) (lam : κ → K)
    (M : κ → Finset α) (hload : ∀ g, ∑ j ∈ s, (if g ∈ M j then lam j else 0) ≤ 1) :
    ∑ j ∈ s, lam j * (M j).card ≤ (s.biUnion M).card := by
  calc ∑ j ∈ s, lam j * (M j).card
      = ∑ j ∈ s, ∑ g ∈ s.biUnion M, (if g ∈ M j then lam j else 0) := by
        refine sum_congr rfl fun j hj => ?_
        rw [← sum_filter]
        have hf : (s.biUnion M).filter (· ∈ M j) = M j := by
          ext g
          simp only [mem_filter, mem_biUnion, and_iff_right_iff_imp]
          exact fun hg => ⟨j, hj, hg⟩
        rw [hf, sum_const, nsmul_eq_mul, mul_comm]
    _ = ∑ g ∈ s.biUnion M, ∑ j ∈ s, (if g ∈ M j then lam j else 0) := sum_comm
    _ ≤ ∑ g ∈ s.biUnion M, (1 : K) := sum_le_sum fun g _ => hload g
    _ = (s.biUnion M).card := by simp

/-- **Fractional matching bound.** Vertex `w` spreads weight `1` (nonnegative `lam w j`) over
`k w` sets `M w j`, each of size at least `d w`; every item carries total weight at most `1`.
Then the demands add up to at most the size of the union. -/
theorem sum_le_card_of_frac {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {ω : Type*} (W : Finset ω) (k : ω → ℕ)
    (lam : ∀ w, Fin (k w) → K) (M : ∀ w, Fin (k w) → Finset α) (d : ω → ℕ)
    (hlam : ∀ w j, 0 ≤ lam w j) (hsum : ∀ w ∈ W, ∑ j, lam w j = 1)
    (hd : ∀ w j, d w ≤ (M w j).card)
    (hload : ∀ g, ∑ w ∈ W, ∑ j, (if g ∈ M w j then lam w j else 0) ≤ 1) :
    ∑ w ∈ W, d w ≤
      ((W.sigma fun w => (univ : Finset (Fin (k w)))).biUnion
        fun x : (Σ w, Fin (k w)) => M x.1 x.2).card := by
  have hmain := sum_mul_card_le_card_biUnion (W.sigma fun w => (univ : Finset (Fin (k w))))
    (fun x : (Σ w, Fin (k w)) => lam x.1 x.2) (fun x : (Σ w, Fin (k w)) => M x.1 x.2) (fun g => by rw [sum_sigma]; exact hload g)
  rw [sum_sigma] at hmain
  have hle : ∀ w ∈ W, (d w : K) ≤ ∑ j, lam w j * (M w j).card := by
    intro w hw
    calc (d w : K) = ∑ j, lam w j * d w := by rw [← sum_mul, hsum w hw, one_mul]
      _ ≤ ∑ j, lam w j * (M w j).card := sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (by exact_mod_cast hd w j) (hlam w j)
  have : ((∑ w ∈ W, d w : ℕ) : K) ≤ ((((W.sigma fun w => (univ : Finset (Fin (k w)))).biUnion
      fun x : (Σ w, Fin (k w)) => M x.1 x.2).card : ℕ) : K) := by
    push_cast
    exact (sum_le_sum hle).trans hmain
  exact_mod_cast this

/-- Capacity-one Hall in the form W951 uses: an injective map of slots into items exists iff
every set of vertices has at least as many items as slots. -/
theorem exists_injective_iff_hall (t : ι → Finset α) (d : ι → ℕ) :
    (∃ f : (Σ i, Fin (d i)) → α, Function.Injective f ∧ ∀ x, f x ∈ t x.1) ↔
      ∀ s : Finset ι, ∑ i ∈ s, d i ≤ (s.biUnion t).card := by
  rw [← hasBMatching_one_iff, hasBMatching_iff]
  simp

/-- `sum_le_card_of_frac` against a ground set `G` that contains every `M w j`. -/
theorem sum_le_card_of_frac_subset {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {ω : Type*} (W : Finset ω) (k : ω → ℕ)
    (lam : ∀ w, Fin (k w) → K) (M : ∀ w, Fin (k w) → Finset α) (d : ω → ℕ)
    (hlam : ∀ w j, 0 ≤ lam w j) (hsum : ∀ w ∈ W, ∑ j, lam w j = 1)
    (hd : ∀ w j, d w ≤ (M w j).card)
    (hload : ∀ g, ∑ w ∈ W, ∑ j, (if g ∈ M w j then lam w j else 0) ≤ 1)
    (G : Finset α) (hG : ∀ w ∈ W, ∀ j, M w j ⊆ G) : ∑ w ∈ W, d w ≤ G.card := by
  refine (sum_le_card_of_frac W k lam M d hlam hsum hd hload).trans (card_le_card ?_)
  intro g hg
  simp only [mem_biUnion, mem_sigma] at hg
  obtain ⟨x, hx, hgx⟩ := hg
  exact hG x.1 hx.1 x.2 hgx

/-- In an injective map of slots into `α × Fin c`, at most `c` vertices reach a given item. -/
theorem card_filter_reach_le {κ : Type*} {d : κ → ℕ} {c : ℕ}
    (f : (Σ i, Fin (d i)) → α × Fin c) (hf : Function.Injective f) (s : Finset κ) (g : α) :
    (s.filter fun i => ∃ k, (f ⟨i, k⟩).1 = g).card ≤ c := by
  classical
  rcases c with _ | c
  · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
    rintro i - ⟨k, -⟩
    exact (f ⟨i, k⟩).2.elim0
  · calc _ ≤ (univ : Finset (Fin (c + 1))).card := by
          refine card_le_card_of_injOn (fun i => if h : ∃ k, (f ⟨i, k⟩).1 = g
            then (f ⟨i, h.choose⟩).2 else 0) (fun _ _ => by simp) ?_
          intro i hi j hj hij
          have hi' := (mem_filter.1 (mem_coe.1 hi)).2
          have hj' := (mem_filter.1 (mem_coe.1 hj)).2
          simp only [dite_eq_left hi', dite_eq_left hj'] at hij
          have e : f ⟨i, hi'.choose⟩ = f ⟨j, hj'.choose⟩ :=
            Prod.ext (hi'.choose_spec.trans hj'.choose_spec.symm) hij
          exact congrArg Sigma.fst (hf e)
      _ = c + 1 := by simp

/-- **Capacity `c` gives load at most `1` with weights `1 / c`.** The step behind
`fracMatch_of_matchG` (`c = 1`) and `fracMatch_of_matchG2` (`c = 2`). -/
theorem load_le_one_of_injective {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {κ : Type*} {d : κ → ℕ} {c : ℕ}
    (f : (Σ i, Fin (d i)) → α × Fin c) (hf : Function.Injective f) (s : Finset κ) (g : α) :
    ∑ i ∈ s, (if ∃ k, (f ⟨i, k⟩).1 = g then (1 / c : K) else 0) ≤ 1 := by
  classical
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  · have h := card_filter_reach_le f hf s g
    rw [mul_one_div, div_le_one (by exact_mod_cast hc)]
    exact_mod_cast h

/-! ### Shapes: constant capacity, capacity one, and the `(w, j)`-indexed slots

The definitions use the dependent target `Σ a, Fin (c a)` and slots `Σ i, Fin (d i)`. Consumers
usually have a constant capacity (target `α × Fin c`) and often slots `Σ w, κ × Fin (d w)` (vertex
`(w, j)` with demand `d w`). The lemmas below do that repacking once. -/

/-- Reassociation of slots: slot `(j, k)` of `w` is slot `k` of the vertex `(w, j)`. -/
def sigmaProdEquiv {ι : Type*} (κ : Type*) (d : ι → ℕ) :
    (Σ w : ι, κ × Fin (d w)) ≃ (Σ i : ι × κ, Fin (d i.1)) where
  toFun x := ⟨(x.1, x.2.1), x.2.2⟩
  invFun y := ⟨y.1.1, (y.1.2, y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem sigmaProdEquiv_apply {ι : Type*} (κ : Type*) (d : ι → ℕ)
    (x : Σ w : ι, κ × Fin (d w)) : sigmaProdEquiv κ d x = ⟨(x.1, x.2.1), x.2.2⟩ := rfl

@[simp] theorem sigmaProdEquiv_symm_apply {ι : Type*} (κ : Type*) (d : ι → ℕ)
    (y : Σ i : ι × κ, Fin (d i.1)) : (sigmaProdEquiv κ d).symm y = ⟨y.1.1, (y.1.2, y.2)⟩ := rfl

theorem sigmaProdEquiv_mk {ι : Type*} (κ : Type*) (d : ι → ℕ) (w : ι) (j : κ) (k : Fin (d w)) :
    sigmaProdEquiv κ d ⟨w, (j, k)⟩ = ⟨(w, j), k⟩ := rfl

theorem sigmaProdEquiv_symm_mk {ι : Type*} (κ : Type*) (d : ι → ℕ) (w : ι) (j : κ)
    (k : Fin (d w)) : (sigmaProdEquiv κ d).symm ⟨(w, j), k⟩ = ⟨w, (j, k)⟩ := rfl

omit [DecidableEq α] in
/-- With a constant capacity `c`, the copies of the items are `α × Fin c`. -/
theorem hasBMatching_const_iff (t : ι → Finset α) (d : ι → ℕ) (c : ℕ) :
    HasBMatching t d (fun _ => c) ↔
      ∃ f : (Σ i, Fin (d i)) → α × Fin c, Function.Injective f ∧ ∀ x, (f x).1 ∈ t x.1 :=
  ⟨fun ⟨f, hf, hft⟩ => ⟨fun x => Equiv.sigmaEquivProd α (Fin c) (f x),
      (Equiv.injective _).comp hf, hft⟩,
    fun ⟨f, hf, hft⟩ => ⟨fun x => (Equiv.sigmaEquivProd α (Fin c)).symm (f x),
      (Equiv.injective _).comp hf, hft⟩⟩

omit [DecidableEq α] in
/-- Constant capacity, vertices `(w, j)` with demand `d w`: the slots are `Σ w, κ × Fin (d w)`. -/
theorem hasBMatching_sigmaProd_iff {κ : Type*} (t : ι → κ → Finset α) (d : ι → ℕ) (c : ℕ) :
    HasBMatching (fun i : ι × κ => t i.1 i.2) (fun i => d i.1) (fun _ => c) ↔
      ∃ f : (Σ w : ι, κ × Fin (d w)) → α × Fin c, Function.Injective f ∧
        ∀ x, (f x).1 ∈ t x.1 x.2.1 := by
  rw [hasBMatching_const_iff]
  exact ⟨fun ⟨f, hf, hft⟩ => ⟨fun x => f (sigmaProdEquiv κ d x),
      hf.comp (Equiv.injective _), fun x => hft (sigmaProdEquiv κ d x)⟩,
    fun ⟨f, hf, hft⟩ => ⟨fun x => f ((sigmaProdEquiv κ d).symm x),
      hf.comp (Equiv.injective _), fun x => hft ((sigmaProdEquiv κ d).symm x)⟩⟩

/-- `load_le_one_of_injective` for slots `Σ w, κ × Fin (d w)`: the vertices are the pairs
`(w, j)`. -/
theorem load_le_one_of_injective_sigmaProd {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {κ : Type*} [Fintype κ] {d : ι → ℕ} {c : ℕ}
    (f : (Σ w : ι, κ × Fin (d w)) → α × Fin c) (hf : Function.Injective f) (s : Finset ι)
    (g : α) :
    ∑ w ∈ s, ∑ j, (if ∃ k, (f ⟨w, (j, k)⟩).1 = g then (1 / c : K) else 0) ≤ 1 := by
  have h := load_le_one_of_injective (K := K) (fun x => f ((sigmaProdEquiv κ d).symm x))
    (hf.comp (Equiv.injective _)) (s ×ˢ univ) g
  rwa [sum_product] at h

/-- **Capacity one gives load at most `1` with weights `1`**: the target is `α` itself. -/
theorem load_le_one_of_injective_one {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {κ : Type*} {d : κ → ℕ}
    (f : (Σ i, Fin (d i)) → α) (hf : Function.Injective f) (s : Finset κ) (g : α) :
    ∑ i ∈ s, (if ∃ k, f ⟨i, k⟩ = g then (1 : K) else 0) ≤ 1 := by
  have h := load_le_one_of_injective (K := K) (c := 1) (fun x => (f x, 0))
    (fun x y h => hf (congrArg Prod.fst h)) s g
  simpa using h

/-- **From an injection to a fractional matching.** For an injective map of slots into
`α × Fin c` that respects `t` and sends the slots of one vertex to distinct items, the item sets
`M i = {(f ⟨i, k⟩).1 | k}` lie in `t i`, have exactly `d i` elements, and carry load at most `1`
with weights `1 / c`. These are the hypotheses of `sum_le_card_of_frac`. -/
theorem image_props_of_injective {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {κ : Type*} {d : κ → ℕ} {c : ℕ} {t : κ → Finset α}
    (f : (Σ i, Fin (d i)) → α × Fin c) (hf : Function.Injective f)
    (hmem : ∀ x, (f x).1 ∈ t x.1)
    (hloc : ∀ i, Function.Injective fun k : Fin (d i) => (f ⟨i, k⟩).1) :
    (∀ i, (univ.image fun k : Fin (d i) => (f ⟨i, k⟩).1) ⊆ t i) ∧
    (∀ i, (univ.image fun k : Fin (d i) => (f ⟨i, k⟩).1).card = d i) ∧
    ∀ (s : Finset κ) (g : α),
      ∑ i ∈ s, (if g ∈ univ.image (fun k : Fin (d i) => (f ⟨i, k⟩).1)
        then (1 / c : K) else 0) ≤ 1 := by
  refine ⟨fun i => image_subset_iff.2 fun k _ => hmem ⟨i, k⟩,
    fun i => by rw [card_image_of_injective _ (hloc i)]; simp, fun s g => ?_⟩
  simpa using load_le_one_of_injective (K := K) f hf s g

/-- `image_props_of_injective` for slots `Σ w, κ × Fin (d w)` (vertices `(w, j)`): the shape of
`fracMatch_of_matchG2`. -/
theorem image_props_of_injective_sigmaProd {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {κ : Type*} [Fintype κ] {d : ι → ℕ} {c : ℕ}
    {t : ι → κ → Finset α}
    (f : (Σ w : ι, κ × Fin (d w)) → α × Fin c) (hf : Function.Injective f)
    (hmem : ∀ x, (f x).1 ∈ t x.1 x.2.1)
    (hloc : ∀ w j, Function.Injective fun k : Fin (d w) => (f ⟨w, (j, k)⟩).1) :
    (∀ w j, (univ.image fun k : Fin (d w) => (f ⟨w, (j, k)⟩).1) ⊆ t w j) ∧
    (∀ w j, (univ.image fun k : Fin (d w) => (f ⟨w, (j, k)⟩).1).card = d w) ∧
    ∀ (s : Finset ι) (g : α),
      ∑ w ∈ s, ∑ j, (if g ∈ univ.image (fun k : Fin (d w) => (f ⟨w, (j, k)⟩).1)
        then (1 / c : K) else 0) ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := image_props_of_injective (K := K)
    (t := fun i : ι × κ => t i.1 i.2) (fun x => f ((sigmaProdEquiv κ d).symm x))
    (hf.comp (Equiv.injective _)) (fun x => hmem ((sigmaProdEquiv κ d).symm x))
    (fun i => hloc i.1 i.2)
  refine ⟨fun w j => h1 (w, j), fun w j => h2 (w, j), fun s g => ?_⟩
  have h := h3 (s ×ˢ univ) g
  rwa [sum_product] at h

/-- `image_props_of_injective` with capacity one: an injective map of slots into items
(the shape of `fracMatch_of_matchG`), weights `1`. -/
theorem image_props_of_injective_one {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {κ : Type*} {d : κ → ℕ} {t : κ → Finset α}
    (f : (Σ i, Fin (d i)) → α) (hf : Function.Injective f) (hmem : ∀ x, f x ∈ t x.1) :
    (∀ i, (univ.image fun k : Fin (d i) => f ⟨i, k⟩) ⊆ t i) ∧
    (∀ i, (univ.image fun k : Fin (d i) => f ⟨i, k⟩).card = d i) ∧
    ∀ (s : Finset κ) (g : α),
      ∑ i ∈ s, (if g ∈ univ.image (fun k : Fin (d i) => f ⟨i, k⟩) then (1 : K) else 0) ≤ 1 := by
  refine ⟨fun i => image_subset_iff.2 fun k _ => hmem ⟨i, k⟩,
    fun i => by
      rw [card_image_of_injective _ fun a b h => by simpa using hf h]; simp,
    fun s g => ?_⟩
  simpa using load_le_one_of_injective_one (K := K) f hf s g

/-- Pairwise disjoint subsets of `U` have total size at most `#U`. -/
theorem sum_card_le_of_pairwiseDisjoint {ι α : Type*} [DecidableEq α] (s : Finset ι)
    (T : ι → Finset α) (U : Finset α)
    (hd : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (T a) (T b)) (hsub : ∀ i ∈ s, T i ⊆ U) :
    ∑ i ∈ s, (T i).card ≤ U.card := by
  rw [← Finset.card_biUnion hd]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr hsub)

/-- A sum over the enumeration `Finset.equivFin` of `s` is the sum over `s`. -/
theorem sum_equivFin {α M : Type*} [AddCommMonoid M] (s : Finset α) (F : α → M) :
    ∑ j : Fin s.card, F (s.equivFin.symm j).1 = ∑ a ∈ s, F a := by
  rw [Equiv.sum_comp s.equivFin.symm (fun a => F a.1), Finset.sum_coe_sort s F]

/-- A sum over the enumeration `Fintype.equivFin` of the subtype `{a // p a}` is the sum over the
elements that satisfy `p`. -/
theorem sum_equivFin_subtype {α M : Type*} [Fintype α] [AddCommMonoid M] (p : α → Prop)
    [DecidablePred p] (f : α → M) :
    ∑ i : Fin (Fintype.card {a // p a}), f ((Fintype.equivFin {a // p a}).symm i).1 =
      ∑ a ∈ univ.filter p, f a := by
  rw [Equiv.sum_comp (Fintype.equivFin {a // p a}).symm (fun a => f a.1)]
  exact (Finset.sum_subtype (univ.filter p) (fun a => by simp) f).symm

end PEqualNP.Base.Matching
