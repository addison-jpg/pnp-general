import PEqualNP.Base.Matching.Hall

/-!
# Base/Matching/Charging: the charging (regrouping) bound

Pure combinatorics, no circuits. `G` is a finite set of "gates", every gate `g` owns a finite set
`R g` of "entries" (its rectangle, but no product structure is used here), and `w` is a weight
on entries.

* `cover G R e`: the number of gates `g ∈ G` with `e ∈ R g`.
* `sum_mul_cover_eq` / `sum_sum_eq_sum_mul_cover`: **regrouping**
  `Σ_g Σ_{e ∈ R g} w e = Σ_e w e · cover e` (double counting, any commutative semiring).
* `sum_mul_cover_le_card`: **charging bound.** `w ≥ 0` and `Σ_{e ∈ R g} w e ≤ 1` for every gate
  give `Σ_{e ∈ S} w e · cover e ≤ |G|`, for every finite set `S` of entries.
* `sum_mul_le_card_of_le_cover` (`_nat`): the same with a lower bound `c e ≤ cover e`.
* `mul_sum_le_card_of_le_cover`, `minCover_mul_sum_le_card`: `m · Σ_e w e ≤ |G|` when every
  entry of the support of `w` is covered at least `m` times; `minCover` is that minimum.

The bound is the weak-duality lemma `sum_mul_card_le_card_biUnion` (Hall.lean) read with the roles
"vertex = entry, item = gate, `M e = {g | e ∈ R g}`"; `sum_mul_cover_le_card'` is that instance
(it needs `R g ⊆ S` instead of `w ≥ 0`).
-/

namespace PEqualNP.Base.Matching

open Finset

variable {γ ε : Type*} [DecidableEq ε]

/-- The number of gates of `G` whose set `R g` contains the entry `e`. -/
def cover (G : Finset γ) (R : γ → Finset ε) (e : ε) : ℕ := (G.filter fun g => e ∈ R g).card

theorem cover_mono {G : Finset γ} {R R' : γ → Finset ε} (h : ∀ g ∈ G, R g ⊆ R' g) (e : ε) :
    cover G R e ≤ cover G R' e :=
  card_le_card fun g hg => by
    rw [mem_filter] at hg ⊢
    exact ⟨hg.1, h g hg.1 hg.2⟩

theorem cover_le_card (G : Finset γ) (R : γ → Finset ε) (e : ε) : cover G R e ≤ G.card :=
  card_le_card (filter_subset _ _)

theorem cover_pos_iff {G : Finset γ} {R : γ → Finset ε} {e : ε} :
    0 < cover G R e ↔ ∃ g ∈ G, e ∈ R g := by
  simp [cover, card_pos, Finset.Nonempty]

/-- **Regrouping (double counting), relative to a set `S` of entries.** -/
theorem sum_mul_cover_eq {M : Type*} [CommSemiring M] (G : Finset γ) (R : γ → Finset ε)
    (w : ε → M) (S : Finset ε) :
    ∑ e ∈ S, w e * cover G R e = ∑ g ∈ G, ∑ e ∈ S.filter (fun e => e ∈ R g), w e := by
  simp_rw [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm, cover]

/-- **Regrouping identity** `Σ_g Σ_{e ∈ R g} w e = Σ_e w e · #{g | e ∈ R g}`, for any finite
set `S` of entries containing all the `R g`. -/
theorem sum_sum_eq_sum_mul_cover {M : Type*} [CommSemiring M] (G : Finset γ)
    (R : γ → Finset ε) (w : ε → M) (S : Finset ε) (hS : ∀ g ∈ G, R g ⊆ S) :
    ∑ g ∈ G, ∑ e ∈ R g, w e = ∑ e ∈ S, w e * cover G R e := by
  rw [sum_mul_cover_eq]
  refine sum_congr rfl fun g hg => ?_
  congr 1
  ext e
  simp only [mem_filter]
  exact ⟨fun h => ⟨hS g hg h, h⟩, fun h => h.2⟩

/-- The regrouping identity over a finite type of entries. -/
theorem sum_sum_eq_sum_mul_cover_univ {M : Type*} [CommSemiring M] [Fintype ε] (G : Finset γ)
    (R : γ → Finset ε) (w : ε → M) :
    ∑ g ∈ G, ∑ e ∈ R g, w e = ∑ e, w e * cover G R e :=
  sum_sum_eq_sum_mul_cover G R w univ fun _ _ => subset_univ _

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Charging bound.** Nonnegative weights with `Σ_{e ∈ R g} w e ≤ 1` for every gate:
`Σ_{e ∈ S} w e · #{g | e ∈ R g} ≤ |G|` for every finite set `S` of entries. -/
theorem sum_mul_cover_le_card (G : Finset γ) (R : γ → Finset ε) (w : ε → K)
    (hw : ∀ e, 0 ≤ w e) (hR : ∀ g ∈ G, ∑ e ∈ R g, w e ≤ 1) (S : Finset ε) :
    ∑ e ∈ S, w e * cover G R e ≤ G.card := by
  rw [sum_mul_cover_eq]
  calc ∑ g ∈ G, ∑ e ∈ S.filter (fun e => e ∈ R g), w e
      ≤ ∑ g ∈ G, (1 : K) := sum_le_sum fun g hg =>
        (sum_le_sum_of_subset_of_nonneg (fun e he => (mem_filter.mp he).2)
          fun e _ _ => hw e).trans (hR g hg)
    _ = G.card := by simp

/-- The charging bound as an instance of weak duality (`sum_mul_card_le_card_biUnion`): no sign
condition, but all the `R g` lie in `S`. -/
theorem sum_mul_cover_le_card' [DecidableEq γ] (G : Finset γ) (R : γ → Finset ε) (w : ε → K)
    (S : Finset ε) (hS : ∀ g ∈ G, R g ⊆ S) (hR : ∀ g ∈ G, ∑ e ∈ R g, w e ≤ 1) :
    ∑ e ∈ S, w e * cover G R e ≤ G.card := by
  refine (sum_mul_card_le_card_biUnion S w (fun e => G.filter fun g => e ∈ R g)
    fun g => ?_).trans ?_
  · by_cases hg : g ∈ G
    · simp only [mem_filter, hg, true_and]
      rw [← sum_filter]
      have : S.filter (fun e => e ∈ R g) = R g := by
        ext e
        simp only [mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hS g hg h, h⟩⟩
      rw [this]
      exact hR g hg
    · simp [hg]
  · exact_mod_cast card_le_card (biUnion_subset.mpr fun e _ => filter_subset _ _)

/-- **Charging bound, the form of the request**: `Σ_e w e · #{g | e ∈ R g} ≤ #gates`. -/
theorem sum_mul_cover_le_card_univ [Fintype γ] [Fintype ε] (R : γ → Finset ε) (w : ε → K)
    (hw : ∀ e, 0 ≤ w e) (hR : ∀ g, ∑ e ∈ R g, w e ≤ 1) :
    ∑ e, w e * cover univ R e ≤ Fintype.card γ :=
  sum_mul_cover_le_card univ R w hw (fun g _ => hR g) univ

/-- **Charging with a coverage count.** If every entry `e ∈ S` lies in at least `c e` of the
sets `R g`, then `Σ_{e ∈ S} w e · c e ≤ |G|`. -/
theorem sum_mul_le_card_of_le_cover (G : Finset γ) (R : γ → Finset ε) (w : ε → K)
    (hw : ∀ e, 0 ≤ w e) (hR : ∀ g ∈ G, ∑ e ∈ R g, w e ≤ 1) (S : Finset ε) (c : ε → K)
    (hc : ∀ e ∈ S, c e ≤ cover G R e) : ∑ e ∈ S, w e * c e ≤ G.card :=
  (sum_le_sum fun e he => mul_le_mul_of_nonneg_left (hc e he) (hw e)).trans
    (sum_mul_cover_le_card G R w hw hR S)

/-- `sum_mul_le_card_of_le_cover` with a natural-number coverage count. -/
theorem sum_mul_le_card_of_le_cover_nat (G : Finset γ) (R : γ → Finset ε) (w : ε → K)
    (hw : ∀ e, 0 ≤ w e) (hR : ∀ g ∈ G, ∑ e ∈ R g, w e ≤ 1) (S : Finset ε) (c : ε → ℕ)
    (hc : ∀ e ∈ S, c e ≤ cover G R e) : ∑ e ∈ S, w e * c e ≤ G.card :=
  sum_mul_le_card_of_le_cover G R w hw hR S (fun e => c e) fun e he => by exact_mod_cast hc e he

/-- **Uniform coverage.** If every entry of `S` with nonzero weight lies in at least `m` of the
sets `R g`, then `m · Σ_{e ∈ S} w e ≤ |G|`. -/
theorem mul_sum_le_card_of_le_cover (G : Finset γ) (R : γ → Finset ε) (w : ε → K)
    (hw : ∀ e, 0 ≤ w e) (hR : ∀ g ∈ G, ∑ e ∈ R g, w e ≤ 1) (S : Finset ε) (m : ℕ)
    (hm : ∀ e ∈ S, w e ≠ 0 → m ≤ cover G R e) : (m : K) * ∑ e ∈ S, w e ≤ G.card := by
  rw [mul_sum]
  refine (sum_le_sum fun e he => ?_).trans (sum_mul_cover_le_card G R w hw hR S)
  by_cases h0 : w e = 0
  · simp [h0]
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hm e he h0) (hw e)

/-- The least coverage over a finite set `T` of entries (`0` if `T` is empty). -/
def minCover (G : Finset γ) (R : γ → Finset ε) (T : Finset ε) : ℕ :=
  if h : T.Nonempty then T.inf' h (cover G R) else 0

theorem minCover_le (G : Finset γ) (R : γ → Finset ε) {T : Finset ε} {e : ε} (he : e ∈ T) :
    minCover G R T ≤ cover G R e := by
  have h : T.Nonempty := ⟨e, he⟩
  simp only [minCover, h, ↓reduceDIte]
  exact inf'_le _ he

theorem le_minCover (G : Finset γ) (R : γ → Finset ε) {T : Finset ε} (hT : T.Nonempty) {m : ℕ}
    (hm : ∀ e ∈ T, m ≤ cover G R e) : m ≤ minCover G R T := by
  simp only [minCover, hT, ↓reduceDIte]
  exact (le_inf'_iff _ _).mpr hm

/-- **The request's bound**: `(min over supp w of #{g | e ∈ R g}) · Σ_e w e ≤ |G|`. -/
theorem minCover_mul_sum_le_card (G : Finset γ) (R : γ → Finset ε) (w : ε → K)
    (hw : ∀ e, 0 ≤ w e) (hR : ∀ g ∈ G, ∑ e ∈ R g, w e ≤ 1) (S : Finset ε) :
    (minCover G R (S.filter fun e => w e ≠ 0) : K) * ∑ e ∈ S, w e ≤ G.card :=
  mul_sum_le_card_of_le_cover G R w hw hR S _ fun _ he h0 =>
    minCover_le G R (mem_filter.mpr ⟨he, h0⟩)

end PEqualNP.Base.Matching
