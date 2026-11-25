import PEqualNP.QuantumGravity.Helpers.GateWords

/-!
Helpers for L-qg-101: the count of local gates, `(localGates n).ncard ≤ (n + 1)^3 * 8!`.

A local gate `g` acts on the bits of a set `T` of at most three positions (`gatesOn T`). Such a
gate is fixed by its action on the bits in `T` (`actionOn T g`), and that action is a
permutation of `T → Bool`, because `g` is injective. So at most `(2^|T|)! ≤ 8!` gates act on the
bits of `T`, and there are at most `(n + 1)^3` sets `T` of at most three positions
(`smallSets n`). The count avoids a case split on `n < 3`: it never enlarges `T` to three
positions.
-/

namespace PEqualNP.QuantumGravity.Helpers

open PEqualNP.QuantumGravity

variable {n : ℕ}

/-- The reversible maps of `n` bits that act on the bits in `T`: they leave every bit outside
`T` unchanged, and the new bits in `T` depend only on the old bits in `T`. -/
def gatesOn (T : Finset (Fin n)) : Set (Equiv.Perm (Fin n → Bool)) :=
  {g | (∀ x i, i ∉ T → g x i = x i) ∧
    ∀ x y, (∀ i ∈ T, x i = y i) → ∀ i ∈ T, g x i = g y i}

/-- The assignment of the `n` bits that agrees with `u` on `T` and is `false` outside `T`. -/
def extendBits (T : Finset (Fin n)) (u : T → Bool) : Fin n → Bool :=
  fun i => if h : i ∈ T then u ⟨i, h⟩ else false

/-- The action of `g` on the bits in `T`, read on the assignments that are `false` outside
`T`. -/
def actionOn (T : Finset (Fin n)) (g : Equiv.Perm (Fin n → Bool)) : (T → Bool) → (T → Bool) :=
  fun u i => g (extendBits T u) i

theorem actionOn_injective {T : Finset (Fin n)} {g : Equiv.Perm (Fin n → Bool)}
    (hg : g ∈ gatesOn T) : Function.Injective (actionOn T g) := by
  intro u v huv
  have hgx : g (extendBits T u) = g (extendBits T v) := by
    funext i
    by_cases hi : i ∈ T
    · exact congrFun huv ⟨i, hi⟩
    · rw [hg.1 _ i hi, hg.1 _ i hi]
      simp [extendBits, hi]
  funext i
  simpa [extendBits] using congrFun (g.injective hgx) i

/-- A gate that acts on the bits in `T` is fixed by its action on the bits in `T`. -/
theorem eq_of_actionOn_eq {T : Finset (Fin n)} {g h : Equiv.Perm (Fin n → Bool)}
    (hg : g ∈ gatesOn T) (hh : h ∈ gatesOn T) (e : actionOn T g = actionOn T h) : g = h := by
  ext x i
  by_cases hi : i ∈ T
  · have hx : ∀ j ∈ T, x j = extendBits T (fun j => x j) j := by
      intro j hj
      simp [extendBits, hj]
    rw [hg.2 x _ hx i hi, hh.2 x _ hx i hi]
    exact congrFun (congrFun e _) ⟨i, hi⟩
  · rw [hg.1 x i hi, hh.1 x i hi]

/-- At most `(2^|T|)!` reversible maps of `n` bits act on the bits in `T`. -/
theorem ncard_gatesOn_le (T : Finset (Fin n)) :
    (gatesOn T).ncard ≤ (2 ^ T.card).factorial := by
  classical
  let F : Equiv.Perm (Fin n → Bool) → Equiv.Perm (T → Bool) := fun g =>
    if hg : Function.Injective (actionOn T g) then
      Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hg)
    else 1
  have hF : ∀ g ∈ gatesOn T, ⇑(F g) = actionOn T g := by
    intro g hg
    simp [F, actionOn_injective hg]
  have hcard : (Set.univ : Set (Equiv.Perm (T → Bool))).ncard = (2 ^ T.card).factorial := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_perm]
    simp
  rw [← hcard]
  exact Set.ncard_le_ncard_of_injOn F (fun _ _ => Set.mem_univ _)
    (fun g hg h hh e => eq_of_actionOn_eq hg hh (by rw [← hF g hg, ← hF h hh, e]))
    Set.finite_univ

/-- The sets of at most three bit positions. -/
def smallSets (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun T => T.card ≤ 3)

/-- There are at most `(n + 1)^3` sets of at most three bit positions: `∑_{k ≤ 3} C(n, k)`. -/
theorem card_smallSets_le (n : ℕ) : (smallSets n).card ≤ (n + 1) ^ 3 := by
  have hsub : smallSets n ⊆
      (Finset.range 4).biUnion (fun k => Finset.powersetCard k (Finset.univ : Finset (Fin n))) := by
    intro T hT
    have hT3 : T.card ≤ 3 := (Finset.mem_filter.1 hT).2
    exact Finset.mem_biUnion.2 ⟨T.card, Finset.mem_range.2 (by omega),
      Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩⟩
  calc (smallSets n).card
      ≤ ((Finset.range 4).biUnion
          (fun k => Finset.powersetCard k (Finset.univ : Finset (Fin n)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range 4, (Finset.powersetCard k (Finset.univ : Finset (Fin n))).card :=
        Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.range 4, n.choose k := by simp [Finset.card_powersetCard]
    _ ≤ ∑ k ∈ Finset.range 4, n ^ k := Finset.sum_le_sum (fun k _ => Nat.choose_le_pow n k)
    _ ≤ (n + 1) ^ 3 := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]
        nlinarith [Nat.zero_le n, Nat.zero_le (n ^ 2)]

theorem localGates_subset_gatesOn {g : Equiv.Perm (Fin n → Bool)} (hg : g ∈ localGates n) :
    ∃ T ∈ smallSets n, g ∈ gatesOn T := by
  obtain ⟨T, hT, h1, h2⟩ := hg
  exact ⟨T, Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩, h1, h2⟩

/-- At most `(n + 1)^3 * 8!` reversible maps of `n` bits act on at most three bits. -/
theorem ncard_localGates_le (n : ℕ) : (localGates n).ncard ≤ (n + 1) ^ 3 * 40320 := by
  classical
  let U : Finset (Equiv.Perm (Fin n → Bool)) :=
    (smallSets n).biUnion (fun T => (gatesOn T).toFinite.toFinset)
  have hsub : localGates n ⊆ (U : Set (Equiv.Perm (Fin n → Bool))) := by
    intro g hg
    obtain ⟨T, hT, hgT⟩ := localGates_subset_gatesOn hg
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨T, hT, (Set.Finite.mem_toFinset _).2 hgT⟩)
  have hT : ∀ T ∈ smallSets n, ((gatesOn T).toFinite.toFinset).card ≤ 40320 := by
    intro T hT
    rw [← Set.ncard_eq_toFinset_card (gatesOn T) (gatesOn T).toFinite]
    refine (ncard_gatesOn_le T).trans ?_
    have hT3 : T.card ≤ 3 := (Finset.mem_filter.1 hT).2
    calc (2 ^ T.card).factorial ≤ (2 ^ 3).factorial :=
          Nat.factorial_le (Nat.pow_le_pow_right (by norm_num) hT3)
      _ = 40320 := by decide
  calc (localGates n).ncard ≤ (U : Set (Equiv.Perm (Fin n → Bool))).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet U)
    _ = U.card := Set.ncard_coe_finset U
    _ ≤ ∑ T ∈ smallSets n, ((gatesOn T).toFinite.toFinset).card := Finset.card_biUnion_le
    _ ≤ (smallSets n).card • 40320 := Finset.sum_le_card_nsmul _ _ _ hT
    _ ≤ (n + 1) ^ 3 * 40320 := by
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_right _ (card_smallSets_le n)

/-- Some reversible map of `n` bits has no circuit of at most `k` gates that each act on at
most three bits, when `((n + 1)^3 * 8! + 1)^k < (2^n)!`. -/
theorem exists_not_mem_reachableIn_localGates (n k : ℕ)
    (h : ((n + 1) ^ 3 * 40320 + 1) ^ k < (2 ^ n).factorial) :
    ∃ g : Equiv.Perm (Fin n → Bool), g ∉ ReachableIn (localGates n) k := by
  have hfin : (localGates n).Finite := Set.toFinite _
  have hcard : hfin.toFinset.card ≤ (n + 1) ^ 3 * 40320 := by
    rw [← Set.ncard_eq_toFinset_card (localGates n) hfin]
    exact ncard_localGates_le n
  obtain ⟨g, hg⟩ := exists_not_mem_reachableIn hfin.toFinset k (by
    rw [nat_card_perm_bits]
    exact lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) k) h)
  exact ⟨g, by rwa [Set.Finite.coe_toFinset] at hg⟩

end PEqualNP.QuantumGravity.Helpers
