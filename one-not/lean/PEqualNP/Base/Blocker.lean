import Mathlib

/-!
# Blockers: maximal false points of a monotone function on a face

Helper module (proofs only; no circuits). `α` is a finite ground set, `h : Finset α → Prop` a
monotone property of subsets (a monotone Boolean function, read on supports), and `S` a set
(the face `{x_S = 0}` is the family of subsets disjoint from `S`).

* `IsMinterm h m`: `h m` holds and fails on every proper subset of `m`.
* `exists_minterm_subset`: if `h Z` then some minterm lies inside `Z`.
* `IsTransversal h S T`: `T` meets every minterm of `h` that is disjoint from `S`
  (the minterms on the face, `Min_w` of research's type-A note).
* `IsMinTransversal h S T`: a transversal with no transversal proper subset (an element of the
  blocker of `Min_w`, Edmonds and Fulkerson).
* `IsMaxFalse h S Z`: `Z` is disjoint from `S`, `h Z` fails, and `h` holds on every strictly larger
  set disjoint from `S` (an I1 zero point of the set `S` when `h` is the input of the NOT gate).
* `not_iff_isTransversal`: for `Z` disjoint from `S`, `¬ h Z` iff `(univ \ S) \ Z` is a transversal.
* `IsMinTransversal.subset_compl`: a minimal transversal avoids `S`.
* **`isMaxFalse_iff`**: `Z` is a maximal false point on the face iff
  `Z = (univ \ S) \ T` for a minimal transversal `T` (research, type-A menus (a)).
-/

namespace PEqualNP.Base.Blocker

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `m` is a minterm of `h`: `h m` holds and fails on every proper subset. -/
def IsMinterm (h : Finset α → Prop) (m : Finset α) : Prop :=
  h m ∧ ∀ m' ⊂ m, ¬ h m'

/-- `T` meets every minterm of `h` that is disjoint from `S`. -/
def IsTransversal (h : Finset α → Prop) (S T : Finset α) : Prop :=
  ∀ m, IsMinterm h m → Disjoint m S → (T ∩ m).Nonempty

/-- A transversal none of whose proper subsets is a transversal. -/
def IsMinTransversal (h : Finset α → Prop) (S T : Finset α) : Prop :=
  IsTransversal h S T ∧ ∀ T' ⊂ T, ¬ IsTransversal h S T'

/-- `Z` is a maximal false point of `h` on the face of sets disjoint from `S`. -/
def IsMaxFalse (h : Finset α → Prop) (S Z : Finset α) : Prop :=
  Disjoint Z S ∧ ¬ h Z ∧ ∀ Z', Z ⊂ Z' → Disjoint Z' S → h Z'

omit [Fintype α] [DecidableEq α] in
/-- Some minterm lies inside every set on which `h` holds. -/
theorem exists_minterm_subset {h : Finset α → Prop} {Z : Finset α} (hZ : h Z) :
    ∃ m ⊆ Z, IsMinterm h m := by
  classical
  have hne : (Z.powerset.filter h).Nonempty := ⟨Z, by simp [hZ]⟩
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image _ Finset.card hne
  simp only [Finset.mem_filter, Finset.mem_powerset] at hm
  refine ⟨m, hm.1, hm.2, fun m' hm' hhm' => ?_⟩
  have := hmin m' (by simp [(hm'.subset.trans hm.1), hhm'])
  exact absurd (Finset.card_lt_card hm') (not_lt.mpr this)

/-- On the face, `h` fails at `Z` exactly when the complement of `Z` in `univ \ S` is a
transversal. -/
theorem not_iff_isTransversal {h : Finset α → Prop} (hmono : Monotone h) {S Z : Finset α}
    (hZ : Disjoint Z S) : ¬ h Z ↔ IsTransversal h S ((Finset.univ \ S) \ Z) := by
  constructor
  · intro hn m hm hmS
    by_contra hT
    rw [Finset.not_nonempty_iff_eq_empty] at hT
    apply hn
    refine hmono (fun t ht => ?_) hm.1
    by_contra htZ
    have htS : t ∉ S := Finset.disjoint_left.mp hmS ht
    have : t ∈ ((Finset.univ \ S) \ Z) ∩ m := by simp [htS, htZ, ht]
    simp [hT] at this
  · intro hT hz
    obtain ⟨m, hmZ, hm⟩ := exists_minterm_subset hz
    obtain ⟨t, ht⟩ := hT m hm (Finset.disjoint_of_subset_left hmZ hZ)
    simp only [Finset.mem_inter, Finset.mem_sdiff] at ht
    exact ht.1.2 (hmZ ht.2)

/-- A minimal transversal avoids `S`. -/
theorem IsMinTransversal.subset_compl {h : Finset α → Prop} {S T : Finset α}
    (hT : IsMinTransversal h S T) : T ⊆ Finset.univ \ S := by
  intro t ht
  by_contra htS
  apply hT.2 (T.erase t) (Finset.erase_ssubset ht)
  intro m hm hmS
  obtain ⟨u, hu⟩ := hT.1 m hm hmS
  have hut : u ≠ t := by
    rintro rfl
    simp only [Finset.mem_inter] at hu
    exact htS (by simp [Finset.disjoint_left.mp hmS hu.2])
  exact ⟨u, by simp only [Finset.mem_inter, Finset.mem_erase] at hu ⊢; exact ⟨⟨hut, hu.1⟩, hu.2⟩⟩

/-- **Research's type-A characterization (a).** `Z` is a maximal false point of the monotone `h`
on the face `{x_S = 0}` iff `Z = (univ \ S) \ T` for a minimal transversal `T` of the minterms of
`h` disjoint from `S`. -/
theorem isMaxFalse_iff {h : Finset α → Prop} (hmono : Monotone h) {S Z : Finset α} :
    IsMaxFalse h S Z ↔ ∃ T, IsMinTransversal h S T ∧ Z = (Finset.univ \ S) \ T := by
  set top : Finset α := Finset.univ \ S
  have htopS : Disjoint top S := Finset.sdiff_disjoint
  constructor
  · rintro ⟨hZS, hZ, hmax⟩
    have hZtop : Z ⊆ top := fun t ht => by
      simp [top, Finset.disjoint_left.mp hZS ht]
    refine ⟨top \ Z, ⟨(not_iff_isTransversal hmono hZS).mp hZ, fun T' hT' hT'tr => ?_⟩, ?_⟩
    · have hT'top : T' ⊆ top := hT'.subset.trans Finset.sdiff_subset
      have hZ' : Z ⊂ top \ T' := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨fun t ht => ?_, fun he => ?_⟩
        · exact Finset.mem_sdiff.mpr ⟨hZtop ht, fun htT' =>
            (Finset.mem_sdiff.mp (hT'.subset htT')).2 ht⟩
        · apply hT'.ne
          ext t
          constructor
          · exact fun ht => hT'.subset ht
          · intro ht
            have httop : t ∈ top := (Finset.mem_sdiff.mp ht).1
            by_contra htT'
            have : t ∈ top \ T' := Finset.mem_sdiff.mpr ⟨httop, htT'⟩
            rw [← he] at this
            exact (Finset.mem_sdiff.mp ht).2 this
      have hdis : Disjoint (top \ T') S := Finset.disjoint_of_subset_left Finset.sdiff_subset htopS
      have hfalse : ¬ h (top \ T') := by
        rw [not_iff_isTransversal hmono hdis, Finset.sdiff_sdiff_eq_self hT'top]
        exact hT'tr
      exact hfalse (hmax _ hZ' hdis)
    · rw [Finset.sdiff_sdiff_eq_self hZtop]
  · rintro ⟨T, hT, rfl⟩
    have hTtop : T ⊆ top := hT.subset_compl
    have hdis : Disjoint (top \ T) S := Finset.disjoint_of_subset_left Finset.sdiff_subset htopS
    refine ⟨hdis, ?_, fun Z' hZ' hZ'S => ?_⟩
    · rw [not_iff_isTransversal hmono hdis, Finset.sdiff_sdiff_eq_self hTtop]
      exact hT.1
    · by_contra hn
      have hZ'top : Z' ⊆ top := fun t ht => by simp [top, Finset.disjoint_left.mp hZ'S ht]
      have hT'tr := (not_iff_isTransversal hmono hZ'S).mp hn
      apply hT.2 (top \ Z') _ hT'tr
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun t ht => ?_, fun he => ?_⟩
      · have ht' := Finset.mem_sdiff.mp ht
        by_contra htT
        exact ht'.2 (hZ'.subset (Finset.mem_sdiff.mpr ⟨ht'.1, htT⟩))
      · apply hZ'.ne
        rw [← Finset.sdiff_sdiff_eq_self hZ'top, he]

end PEqualNP.Base.Blocker
