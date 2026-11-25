import PEqualNP.W951.Open.PaymentHall

/-!
# PHC: the deletion form of the payment Hall condition, necessity (seat F1)

Boards `open-one-not`, `open-many-not`. Paper: `one-not/research/open/F1_phc.md` (Lemma D).

Lemma D (paper): the payment Hall condition holds iff for every set `J` of payers
`∑ w, (c_w(J) - 1) ≤ |E \ J|`, where `c_w(J)` is the number of components of the classes of `w`
under the hyperedges of the payers in `J`. This file checks the direction "PHC implies the
deletion inequality", in a form that does not need components: any colouring of the classes that is
constant on the hyperedges of `J` uses at most `|F w \ J| + 1` colours on the classes of `w`.
The other direction is the matroid union theorem (Edmonds, Nash-Williams) and is not checked here.

* `card_colours_le`: a set joined by a family of edges, of which at most `k` are two-coloured, has
  at most `k + 1` colours.
* `ForestPay`: disjoint payer sets `F w ⊆ E`, each joining all classes of `w` by pairs picked
  inside the payers' hyperedges.
* `deletion_of_forestPay`: the deletion inequality.
* `card_ge_of_forestPay`: the count `∑ (classes - 1) ≤ |E|` (the case `J = ∅`).
-/

namespace PEqualNP.Outside.L_meta_951_aux.F2Transfer

open Finset

section Colours

variable {α γ κ : Type*} [DecidableEq α] [DecidableEq γ] [DecidableEq κ]

/-- The edge relation of the picked pairs of `F`. -/
def PickAdj (F : Finset α) (p q : α → γ) (x y : γ) : Prop :=
  ∃ g ∈ F, (p g = x ∧ q g = y) ∨ (p g = y ∧ q g = x)

/-- `C` is joined by the picked pairs of `F`. -/
def Joined (F : Finset α) (p q : α → γ) (C : Finset γ) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, Relation.ReflTransGen (PickAdj F p q) a b

/-- A set joined by edges of which at most `k` are two-coloured has at most `k + 1` colours. -/
theorem card_colours_le (F : Finset α) (p q : α → γ) (C : Finset γ) (hC : Joined F p q C) :
    ∀ (k : ℕ) (col : γ → κ), (F.filter (fun g => col (p g) ≠ col (q g))).card ≤ k →
      (C.image col).card ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro col hk
    have hmono : ∀ g ∈ F, col (p g) = col (q g) := by
      intro g hg
      by_contra hne
      have : g ∈ F.filter (fun g => col (p g) ≠ col (q g)) := Finset.mem_filter.mpr ⟨hg, hne⟩
      have h0 := Nat.le_zero.mp hk
      rw [Finset.card_eq_zero] at h0
      rw [h0] at this
      exact absurd this (Finset.notMem_empty _)
    have hstep : ∀ x y, PickAdj F p q x y → col x = col y := by
      rintro x y ⟨g, hg, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact hmono g hg
      · exact (hmono g hg).symm
    have hpath : ∀ x y, Relation.ReflTransGen (PickAdj F p q) x y → col x = col y := by
      intro x y h
      induction h with
      | refl => rfl
      | tail _ hbc ih => exact ih.trans (hstep _ _ hbc)
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact hpath x y (hC x hx y hy)
  | succ k ih =>
    intro col hk
    by_cases hbad : ∃ g ∈ F, col (p g) ≠ col (q g)
    · obtain ⟨g0, hg0, hne⟩ := hbad
      -- recolour: the colour of `q g0` becomes the colour of `p g0`
      set col' : γ → κ := fun x => if col x = col (q g0) then col (p g0) else col x with hcol'
      have hsub : F.filter (fun g => col' (p g) ≠ col' (q g)) ⊆
          (F.filter (fun g => col (p g) ≠ col (q g))).erase g0 := by
        intro g hg
        obtain ⟨hgF, hgne⟩ := Finset.mem_filter.mp hg
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hgF, ?_⟩⟩
        · rintro rfl
          apply hgne
          simp [hcol', hne]
        · intro heq
          apply hgne
          simp [hcol', heq]
      have hcard : (F.filter (fun g => col' (p g) ≠ col' (q g))).card ≤ k := by
        have h1 := Finset.card_le_card hsub
        have h2 : g0 ∈ F.filter (fun g => col (p g) ≠ col (q g)) :=
          Finset.mem_filter.mpr ⟨hg0, hne⟩
        rw [Finset.card_erase_of_mem h2] at h1
        omega
      have him : C.image col ⊆ insert (col (q g0)) (C.image col') := by
        intro c hc
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
        by_cases hxq : col x = col (q g0)
        · rw [hxq]; exact Finset.mem_insert_self _ _
        · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, ?_⟩)
          simp [hcol', hxq]
      calc (C.image col).card ≤ (insert (col (q g0)) (C.image col')).card :=
            Finset.card_le_card him
        _ ≤ (C.image col').card + 1 := Finset.card_insert_le _ _
        _ ≤ k + 1 + 1 := Nat.add_le_add_right (ih col' hcard) 1
    · have h0 : (F.filter (fun g => col (p g) ≠ col (q g))).card ≤ 0 := by
        rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro g hg hne
        exact hbad ⟨g, hg, hne⟩
      have hk0 : (F.filter (fun g => col (p g) ≠ col (q g))).card ≤ k := by omega
      exact (ih col hk0).trans (by omega)

end Colours

section Deletion

variable {ι α γ κ : Type*} [DecidableEq ι] [DecidableEq α] [DecidableEq γ] [DecidableEq κ]

/-- **Forest payment** (the payment Hall condition, joined form): pairwise disjoint payer sets
`F w ⊆ E`; every payer of `F w` picks two classes inside its hyperedge `Φ w g`; the picked pairs
join all classes `C w` of `w`. -/
def ForestPay (W : Finset ι) (E : Finset α) (C : ι → Finset γ) (Φ : ι → α → Finset γ) : Prop :=
  ∃ (F : ι → Finset α) (p q : ι → α → γ),
    (∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (F a) (F b)) ∧
    ∀ w ∈ W, F w ⊆ E ∧ (∀ g ∈ F w, p w g ∈ Φ w g ∧ q w g ∈ Φ w g) ∧ Joined (F w) (p w) (q w) (C w)

/-- **Deletion form, necessity.** If the payers of `J` keep `col w` constant on their hyperedges,
the colours used on the classes beyond the first are paid by the deleted payers `E \ J`. -/
theorem deletion_of_forestPay {W : Finset ι} {E : Finset α} {C : ι → Finset γ}
    {Φ : ι → α → Finset γ} (h : ForestPay W E C Φ) (J : Finset α) (col : ι → γ → κ)
    (hcol : ∀ w ∈ W, ∀ g ∈ J, ∀ x ∈ Φ w g, ∀ y ∈ Φ w g, col w x = col w y) :
    ∑ w ∈ W, (((C w).image (col w)).card - 1) ≤ (E \ J).card := by
  obtain ⟨F, p, q, hdis, hF⟩ := h
  have hper : ∀ w ∈ W, ((C w).image (col w)).card - 1 ≤ (F w \ J).card := by
    intro w hw
    obtain ⟨-, hpick, hjoin⟩ := hF w hw
    have hbad : (F w).filter (fun g => col w (p w g) ≠ col w (q w g)) ⊆ F w \ J := by
      intro g hg
      obtain ⟨hgF, hne⟩ := Finset.mem_filter.mp hg
      refine Finset.mem_sdiff.mpr ⟨hgF, fun hgJ => hne ?_⟩
      exact hcol w hw g hgJ _ (hpick g hgF).1 _ (hpick g hgF).2
    have := card_colours_le (F w) (p w) (q w) (C w) hjoin _ (col w) (Finset.card_le_card hbad)
    omega
  have hdis' : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (F a \ J) (F b \ J) := fun a ha b hb hab =>
    (hdis a ha b hb hab).mono Finset.sdiff_subset Finset.sdiff_subset
  calc ∑ w ∈ W, (((C w).image (col w)).card - 1) ≤ ∑ w ∈ W, (F w \ J).card :=
        Finset.sum_le_sum hper
    _ = (W.biUnion fun w => F w \ J).card := (Finset.card_biUnion hdis').symm
    _ ≤ (E \ J).card := Finset.card_le_card (Finset.biUnion_subset.mpr fun w hw =>
        Finset.sdiff_subset_sdiff (hF w hw).1 (Finset.Subset.refl J))

/-- **The count** (`J = ∅`, every class its own colour). -/
theorem card_ge_of_forestPay {W : Finset ι} {E : Finset α} {C : ι → Finset γ}
    {Φ : ι → α → Finset γ} (h : ForestPay W E C Φ) : ∑ w ∈ W, ((C w).card - 1) ≤ E.card := by
  have := deletion_of_forestPay h ∅ (fun _ x => x) (by simp)
  simpa using this

end Deletion

end PEqualNP.Outside.L_meta_951_aux.F2Transfer

#print axioms PEqualNP.Outside.L_meta_951_aux.F2Transfer.deletion_of_forestPay
#print axioms PEqualNP.Outside.L_meta_951_aux.F2Transfer.card_ge_of_forestPay
