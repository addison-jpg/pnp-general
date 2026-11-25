import Mathlib
import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.W951.Open.Or4ManyNot

/-!
# Systems of ORs, any number of NOT gates: `gates ≥ n - components`

Several outputs, output `i` the OR of the set `S i ⊆ Fin n`. NOT gates are free (only AND/OR gates are
counted). B2's partition argument gives a colouring `c` of the inputs with
`n ≤ #classes(c) + #AND/OR gates` in which every wire depends on one class. Every output depends on one
class, and the OR of `S i` depends on each input of `S i`, so `c` is constant on each `S i`, hence on each
connected component of the union graph (two inputs adjacent when they lie in a common set). So the
number of classes is at most the number of components `comp`, and
`gates ≥ n - comp` (isolated inputs count as components, so this is `n_used - comp_used`).

Compared with `base = ∑ (|S i| - 1)`: always `n - comp ≤ base`, with equality exactly when the incidence
graph (inputs and sets, edges = membership) is a forest, i.e. the system is a Berge-acyclic hyperforest.
This file proves the bound, and equality with `base` for pairwise disjoint sets and for a chain
`S i = {i, i+1}` (the general equality statement is stated in the board finding, not proved here).
-/

namespace PEqualNP.W951.Open.OrSystemManyNot

open PEqualNP.CircuitLowerBounds PEqualNP.W951.Open.Or4ManyNot

variable {n m : ℕ}

/-- inputs adjacent when they share a set -/
def Adj (S : Fin m → Finset (Fin n)) (i j : Fin n) : Prop := ∃ s, i ∈ S s ∧ j ∈ S s

/-- same connected component of the union graph -/
def Rel (S : Fin m → Finset (Fin n)) : Fin n → Fin n → Prop := Relation.ReflTransGen (Adj S)

theorem eq_of_mono {S : Fin m → Finset (Fin n)} {c : Fin n → ℕ}
    (h : ∀ s, ∀ i ∈ S s, ∀ j ∈ S s, c i = c j) : ∀ i j, Rel S i j → c i = c j := by
  intro i j hij
  induction hij with
  | refl => rfl
  | tail _ hb ih =>
    obtain ⟨s, h1, h2⟩ := hb
    exact ih.trans (h s _ h1 _ h2)

/-- **The partition bound for a system of ORs, any number of NOT gates.** If `g` labels the connected
components of the union graph (`g i = g j` only for inputs in the same component), a circuit whose
outputs `o s` are the ORs of the sets `S s` has at least `n - #labels` AND/OR gates. -/
theorem system_bound (C : Circuit) (hv : ∀ g ∈ C.gates, Valid g)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hor : ∀ s, ∀ x : Fin n → Bool,
      (C.gates.foldl stepW (List.ofFn x)).getD (o s) false = decide (∃ i ∈ S s, x i = true))
    {β : Type} [DecidableEq β] (g : Fin n → β) (hg : ∀ i j, g i = g j → Rel S i j) :
    n ≤ C.gates.countP counted + (Finset.univ.image g).card := by
  obtain ⟨c, L, hL, hn, hd⟩ := foldl_inv C.gates hv _ _ _ _ (init_inv (n := n))
  have hmono : ∀ s, ∀ i ∈ S s, ∀ j ∈ S s, c i = c j := by
    intro s
    obtain ⟨k, hk⟩ := hd (o s)
    have hall : ∀ i ∈ S s, c i = k := by
      intro i hi
      by_contra hne
      have := hk (fun _ => false) (fun j => decide (j = i)) (by
        intro j hj
        have : j ≠ i := fun e => hne (e ▸ hj)
        simp [this])
      simp only at this
      rw [hor s, hor s] at this
      simp [hi] at this
    intro i hi j hj
    rw [hall i hi, hall j hj]
  have hc : ∀ i j, g i = g j → c i = c j := fun i j h => eq_of_mono hmono i j (hg i j h)
  have : (Finset.univ.image c).card ≤ (Finset.univ.image g).card := by
    let f : β → ℕ := fun b => if h : ∃ i, g i = b then c h.choose else 0
    apply Finset.card_le_card_of_surjOn f
    intro k hk
    rw [Finset.mem_coe] at hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    refine ⟨g i, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩), ?_⟩
    have hex : ∃ i', g i' = g i := ⟨i, rfl⟩
    simp only [f, dif_pos hex]
    exact hc _ _ hex.choose_spec
  omega

/-- number of connected components of the union graph (isolated inputs included) -/
def compSetoid (S : Fin m → Finset (Fin n)) : Setoid (Fin n) :=
  ⟨Relation.EqvGen (Adj S), Relation.EqvGen.is_equivalence _⟩

noncomputable def comp (S : Fin m → Finset (Fin n)) : ℕ :=
  Nat.card (Quotient (compSetoid S))

theorem adj_symm {S : Fin m → Finset (Fin n)} {i j : Fin n} (h : Adj S i j) : Adj S j i := by
  obtain ⟨s, h1, h2⟩ := h; exact ⟨s, h2, h1⟩

theorem rel_symm {S : Fin m → Finset (Fin n)} {i j : Fin n} (h : Rel S i j) : Rel S j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hb ih => exact Relation.ReflTransGen.head (adj_symm hb) ih

theorem eqvGen_rel {S : Fin m → Finset (Fin n)} {i j : Fin n} (h : Relation.EqvGen (Adj S) i j) :
    Rel S i j := by
  induction h with
  | rel _ _ h => exact Relation.ReflTransGen.single h
  | refl _ => exact Relation.ReflTransGen.refl
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ h1 h2 => exact h1.trans h2

/-- **Canonical form: `n ≤ gates + comp`**, i.e. `gates ≥ n_used - (components of the union graph)`. -/
theorem system_bound_comp (C : Circuit) (hv : ∀ g ∈ C.gates, Valid g)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hor : ∀ s, ∀ x : Fin n → Bool,
      (C.gates.foldl stepW (List.ofFn x)).getD (o s) false = decide (∃ i ∈ S s, x i = true)) :
    n ≤ C.gates.countP counted + comp S := by
  classical
  have h := system_bound C hv S o hor
    (fun i : Fin n => (Quotient.mk (compSetoid S) i)) (fun i j hij => eqvGen_rel (Quotient.exact hij))
  have h2 : (Finset.univ.image (fun i : Fin n => (Quotient.mk (compSetoid S) i))).card ≤ comp S := by
    unfold comp
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  omega

/-! ### Equality with `base` -/

/-- the project's `base` of a set system: `∑ (|S i| - 1)` -/
def base (S : Fin m → Finset (Fin n)) : ℕ := ∑ s, ((S s).card - 1)

/-- Pairwise disjoint nonempty sets: the bound is exactly `base`, so every circuit with any number of NOT
gates needs at least `base` AND/OR gates. -/
theorem disjoint_bound (C : Circuit) (hv : ∀ g ∈ C.gates, Valid g)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hor : ∀ s, ∀ x : Fin n → Bool,
      (C.gates.foldl stepW (List.ofFn x)).getD (o s) false = decide (∃ i ∈ S s, x i = true))
    (hdis : ∀ s t, s ≠ t → Disjoint (S s) (S t)) (hne : ∀ s, (S s).Nonempty) :
    base S ≤ C.gates.countP counted := by
  classical
  let g : Fin n → Fin m ⊕ Fin n := fun i => if h : ∃ s, i ∈ S s then Sum.inl h.choose else Sum.inr i
  have hg : ∀ i j, g i = g j → Rel S i j := by
    intro i j hij
    by_cases hi : ∃ s, i ∈ S s <;> by_cases hj : ∃ s, j ∈ S s <;> simp only [g, hi, hj, dif_pos, dif_neg, not_false_eq_true] at hij
    · have e : hi.choose = hj.choose := Sum.inl.inj hij
      exact Relation.ReflTransGen.single ⟨hi.choose, hi.choose_spec, e ▸ hj.choose_spec⟩
    · exact absurd hij (by simp)
    · exact absurd hij (by simp)
    · have : i = j := Sum.inr.inj hij
      subst this; exact Relation.ReflTransGen.refl
  have h := system_bound C hv S o hor g hg
  -- card of image g ≤ m + (n - |union|)
  have hun : (Finset.univ.biUnion S).card = ∑ s, (S s).card :=
    Finset.card_biUnion (fun s _ t _ hst => hdis s t hst)
  have himg : (Finset.univ.image g).card ≤ m + (n - (Finset.univ.biUnion S).card) := by
    have hsub : Finset.univ.image g ⊆
        (Finset.univ.image (Sum.inl : Fin m → Fin m ⊕ Fin n)) ∪
          ((Finset.univ \ Finset.univ.biUnion S).image (Sum.inr : Fin n → Fin m ⊕ Fin n)) := by
      intro v hv'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv'
      by_cases hi : ∃ s, i ∈ S s
      · simp only [g, dif_pos hi]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
      · simp only [g, dif_neg hi]
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, ?_, rfl⟩)
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and, not_exists]
        exact fun s => fun h => hi ⟨s, h⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    have a1 : (Finset.univ.image (Sum.inl : Fin m → Fin m ⊕ Fin n)).card ≤ m := by
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := Sum.inl (β := Fin n))
    have a2 : ((Finset.univ \ Finset.univ.biUnion S).image (Sum.inr : Fin n → Fin m ⊕ Fin n)).card
        ≤ n - (Finset.univ.biUnion S).card := by
      refine (Finset.card_image_le).trans ?_
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp
    omega
  have hle : ∑ s, (S s).card ≤ n := by
    rw [← hun]; simpa using Finset.card_le_univ (Finset.univ.biUnion S)
  have hsum : ∑ s, (S s).card = base S + m := by
    unfold base
    have e : ∑ s, (S s).card = ∑ s, (((S s).card - 1) + 1) :=
      Finset.sum_congr rfl fun s _ => by have := (hne s).card_pos; omega
    rw [e, Finset.sum_add_distrib]
    simp
  omega

/-- The chain `S i = {i, i+1}` on `m + 1` inputs: `m` sets, `base = m`, one component, so the bound is
`m = base`. Any circuit, any number of NOT gates, needs `m` AND/OR gates. -/
theorem chain_bound (m : ℕ) (C : Circuit) (hv : ∀ g ∈ C.gates, Valid g)
    (S : Fin m → Finset (Fin (m + 1))) (hS : ∀ s, S s = {s.castSucc, s.succ}) (o : Fin m → ℕ)
    (hor : ∀ s, ∀ x : Fin (m + 1) → Bool,
      (C.gates.foldl stepW (List.ofFn x)).getD (o s) false = decide (∃ i ∈ S s, x i = true)) :
    m ≤ C.gates.countP counted := by
  have hg : ∀ i j : Fin (m + 1), (fun _ => (0 : Unit)) i = (fun _ => (0 : Unit)) j → Rel S i j := by
    have key : ∀ k : ℕ, ∀ hk : k < m + 1, Rel S ⟨0, by omega⟩ ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero => intro hk; exact Relation.ReflTransGen.refl
      | succ k ih =>
        intro hk
        refine (ih (by omega)).tail ⟨⟨k, by omega⟩, ?_, ?_⟩
        · rw [hS]; simp [Fin.ext_iff]
        · rw [hS]; simp [Fin.ext_iff]
    intro i j _
    have hi := key i.val i.isLt
    have hj := key j.val j.isLt
    exact (rel_symm hi).trans hj
  have h := system_bound C hv S o hor _ hg
  have : (Finset.univ.image (fun _ : Fin (m + 1) => (0 : Unit))).card ≤ 1 := by
    apply Finset.card_le_one.mpr; intro a _ b _; exact Subsingleton.elim _ _
  omega

#print axioms system_bound
#print axioms system_bound_comp
#print axioms disjoint_bound
#print axioms chain_bound

end PEqualNP.W951.Open.OrSystemManyNot
