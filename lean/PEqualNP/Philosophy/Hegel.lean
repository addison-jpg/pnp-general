import PEqualNP.Philosophy.Fisher

/-!
# Determinate negation, sublation, and adjoint opposites (philosophy-unification seat)

HONESTY. This file contains formal models of cited readings. It claims nothing about what Hegel
meant, and the readings are contested (LITERATURE.md, M1 and M5). Each definition names the
reading it follows. Nothing here is about circuits.

Readings followed.
* Hegel, *Phenomenology of Spirit* (1807), Introduction, on determinate negation: the result of a
  refutation is not an empty nothing but "the nothing of that from which it results", so it has a
  content. Cited from memory of the Baillie (1910, public domain) and Miller translations, not
  re-read for this file.
* Hegel, *Science of Logic*: sublation (Aufhebung) both cancels and preserves.
* F. W. Lawvere, "Unity and Identity of Opposites in Calculus and Physics", Applied Categorical
  Structures 4 (1996): an adjoint cylinder is an adjoint triple whose two outer functors are full
  and faithful (definition as reported on the nLab page "adjoint modality"; paper not opened).
* G. Priest, the Logic of Paradox (LP), as one contested model of dialectical contradiction.

The carrier is Fisher's branching frame (`Fisher.Frame`, seat P4). The new object is the free
rooted frame `Path α`: a moment is the list of decisions taken so far.
-/

namespace PEqualNP.Philosophy.Hegel

open PEqualNP.Philosophy.Fisher

/-! ### 1. Rooted frames: the lost is the other -/

section Rooted

variable {M : Type*} [Frame M]

/-- The other of a moment: neither its past nor its possible future. Reading: the negative of
`m` inside one frame (our modelling choice; the same relation is Beauvoir's "barbarian" in
`Beauvoir.lean`). -/
def Other (m f : M) : Prop := ¬ m ≤ f ∧ ¬ f ≤ m

theorem other_symm {m f : M} (h : Other m f) : Other f m := ⟨h.2, h.1⟩

/-- A lost future is an other (any frame). -/
theorem other_of_lost {m f : M} (h : Lost m f) : Other m f := h.2

/-- Two moments are joined in some later moment exactly when they are comparable. Linear past is
what forbids a common future of incomparable moments. -/
theorem coactual_iff_comparable {f g : M} : (∃ h, f ≤ h ∧ g ≤ h) ↔ (f ≤ g ∨ g ≤ f) := by
  constructor
  · rintro ⟨h, hf, hg⟩
    exact Frame.linear_past f g h hf hg
  · rintro (h | h)
    · exact ⟨g, h, le_rfl⟩
    · exact ⟨f, le_rfl, h⟩

/-- The other is exactly the moment with which no future is shared. -/
theorem other_iff_no_common_future {m f : M} : Other m f ↔ ¬ ∃ h, m ≤ h ∧ f ≤ h := by
  rw [coactual_iff_comparable]
  unfold Other
  tauto

variable [OrderBot M]

/-- In a frame with a first moment, Fisher's lost futures are exactly the others: everything that
is not me, was not me and cannot become me was once possible, and is lost. -/
theorem lost_iff_other {m f : M} : Lost m f ↔ Other m f :=
  ⟨other_of_lost, fun h => ⟨⟨⊥, bot_le, bot_le⟩, h⟩⟩

/-- Loss is mutual in a rooted frame. -/
theorem lost_symm {m f : M} (h : Lost m f) : Lost f m :=
  lost_iff_other.2 (other_symm (lost_iff_other.1 h))

/-- Nothing leaves the frame: every moment is past, still open, or lost. -/
theorem trichotomy (m f : M) : f ≤ m ∨ m ≤ f ∨ Lost m f := by
  by_cases h1 : f ≤ m
  · exact Or.inl h1
  · by_cases h2 : m ≤ f
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (lost_iff_other.2 ⟨h2, h1⟩))

end Rooted

/-! ### 2. The free rooted frame: paths of decisions -/

/-- A moment of a search: the decisions taken so far, oldest first. Reading: a route on the
boards is the list of its reductions; the order is "extends". -/
@[ext] structure Path (α : Type*) where
  /-- the decisions, oldest first -/
  steps : List α

namespace Path

variable {α : Type*}

instance : Frame (Path α) where
  le p q := p.steps <+: q.steps
  le_refl p := List.prefix_refl _
  le_trans _ _ _ h1 h2 := List.IsPrefix.trans h1 h2
  le_antisymm p q h1 h2 := Path.ext (h1.eq_of_length_le h2.length_le)
  linear_past _ _ _ h1 h2 := List.prefix_or_prefix_of_prefix h1 h2

theorem le_def {p q : Path α} : p ≤ q ↔ p.steps <+: q.steps := Iff.rfl

instance : OrderBot (Path α) where
  bot := ⟨[]⟩
  bot_le _ := List.nil_prefix

instance [DecidableEq α] : DecidableRel (α := Path α) (· ≤ ·) :=
  fun p q => inferInstanceAs (Decidable (p.steps <+: q.steps))

/-- The past of a path is its initial segments: a chain fixed by the path alone. -/
theorem le_iff_take {p m : Path α} : p ≤ m ↔ ∃ k, p.steps = m.steps.take k := by
  rw [le_def]
  constructor
  · intro h
    exact ⟨p.steps.length, List.prefix_iff_eq_take.1 h⟩
  · rintro ⟨k, hk⟩
    rw [hk]
    exact List.take_prefix _ _

end Path

/-! ### 3. Lost routes diverge at one point (our label: determinate negation) -/

/-- Two lists, neither a prefix of the other, part at a first point of difference. -/
theorem diverge {α : Type*} : ∀ l₁ l₂ : List α, ¬ l₁ <+: l₂ → ¬ l₂ <+: l₁ →
    ∃ a x y s t, x ≠ y ∧ l₁ = a ++ x :: s ∧ l₂ = a ++ y :: t
  | [], l₂, h, _ => absurd List.nil_prefix h
  | _ :: _, [], _, h => absurd List.nil_prefix h
  | x :: s, y :: t, h1, h2 => by
    by_cases hxy : x = y
    · subst hxy
      have h1' : ¬ s <+: t := fun h => h1 (List.cons_prefix_cons.2 ⟨rfl, h⟩)
      have h2' : ¬ t <+: s := fun h => h2 (List.cons_prefix_cons.2 ⟨rfl, h⟩)
      obtain ⟨a, x', y', s', t', hne, e1, e2⟩ := diverge s t h1' h2'
      exact ⟨x :: a, x', y', s', t', hne, by simp [e1], by simp [e2]⟩
    · exact ⟨[], x, y, s, t, hxy, rfl, rfl⟩

/-- Lost routes share a longest common prefix and then differ. If `f` is lost at `m`, the two
share a common part `a` and then differ by one pair of decisions `x ≠ y`: the present took `x`
where the lost route took `y`. This is a fact about two lists, neither a prefix of the other.
Calling it "determinate negation" (Hegel, *Phenomenology*, Introduction) is our reading; Hegel's
notion concerns the content of a refuted standpoint, not a branch point in a tree. -/
theorem determinate_negation {α : Type*} {m f : Path α} (h : Lost m f) :
    ∃ (a : Path α) (x y : α), x ≠ y ∧ a ≤ m ∧ a ≤ f ∧
      (⟨a.steps ++ [x]⟩ : Path α) ≤ m ∧ (⟨a.steps ++ [y]⟩ : Path α) ≤ f := by
  obtain ⟨hmf, hfm⟩ := other_of_lost h
  obtain ⟨a, x, y, s, t, hne, e1, e2⟩ := diverge m.steps f.steps hmf hfm
  refine ⟨⟨a⟩, x, y, hne, ?_, ?_, ?_, ?_⟩
  · exact Path.le_def.2 (e1 ▸ List.prefix_append _ _)
  · exact Path.le_def.2 (e2 ▸ List.prefix_append _ _)
  · refine Path.le_def.2 ⟨s, ?_⟩
    simp [e1]
  · refine Path.le_def.2 ⟨t, ?_⟩
    simp [e2]

/-- The point of first difference of two lists is unique. -/
theorem determinate_negation_unique {α : Type*} {a a' : List α} {x y x' y' : α}
    {s t s' t' : List α} (hne : x ≠ y) (hne' : x' ≠ y')
    (e1 : a ++ x :: s = a' ++ x' :: s') (e2 : a ++ y :: t = a' ++ y' :: t') : a = a' := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => rfl
    | cons b a' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at e1 e2
      exact absurd (e1.1.trans e2.1.symm) hne
  | cons b a ih =>
    cases a' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at e1 e2
      exact absurd (e1.1.symm.trans e2.1) hne'
    | cons b' a' =>
      simp only [List.cons_append, List.cons.injEq] at e1 e2
      rw [e1.1, ih e1.2 e2.2]

/-! ### 4. Sublation of a claim by its counterexample -/

section Sublation

variable {X : Type*}

/-- Remove one element `c` from a set `D`. Read, by us, as a claim over `D` refuted at `c`
continuing over `D` without `c`. This is not Hegel's Aufhebung: that preserves the negated moment
in a higher unity, while here the counterexample is deleted from the domain. -/
def sublate (D : Set X) (c : X) : Set X := D \ {c}

/-- Removing a member makes the set strictly smaller. -/
theorem sublate_ssubset {D : Set X} {c : X} (hc : c ∈ D) : sublate D c ⊂ D :=
  ⟨Set.sdiff_subset, fun h => (h hc).2 rfl⟩

/-- Removing one element: everything else is unchanged (re-inserting it restores the set). -/
theorem sublate_preserves {D : Set X} {c : X} (hc : c ∈ D) : insert c (sublate D c) = D := by
  ext x
  simp only [sublate, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | h)
    · exact hc
    · exact h.1
  · intro h
    by_cases hx : x = c
    · exact Or.inl hx
    · exact Or.inr ⟨h, hx⟩

/-- `D \ {c}` is the greatest subset of `D` that avoids `c`. -/
theorem sublate_greatest {D D' : Set X} {c : X} (h : D' ⊆ D) (hc : c ∉ D') : D' ⊆ sublate D c :=
  fun _ hx => ⟨h hx, fun hxc => hc (hxc ▸ hx)⟩

/-- A larger removed set leaves a smaller remainder `D \ W`. -/
theorem live_antitone (D : Set X) {W W' : Set X} (h : W ⊆ W') : D \ W' ⊆ D \ W :=
  Set.sdiff_subset_sdiff_right h

/-- Contraposition for sets: `W ⊆ Dᶜ ↔ D ⊆ Wᶜ`. (One can say complement is self-adjoint; no
claim is made that this is Lawvere's reading of opposites.) -/
theorem witness_domain_adjoint (W D : Set X) : W ⊆ Dᶜ ↔ D ⊆ Wᶜ :=
  Set.subset_compl_comm

end Sublation

/-! ### 5. Lawvere: unity and identity of opposites, smallest instance -/

/-- Left adjoint: the even numbers `n ↦ 2n` sit below `half`. -/
theorem even_half_adjoint : GaloisConnection (fun n : ℕ => 2 * n) (fun m : ℕ => m / 2) := by
  intro n m
  show 2 * n ≤ m ↔ n ≤ m / 2
  omega

/-- Right adjoint: the odd numbers `n ↦ 2n + 1` sit above `half`. -/
theorem half_odd_adjoint : GaloisConnection (fun m : ℕ => m / 2) (fun n : ℕ => 2 * n + 1) := by
  intro m n
  show m / 2 ≤ n ↔ m ≤ 2 * n + 1
  omega

/-- Even and odd embeddings of `ℕ` with `half` as a common retraction: `2n/2 = n`,
`(2n+1)/2 = n`, both maps injective, images disjoint. The adjunctions are the separate lemmas
`even_half_adjoint` and `half_odd_adjoint`; full-and-faithfulness is not stated here. A toy
instance of the shape of Lawvere's adjoint cylinder (1996, as reported on nLab); it relates to
Hegel only by our labelling. -/
theorem even_odd_embeddings_with_half :
    (∀ n : ℕ, (2 * n) / 2 = n) ∧ (∀ n : ℕ, (2 * n + 1) / 2 = n) ∧
      Function.Injective (fun n : ℕ => 2 * n) ∧ Function.Injective (fun n : ℕ => 2 * n + 1) ∧
      ∀ n k : ℕ, 2 * n ≠ 2 * k + 1 := by
  refine ⟨fun n => by omega, fun n => by omega, fun a b h => ?_, fun a b h => ?_,
    fun n k => by omega⟩
  · simp only at h; omega
  · simp only at h; omega

/-! ### 6. A paraconsistent check (Priest's LP) -/

/-- Truth values of LP: true only, both, false only. -/
inductive LP | t | b | f deriving DecidableEq

/-- LP negation: swaps `t` and `f`, fixes `b`. -/
def LP.neg : LP → LP
  | .t => .f | .b => .b | .f => .t

/-- LP conjunction: the minimum in the order `f < b < t`. -/
def LP.and : LP → LP → LP
  | .f, _ => .f | _, .f => .f
  | .b, _ => .b | _, .b => .b
  | .t, .t => .t

/-- Designated values: at least true. -/
def LP.designated : LP → Prop
  | .f => False | _ => True

instance : DecidablePred LP.designated := fun v => by cases v <;> unfold LP.designated <;> infer_instance

/-- A contradiction can be designated without everything being designated. Reading: Priest's LP as a model of
dialectical contradiction (contested: see LITERATURE.md M1). A three-valued truth-table check;
it is not connected to the frame or to any board. -/
theorem lp_no_explosion :
    ∃ A B : LP, LP.designated (LP.and A (LP.neg A)) ∧ ¬ LP.designated B :=
  ⟨.b, .f, by decide, by decide⟩

/-- Yet non-contradiction stays a law of LP: `¬(A ∧ ¬A)` is always designated. -/
theorem lp_noncontradiction (A : LP) : LP.designated (LP.neg (LP.and A (LP.neg A))) := by
  cases A <;> decide

end PEqualNP.Philosophy.Hegel
