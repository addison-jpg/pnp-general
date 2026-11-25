import Mathlib

/-!
# Methods 2: multidimensional bounds. Dominance and the Pareto frontier

LABEL. Definitions and theorems about the METHOD (task `boards/tasks/methods-formal.md`), not
about circuits; nothing bears on P versus NP.

The method. A bound is a vector over axes (size, depth, fan-out, number of NOT gates, ...), not a
number. Two bounds may be incomparable. What a set of known points says is its frontier.

DEFINITION CHOICES (see `methods/README.md`):
* a bound is `Bound ι = ι → ℕ` for an axis type `ι`; the order is pointwise;
* SMALLER IS BETTER (costs: an upper bound, a construction). For lower bounds apply everything to
  the order dual; sections 1 and 2 are stated for any partial order, so they apply to it;
* `frontier S` is the set of minimal points of `S`.

CHECKED: the frontier is an antichain; inserting a point never brings back a discarded point,
keeps every frontier point the new point does not beat, and never shrinks the covered region;
under well-foundedness (which `ι → ℕ` has when `ι` is finite) every point lies above a frontier
point, so the frontier covers what the set covers and is nonempty when the set is; the same for
any FINITE set in any partial order; in `ι → ℕ` with `ι` finite the frontier of ANY set, also an
infinite one, is finite (Dickson's lemma, from Mathlib).

Section 4 is DATA: the axes of `worlds/README.md` and pointers to the rows called L6. No
circuit numbers are encoded.
-/

namespace PEqualNP.Methods.Pareto

/-- A bound: one natural number for each axis. -/
abbrev Bound (ι : Type*) := ι → ℕ

/-! ### 1. Dominance and the frontier, in any partial order -/

section Order

variable {β : Type*} [PartialOrder β]

/-- `p` dominates `q`: at most `q` everywhere, and not equal. -/
def Dominates (p q : β) : Prop := p < q

/-- The frontier: the points of `S` that no point of `S` dominates. -/
def frontier (S : Set β) : Set β := {p | p ∈ S ∧ ∀ q ∈ S, ¬ Dominates q p}

/-- The region covered by `S`: everything at or above a point of `S`. -/
def covered (S : Set β) : Set β := {x | ∃ p ∈ S, p ≤ x}

theorem frontier_subset (S : Set β) : frontier S ⊆ S := fun _ h => h.1

theorem mem_frontier_iff_minimal {S : Set β} {p : β} : p ∈ frontier S ↔ Minimal (· ∈ S) p := by
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun q hq hqp => by_contra fun hn => h q hq (lt_of_le_not_ge hqp hn)⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun q hq hlt => not_le_of_gt hlt (h hq hlt.le)⟩

/-- **The frontier is an antichain**: two different frontier points are incomparable. -/
theorem frontier_isAntichain (S : Set β) : IsAntichain (· ≤ ·) (frontier S) := by
  intro p hp q hq hne hle
  exact hq.2 p hp.1 (lt_of_le_of_ne hle hne)

theorem frontier_idem (S : Set β) : frontier (frontier S) = frontier S := by
  ext p
  exact ⟨fun h => h.1, fun h => ⟨h, fun q hq => h.2 q hq.1⟩⟩

theorem covered_mono {S T : Set β} (h : S ⊆ T) : covered S ⊆ covered T :=
  fun _ ⟨p, hp, hx⟩ => ⟨p, h hp, hx⟩

theorem subset_covered (S : Set β) : S ⊆ covered S := fun p hp => ⟨p, hp, le_rfl⟩

/-- In dimension one there is nothing multidimensional: the frontier has at most one point. -/
theorem frontier_subsingleton_of_linear {γ : Type*} [LinearOrder γ] (S : Set γ) :
    (frontier S).Subsingleton := by
  intro p hp q hq
  rcases lt_trichotomy p q with h | h | h
  · exact absurd h (hq.2 p hp.1)
  · exact h
  · exact absurd h (hp.2 q hq.1)

/-! ### 2. Update: inserting one point -/

/-- **No discarded point comes back.** After inserting `x`, the frontier is inside the old
frontier plus `x`. -/
theorem frontier_insert_subset (S : Set β) (x : β) :
    frontier (insert x S) ⊆ insert x (frontier S) := by
  rintro p ⟨hp, h⟩
  rcases hp with rfl | hp
  · exact .inl rfl
  · exact .inr ⟨hp, fun q hq => h q (.inr hq)⟩

/-- A frontier point stays on the frontier unless the new point dominates it. -/
theorem mem_frontier_insert {S : Set β} {x p : β} (hp : p ∈ frontier S) (hx : ¬ Dominates x p) :
    p ∈ frontier (insert x S) := by
  refine ⟨.inr hp.1, ?_⟩
  rintro q (rfl | hq)
  · exact hx
  · exact hp.2 q hq

/-- The new point is on the frontier unless an old point dominates it. -/
theorem self_mem_frontier_insert {S : Set β} {x : β} (hx : ∀ q ∈ S, ¬ Dominates q x) :
    x ∈ frontier (insert x S) := by
  refine ⟨.inl rfl, ?_⟩
  rintro q (rfl | hq)
  · exact lt_irrefl _
  · exact hx q hq

/-- Exact form of the update. -/
theorem frontier_insert (S : Set β) (x : β) :
    frontier (insert x S) =
      {p | (p = x ∧ ∀ q ∈ S, ¬ Dominates q x) ∨ (p ∈ frontier S ∧ ¬ Dominates x p)} := by
  ext p
  constructor
  · rintro ⟨hp, h⟩
    by_cases hpx : p = x
    · subst hpx
      exact .inl ⟨rfl, fun q hq => h q (.inr hq)⟩
    · rcases hp with rfl | hp
      · exact absurd rfl hpx
      · exact .inr ⟨⟨hp, fun q hq => h q (.inr hq)⟩, h x (.inl rfl)⟩
  · rintro (⟨rfl, h⟩ | ⟨hp, hx⟩)
    · exact self_mem_frontier_insert h
    · exact mem_frontier_insert hp hx

/-- A point dominated by the set changes nothing. -/
theorem frontier_insert_of_dominated {S : Set β} {x : β} (h : ∃ q ∈ frontier S, Dominates q x) :
    frontier (insert x S) = frontier S := by
  obtain ⟨q, hq, hqx⟩ := h
  rw [frontier_insert]
  ext p
  constructor
  · rintro (⟨rfl, h⟩ | ⟨hp, _⟩)
    · exact absurd hqx (h q hq.1)
    · exact hp
  · intro hp
    refine .inr ⟨hp, fun hxp => ?_⟩
    exact hp.2 q hq.1 (lt_trans hqx hxp)

/-! ### 3. Reaching the frontier -/

/-- Every point of `S` lies at or above a frontier point. -/
def Reaches (S : Set β) : Prop := ∀ p ∈ S, ∃ q ∈ frontier S, q ≤ p

/-- If the frontier is reached, the frontier covers exactly what the set covers. -/
theorem covered_frontier {S : Set β} (h : Reaches S) : covered (frontier S) = covered S := by
  refine Set.Subset.antisymm (covered_mono (frontier_subset S)) ?_
  rintro x ⟨p, hp, hx⟩
  obtain ⟨q, hq, hqp⟩ := h p hp
  exact ⟨q, hq, hqp.trans hx⟩

theorem frontier_nonempty_of_reaches {S : Set β} (h : Reaches S) (hne : S.Nonempty) :
    (frontier S).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨q, hq, _⟩ := h p hp
  exact ⟨q, hq⟩

/-- **Monotone update.** If the frontier is reached before and after, the region covered by the
frontier only grows when a point is inserted. -/
theorem covered_frontier_insert {S : Set β} {x : β} (h : Reaches S) (h' : Reaches (insert x S)) :
    covered (frontier S) ⊆ covered (frontier (insert x S)) := by
  rw [covered_frontier h, covered_frontier h']
  exact covered_mono (Set.subset_insert x S)

/-- With a well-founded order the frontier of any set is reached. -/
theorem reaches_of_wellFoundedLT [WellFoundedLT β] (S : Set β) : Reaches S := by
  intro p hp
  obtain ⟨q, hqp, hq⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ S) p hp
  exact ⟨q, mem_frontier_iff_minimal.2 hq, hqp⟩

/-- The frontier of a finite set is reached, in any partial order. -/
theorem reaches_of_finite {S : Set β} (hS : S.Finite) : Reaches S := by
  intro p hp
  have hT : ({q | q ∈ S ∧ q ≤ p} : Set β).Finite := hS.subset fun _ h => h.1
  obtain ⟨q, ⟨hqS, hqp⟩, hmin⟩ := hT.exists_minimal ⟨p, hp, le_rfl⟩
  refine ⟨q, ⟨hqS, fun r hr hlt => ?_⟩, hqp⟩
  exact not_le_of_gt hlt (hmin ⟨hr, hlt.le.trans hqp⟩ hlt.le)

/-- **The frontier of a nonempty finite set is nonempty.** -/
theorem frontier_nonempty_of_finite {S : Set β} (hS : S.Finite) (hne : S.Nonempty) :
    (frontier S).Nonempty :=
  frontier_nonempty_of_reaches (reaches_of_finite hS) hne

end Order

/-! ### Bounds over finitely many axes -/

section Bounds

variable {ι : Type*}

theorem dominates_iff {p q : Bound ι} :
    Dominates p q ↔ (∀ i, p i ≤ q i) ∧ ∃ i, p i < q i := Pi.lt_def

variable [Finite ι]

/-- In `ι → ℕ` with finitely many axes the frontier of any set is reached. -/
theorem bound_reaches (S : Set (Bound ι)) : Reaches S := reaches_of_wellFoundedLT S

theorem bound_frontier_nonempty {S : Set (Bound ι)} (hne : S.Nonempty) : (frontier S).Nonempty :=
  frontier_nonempty_of_reaches (bound_reaches S) hne

/-- Inserting a bound never shrinks the region covered by the frontier. -/
theorem bound_update_mono (S : Set (Bound ι)) (x : Bound ι) :
    covered (frontier S) ⊆ covered (frontier (insert x S)) :=
  covered_frontier_insert (bound_reaches S) (bound_reaches _)

/-- **The frontier is finite**, for any set of bounds, also an infinite one (Dickson's lemma). -/
theorem bound_frontier_finite (S : Set (Bound ι)) : (frontier S).Finite :=
  WellQuasiOrderedLE.finite_of_isAntichain (frontier_isAntichain S)

end Bounds

/-! ### 4. Links, as DATA

Nothing below is checked against the files it names. -/

/-- The circuit axes named in `worlds/README.md` ("Circuit axes") and on the task card. -/
inductive Axis
  | size | depth | fanOut | nots
  deriving DecidableEq, Repr

instance : Fintype Axis :=
  ⟨⟨[Axis.size, Axis.depth, Axis.fanOut, Axis.nots], by decide⟩, fun x => by cases x <;> decide⟩

/-- DATA: the other axes of `worlds/README.md`, by name. They are not ℕ-valued here. -/
def worldAxes : List String :=
  ["time exponent", "average case", "non-uniformity", "provability", "barriers", "fine-grained"]

/-- DATA: what carries the name L6 (`worlds/README.md`, last section, lists two things; neither is
a table of depth and size rows). -/
def l6Links : List (String × String) :=
  [("L6 time average", "lean/PEqualNP/QuantumGravity/Helpers/FixedPoint.lean"),
   ("L6 MONO lemma (hand proof, unverified)", "notes/general/generalize-open-case.md"),
   ("worlds map", "worlds/README.md")]

/-- The frontier of circuit bounds over the four axes is finite whatever the set. -/
theorem axis_frontier_finite (S : Set (Bound Axis)) : (frontier S).Finite :=
  bound_frontier_finite S

/-- A TOY set over (size, nots), not project data: two incomparable points and one dominated. -/
def toy : Set (Bound (Fin 2)) := {![7, 0], ![5, 1], ![6, 1]}

theorem toy_frontier : frontier toy = {![7, 0], ![5, 1]} := by
  have h1 : ¬ Dominates (![5, 1] : Bound (Fin 2)) ![7, 0] := fun h => by
    have := h.le 1; simp at this
  have h2 : ¬ Dominates (![7, 0] : Bound (Fin 2)) ![5, 1] := fun h => by
    have := h.le 0; simp at this
  have h3 : Dominates (![5, 1] : Bound (Fin 2)) ![6, 1] := by
    rw [dominates_iff]
    exact ⟨fun i => by fin_cases i <;> simp, 0, by simp⟩
  have h4 : ¬ Dominates (![6, 1] : Bound (Fin 2)) ![7, 0] := fun h => by
    have := h.le 1; simp at this
  have h5 : ¬ Dominates (![6, 1] : Bound (Fin 2)) ![5, 1] := fun h => by
    have := h.le 0; simp at this
  ext p
  constructor
  · rintro ⟨hp, h⟩
    rcases hp with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr rfl
    · exact absurd h3 (h _ (.inr (.inl rfl)))
  · rintro (rfl | rfl)
    · refine ⟨.inl rfl, ?_⟩
      rintro q (rfl | rfl | rfl)
      · exact lt_irrefl _
      · exact h1
      · exact h4
    · refine ⟨.inr (.inl rfl), ?_⟩
      rintro q (rfl | rfl | rfl)
      · exact h2
      · exact lt_irrefl _
      · exact h5

end PEqualNP.Methods.Pareto
