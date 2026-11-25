import Mathlib

/-!
# A formal model of one reading of Deleuze's virtual / actual (seat P2)

HONESTY. This file models readings; it claims nothing about what Deleuze meant. The readings are
contested (Badiou, DeLanda, Duffy, Smith differ). Each definition names the reading it follows.

Sources: Aristotle, *Metaphysics* Theta (potentiality / actuality); Deleuze, *Difference and
Repetition* ch. 4 (virtual / actual, problems, the differential); Bergson (virtual vs possible);
Lautman (problems and their solutions); DeLanda, *Intensive Science and Virtual Philosophy*
(vector fields, singularities, phase space); D. W. Smith (the differential, problematics).
Everything lives in a finite-dimensional real normed space `E`; no manifolds.
-/

namespace PEqualNP.Philosophy.Deleuze

open Filter Topology

/-! ### 1. The possible (Aristotle; Bergson's and Deleuze's target) -/

/-- The possible, as a set of candidates (Aristotle's potentiality read as Bergson/Deleuze
criticise it: a pre-formed list of what could be real). -/
abbrev Possible (α : Type*) := Set α

/-- Realization is selection from the possible: a real thing is a member of the possible
(Deleuze, D&R ch. 4: the possible is realised by "limitation"). -/
def realize {α : Type*} (P : Possible α) (x : α) (_h : x ∈ P) : α := x

/-- What is realised resembles the possible: it was already in it. This triviality is Deleuze's
point: the possible is a pre-formed copy of the real, so realization creates nothing. -/
theorem realize_mem {α : Type*} (P : Possible α) (x : α) (h : x ∈ P) : realize P x h ∈ P := h

/-! ### 2. The virtual as problem (Lautman; DeLanda) -/

section Problems

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A problem, read as a vector field on phase space (DeLanda; Lautman: a problem is the field of
tendencies whose solutions are its actualisations). -/
structure Problem (E : Type*) where
  /-- the vector field -/
  field : E → E

/-- The actual: the singular points (zeros) of the field, read as the problem's solutions
(DeLanda: singularities as the topological features that organise a phase space). -/
def actual (P : Problem E) : Set E := {x | P.field x = 0}

/-- A trajectory (integral curve) of a problem: a curve whose velocity is the field (DeLanda:
trajectories in phase space). -/
structure Trajectory (P : Problem E) where
  /-- the curve -/
  curve : ℝ → E
  /-- velocity equals the field along the curve -/
  hasDeriv : ∀ t, HasDerivAt curve (P.field (curve t)) t

/-- A singular point (an actual solution) gives a stationary trajectory. -/
def Trajectory.const (P : Problem E) (x : E) (hx : x ∈ actual P) : Trajectory P where
  curve := fun _ => x
  hasDeriv := fun t => by
    have h : P.field x = 0 := hx
    simpa [h] using hasDerivAt_const t x

/-! ### 3. Non-resemblance: the virtual exceeds the actual -/

/-- Rescaling a problem by a nonzero scalar. -/
def Problem.smul (c : ℝ) (P : Problem E) : Problem E := ⟨fun x => c • P.field x⟩

/-- Same actual solutions for a nonzero rescaling (Bergson/Deleuze: the virtual is not
resembled by its actualisations). -/
theorem actual_smul {c : ℝ} (hc : c ≠ 0) (P : Problem E) :
    actual (P.smul c) = actual P := by
  ext x; simp [actual, Problem.smul, hc]

/-- A nonzero field and its double are different problems with the same actual solutions. -/
theorem distinct_problems_same_actual (P : Problem E) (hP : ∃ x, P.field x ≠ 0) :
    P.smul 2 ≠ P ∧ actual (P.smul 2) = actual P := by
  refine ⟨?_, actual_smul (by norm_num) P⟩
  intro h
  obtain ⟨x, hx⟩ := hP
  have := congrArg (fun Q : Problem E => Q.field x) h
  simp only [Problem.smul] at this
  apply hx
  have h2 : (2:ℝ) • P.field x = (1:ℝ) • P.field x := by simpa using this
  have : ((2:ℝ) - 1) • P.field x = 0 := by rw [sub_smul]; simp [h2]
  exact (smul_eq_zero.1 this).resolve_left (by norm_num)

/-- The map from problems to their actual sets is not injective: the virtual is not recoverable
from its actualisations (needs a nonzero field to exist, i.e. `E` nontrivial). -/
theorem actual_not_injective [Nontrivial E] : ¬ Function.Injective (actual (E := E)) := by
  intro hinj
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let P : Problem E := ⟨fun _ => v⟩
  have ⟨hne, heq⟩ := distinct_problems_same_actual P ⟨0, hv⟩
  exact hne (hinj heq)

/-! ### 4. Difference in itself: the differential (Deleuze D&R ch. 4; Smith) -/

variable [FiniteDimensional ℝ E]

/-- A singular point is nondegenerate when the field has an invertible strict derivative there
(Smith on the differential: the local linear relation `dy/dx` that is determinate though the
quantities vanish). -/
def Nondegenerate (P : Problem E) (x : E) : Prop :=
  P.field x = 0 ∧ ∃ L : E ≃L[ℝ] E, HasStrictFDerivAt P.field (L : E →L[ℝ] E) x

/-- Actualisation is differenciation into distinct points: a nondegenerate solution is isolated,
i.e. there is a neighbourhood containing no other solution. -/
theorem nondegenerate_isolated (P : Problem E) {x : E} (h : Nondegenerate P x) :
    ∃ ε > 0, ∀ y ∈ Metric.ball x ε, y ∈ actual P → y = x := by
  obtain ⟨hx0, L, hL⟩ := h
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hev := hL.eventually_left_inverse
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun y hy hya => ?_⟩
  have h1 := hball (by simpa [dist_comm] using hy)
  have hya' : P.field y = 0 := hya
  rw [hya', ← hx0] at h1
  exact h1.symm.trans hL.localInverse_apply_image

end Problems

/-! ### 5. Multiplicity (Deleuze D&R ch. 4, from Riemann; DeLanda ch. 1) -/

/-- The dimension of a multiplicity (the number of independent directions of variation). -/
noncomputable def dimension (E : Type*) [AddCommGroup E] [Module ℝ E] : ℕ := Module.finrank ℝ E

/-- Multiplicities of different dimension are not linearly isomorphic: difference in kind, not in
degree. -/
theorem not_linearEquiv_of_dimension_ne {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (h : dimension E ≠ dimension F) : IsEmpty (E ≃ₗ[ℝ] F) :=
  ⟨fun e => h (LinearEquiv.finrank_eq e)⟩

/-! ### 6. Intensity (Deleuze D&R ch. 5; DeLanda ch. 2: intensive vs extensive) -/

/-- An extensive magnitude: a sum over a finite region (volume, mass). -/
def extensive (f : ℕ → ℝ) (s : Finset ℕ) : ℝ := ∑ i ∈ s, f i

/-- An intensive magnitude: a mean over a finite region (temperature, density). -/
noncomputable def intensive (f : ℕ → ℝ) (s : Finset ℕ) : ℝ := (∑ i ∈ s, f i) / s.card

/-- Extensive magnitudes add under disjoint union. -/
theorem extensive_union (f : ℕ → ℝ) {s t : Finset ℕ} (h : Disjoint s t) :
    extensive f (s ∪ t) = extensive f s + extensive f t :=
  Finset.sum_union h

/-- Intensive magnitudes do not: two regions at temperature 1 joined are not at temperature 2. -/
theorem intensive_not_additive :
    ∃ s t : Finset ℕ, Disjoint s t ∧
      intensive (fun _ => 1) (s ∪ t) ≠ intensive (fun _ => 1) s + intensive (fun _ => 1) t := by
  refine ⟨{0}, {1}, by decide, ?_⟩
  simp [intensive]

end PEqualNP.Philosophy.Deleuze
