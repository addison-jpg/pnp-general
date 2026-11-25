import PEqualNP.W951.ContinuousAttach

/-!
# Bridge (seat P3): the repository's three levels as a virtual / actual structure

HONESTY. This is a formal analogy between a cited reading of Deleuze (virtual / actual, problem /
solution; DeLanda, *Intensive Science and Virtual Philosophy*; Deleuze, *Difference and Repetition*
ch. 4) and this repository's own definitions `slack` and `Phi`. It claims nothing about what
Deleuze meant and proves nothing about circuits beyond the lemmas stated here (all of them are
about arbitrary integer tables, or are one-line unfoldings of `slack` / `Phi`).

Dependency note: `Problem` and `actual` below are restated from
`lean/PEqualNP/Philosophy/Deleuze.lean` (seat P2, the source), in identical form, because that file
lives in the separate `lean/` Lake project and cannot be imported here.

Levels:
* actual  = finite: the integer `slack gates S Q` at each cube `Q`, and the corner `slack ∅` that
  decides `no_minCE`;
* virtual = polynomial: `Phi gates S`, one continuous function on `[0,1]` that the finite table
  determines and that is actualised again at its corners (`Phi_zero`, `PhiT_one`);
* non-resemblance: the corners do not determine `Phi` (`corners_not_injective`) and `Phi` does not
  determine the table (`PhiT_not_injective`), as `distinct_problems_same_actual` in P2;
* limit  = a named open target, `LimitTarget` (no proof). See BOARD.md, "TOP: THREE LEVELS".
-/

namespace PEqualNP.Philosophy.Bridge

open Finset PEqualNP.Outside.L_meta_951_aux PEqualNP.CircuitLowerBounds

/-! ### Restated from `lean/PEqualNP/Philosophy/Deleuze.lean` (identical form) -/

/-- A problem, read as a vector field on phase space (DeLanda; Lautman). Source: P2. -/
structure Problem (E : Type*) where
  /-- the vector field -/
  field : E → E

/-- The actual: the zeros of the field. Source: P2 (`Deleuze.actual`). -/
def actual {E : Type*} [Zero E] (P : Problem E) : Set E := {x | P.field x = 0}

/-! ### Actual level: a slack table, and its virtual: the polynomial -/

/-- The product-measure average of an arbitrary integer table on the cubes of `Fin n`, same formula
as `Phi`. -/
noncomputable def PhiT {n : ℕ} (t : Finset (Fin n) → ℤ) (p : ℝ) : ℝ :=
  ∑ Q : Finset (Fin n), p ^ Q.card * (1 - p) ^ (n - Q.card) * (t Q : ℝ)

/-- `Phi` is `PhiT` of the slack table: the polynomial level is a function of the finite level. -/
theorem Phi_eq_PhiT {n m : ℕ} (gates : List Gate) (S : Fin m → Finset (Fin n)) :
    Phi gates S = PhiT (slack gates S) := rfl

/-- Corner at 0: the polynomial actualises `t ∅`. -/
theorem PhiT_zero {n : ℕ} (t : Finset (Fin n) → ℤ) : PhiT t 0 = (t ∅ : ℝ) := by
  unfold PhiT
  rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
  · simp
  · intro Q _ hQ
    have : Q.card ≠ 0 := by simpa [Finset.card_eq_zero] using hQ
    simp [zero_pow this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Corner at 1: the polynomial actualises the slack of the full cube. -/
theorem PhiT_one {n : ℕ} (t : Finset (Fin n) → ℤ) : PhiT t 1 = (t Finset.univ : ℝ) := by
  unfold PhiT
  rw [Finset.sum_eq_single (Finset.univ : Finset (Fin n))]
  · simp
  · intro Q _ hQ
    have : Q.card ≠ n := by
      intro h; apply hQ
      exact Finset.eq_univ_of_card Q (by simpa using h)
    have : n - Q.card ≠ 0 := by
      have := Finset.card_le_univ Q
      simp only [Fintype.card_fin] at this
      omega
    simp [zero_pow this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `Phi (1)` is the slack of the full cube. -/
theorem Phi_one {n m : ℕ} (gates : List Gate) (S : Fin m → Finset (Fin n)) :
    Phi gates S 1 = (slack gates S Finset.univ : ℝ) := PhiT_one _

/-- The virtual object attached to a table, as a P2 problem on `ℝ` (the field is `Φ`). -/
noncomputable def virtualOf {n : ℕ} (t : Finset (Fin n) → ℤ) : Problem ℝ := ⟨PhiT t⟩

/-- The actualisation at the corners: the two integers the polynomial meets the finite level in. -/
noncomputable def corners (P : Problem ℝ) : ℝ × ℝ := (P.field 0, P.field 1)

theorem corners_virtualOf {n : ℕ} (t : Finset (Fin n) → ℤ) :
    corners (virtualOf t) = ((t ∅ : ℝ), (t Finset.univ : ℝ)) := by
  simp [corners, virtualOf, PhiT_zero, PhiT_one]

/-! ### Non-resemblance, both directions (instances at `n = 2`) -/

/-- The table `+1` at `{0}`, `-1` at `{1}`, zero elsewhere. -/
def tAnti : Finset (Fin 2) → ℤ := fun Q => if Q = {0} then 1 else if Q = {1} then -1 else 0

/-- The table `1` at `{0}` and zero elsewhere. -/
def tOne : Finset (Fin 2) → ℤ := fun Q => if Q = {0} then 1 else 0

/-- The zero table. -/
def tZero : Finset (Fin 2) → ℤ := fun _ => 0

private theorem sum_fin2 (f : Finset (Fin 2) → ℝ) :
    ∑ Q : Finset (Fin 2), f Q = f ∅ + (f {0} + (f {1} + f {0, 1})) := by
  have : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [this, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by decide)]

theorem PhiT_tAnti (p : ℝ) : PhiT tAnti p = 0 := by
  unfold PhiT
  rw [sum_fin2]
  have h1 : ({0, 1} : Finset (Fin 2)) ≠ {0} := by decide
  have h2 : ({0, 1} : Finset (Fin 2)) ≠ {1} := by decide
  have h3 : ({1} : Finset (Fin 2)) ≠ {0} := by decide
  simp [tAnti, h1, h2, h3]

theorem PhiT_tOne (p : ℝ) : PhiT tOne p = p * (1 - p) := by
  unfold PhiT
  rw [sum_fin2]
  have h1 : ({0, 1} : Finset (Fin 2)) ≠ {0} := by decide
  have h3 : ({1} : Finset (Fin 2)) ≠ {0} := by decide
  simp [tOne, h1, h3]

theorem PhiT_tZero (p : ℝ) : PhiT tZero p = 0 := by simp [PhiT, tZero]

/-- **The virtual does not determine the actual table.** Two different slack tables with the same
polynomial `Φ` (so the same values at every `p`, and the same corners). The finite level carries
information the continuous level forgets. -/
theorem PhiT_not_injective :
    tAnti ≠ tZero ∧ PhiT tAnti = PhiT tZero := by
  refine ⟨?_, funext fun p => by rw [PhiT_tAnti, PhiT_tZero]⟩
  intro h
  have := congrFun h {0}
  simp [tAnti, tZero] at this

/-- The same, as problems in P2's sense: one virtual problem, two different tables. -/
theorem virtualOf_not_injective : ¬ Function.Injective (virtualOf (n := 2)) := fun h =>
  PhiT_not_injective.1 (h (by
    show (⟨PhiT tAnti⟩ : Problem ℝ) = ⟨PhiT tZero⟩
    rw [PhiT_not_injective.2]))

/-- **The actual corners do not determine the virtual.** Two problems with the same corner values
(`Φ(0)`, `Φ(1)`, the values `no_minCE` sees at the ends) but different polynomials. -/
theorem corners_not_injective :
    corners (virtualOf tOne) = corners (virtualOf tZero) ∧ virtualOf tOne ≠ virtualOf tZero := by
  refine ⟨?_, ?_⟩
  · rw [corners_virtualOf, corners_virtualOf]
    have h : (Finset.univ : Finset (Fin 2)) ≠ {0} := by decide
    simp [tOne, tZero, h]
  · intro h
    have := congrArg (fun P : Problem ℝ => P.field (1/2)) h
    simp only [virtualOf] at this
    rw [PhiT_tOne, PhiT_tZero] at this
    norm_num at this

/-! ### The limit level: a named open target (statement only) -/

/-- OPEN, NOT PROVED. The asymptotic statement of BOARD.md "TOP: THREE LEVELS" in the notation of
`Phi`: for every `ε > 0` there is `N` such that every minimal counterexample on `n ≥ N` points has
`Φ(0) ≥ -ε · base`. (The exact, all-`n` statement `0 ≤ Φ(0)` is `no_minCE_of_Phi_zero_nonneg`'s
hypothesis; passing from this asymptotic form to it is the stability step of the plan.) -/
def LimitTarget : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (n m : ℕ), N ≤ n →
    ∀ (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → -(ε * (baseDQ S ∅ ∅ : ℝ)) ≤ Phi gates S 0

end PEqualNP.Philosophy.Bridge
