import PEqualNP.W951.ContinuousAttach
import PEqualNP.W951.ChainSum

/-!
# The continuous form: what reaches `0 ≤ Phi gates S 0` (README items L5, L6, C2; task continuous-mapping)

`slack` and `Phi` are those of `ContinuousAttach.lean`. Notes: `one-not/board/agents/fable-continuous.md`.

* `nonneg_of_descent_at_neg`: the maximum principle. On any set of states with a rank, if every state of
  NEGATIVE value has a state of smaller rank whose value is no larger, no value is negative.
  (L7 asks for the descent at every non-terminal state; only the negative ones are needed.)
* `slack_nonneg_of_cube_descent_at_neg`, `Phi_zero_nonneg_of_cube_descent_at_neg`: the instance for cubes.
* `Phi_zero_nonneg_of_mixed_descent`: the instance for mixed states `(Q, R)` (points of `Q` set to 1, points
  of `R` set to 0), for an abstract mixed slack `f` with `f ∅ ∅ = slack gates S ∅`.
* `nonneg_of_upLaplacian_le`: the averaged form (the sum over the free points of the one-point changes is
  `≤ 0` at every negative cube).
* `Phi_nonneg_of_slack_nonneg`: the count at every cube gives `0 ≤ Phi p` on `[0, 1]`.

Nothing here proves a descent hypothesis; the hypotheses are the missing arrow.
-/

namespace PEqualNP.Outside.L_meta_951_aux.Continuous

open Finset
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_951_aux

/-- **Maximum principle.** If every state of negative value has a state of smaller rank whose value is
no larger, then no value is negative. -/
theorem nonneg_of_descent_at_neg {α : Type*} (rank : α → ℕ) (f : α → ℤ)
    (hstep : ∀ s, f s < 0 → ∃ s', rank s' < rank s ∧ f s' ≤ f s) :
    ∀ s, 0 ≤ f s := by
  intro s
  induction h : rank s using Nat.strong_induction_on generalizing s with
  | _ k ih =>
    by_contra hneg
    obtain ⟨s', hr, hle⟩ := hstep s (not_le.mp hneg)
    have := ih (rank s') (h ▸ hr) s' rfl
    omega

variable {n m : ℕ}

/-- The maximum principle on cubes: descent is needed only at cubes of negative slack. -/
theorem slack_nonneg_of_cube_descent_at_neg (f : Finset (Fin n) → ℤ)
    (hstep : ∀ Q, f Q < 0 → ∃ Q', Q ⊂ Q' ∧ f Q' ≤ f Q) :
    ∀ Q, 0 ≤ f Q := by
  apply nonneg_of_descent_at_neg (fun Q : Finset (Fin n) => n - Q.card) f
  intro Q hQ
  obtain ⟨Q', hlt, hle⟩ := hstep Q hQ
  refine ⟨Q', ?_, hle⟩
  have hc : Q.card < Q'.card := Finset.card_lt_card hlt
  have hn : Q'.card ≤ n := by simpa using Finset.card_le_univ Q'
  show n - Q'.card < n - Q.card
  omega

/-- Chain to the attachment line, cubes: descent at the cubes of negative slack gives `0 ≤ Φ(0)`. -/
theorem Phi_zero_nonneg_of_cube_descent_at_neg (gates : List Gate) (S : Fin m → Finset (Fin n))
    (hstep : ∀ Q, slack gates S Q < 0 → ∃ Q', Q ⊂ Q' ∧ slack gates S Q' ≤ slack gates S Q) :
    0 ≤ Phi gates S 0 := by
  rw [Phi_zero]
  exact_mod_cast slack_nonneg_of_cube_descent_at_neg (slack gates S) hstep ∅

/-- Chain to the attachment line, mixed states. `f Q R` stands for the slack of the state `(Q, R)`
(the cube `Q` of the circuit with the points of `R` set to 0); only `f ∅ ∅ = slack gates S ∅` is used.
A step enlarges `Q ∪ R` (a 1-step puts a point in `Q`, a 0-step puts it in `R`). -/
theorem Phi_zero_nonneg_of_mixed_descent (gates : List Gate) (S : Fin m → Finset (Fin n))
    (f : Finset (Fin n) → Finset (Fin n) → ℤ) (h0 : f ∅ ∅ = slack gates S ∅)
    (hstep : ∀ Q R, f Q R < 0 → ∃ Q' R', Q ∪ R ⊂ Q' ∪ R' ∧ f Q' R' ≤ f Q R) :
    0 ≤ Phi gates S 0 := by
  rw [Phi_zero, ← h0]
  have key := nonneg_of_descent_at_neg
    (fun s : Finset (Fin n) × Finset (Fin n) => n - (s.1 ∪ s.2).card) (fun s => f s.1 s.2) (by
      rintro ⟨Q, R⟩ hQ
      obtain ⟨Q', R', hlt, hle⟩ := hstep Q R hQ
      refine ⟨(Q', R'), ?_, hle⟩
      have hc : (Q ∪ R).card < (Q' ∪ R').card := Finset.card_lt_card hlt
      have hn : (Q' ∪ R').card ≤ n := by simpa using Finset.card_le_univ (Q' ∪ R')
      show n - (Q' ∪ R').card < n - (Q ∪ R).card
      omega) (∅, ∅)
  exact_mod_cast key

/-- The same with the conclusion `no_minCE`: if in every minimal counterexample a mixed slack with
`f ∅ ∅ = slack ∅` has the descent at its negative states, there is no minimal counterexample. -/
theorem no_minCE_of_mixed_descent
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ f : Finset (Fin n) → Finset (Fin n) → ℤ, f ∅ ∅ = slack gates S ∅ ∧
        ∀ Q R, f Q R < 0 → ∃ Q' R', Q ∪ R ⊂ Q' ∪ R' ∧ f Q' R' ≤ f Q R) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_Phi_zero_nonneg fun n m S gates out M => by
    obtain ⟨f, h0, hstep⟩ := H n m S gates out M
    exact Phi_zero_nonneg_of_mixed_descent gates S f h0 hstep

/-- The averaged form (up-Laplacian): if at every cube of negative value the SUM over the free points
of the one-point changes is `≤ 0`, and the full cube is not negative, no value is negative. -/
theorem nonneg_of_upLaplacian_le (f : Finset (Fin n) → ℤ) (huniv : 0 ≤ f univ)
    (hlap : ∀ Q, f Q < 0 → ∑ v ∈ univ \ Q, (f (insert v Q) - f Q) ≤ 0) :
    ∀ Q, 0 ≤ f Q := by
  apply slack_nonneg_of_cube_descent_at_neg
  intro Q hQ
  have hne : (univ \ Q).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have : Q = univ := by
      ext v; simp only [mem_univ, iff_true]
      by_contra hv
      have : v ∈ univ \ Q := by simp [hv]
      rw [he] at this; simp at this
    rw [this] at hQ; omega
  by_contra hno
  have hpos : ∀ v ∈ univ \ Q, 0 < f (insert v Q) - f Q := by
    intro v hv
    by_contra hle
    apply hno
    refine ⟨insert v Q, Finset.ssubset_insert (by simpa using hv), ?_⟩
    omega
  have := Finset.sum_pos hpos hne
  have := hlap Q hQ
  omega

/-- The count at every cube gives `0 ≤ Φ(p)` on `[0, 1]`. -/
theorem Phi_nonneg_of_slack_nonneg (gates : List Gate) (S : Fin m → Finset (Fin n))
    (h : ∀ Q, 0 ≤ slack gates S Q) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ Phi gates S p := by
  unfold Phi
  apply Finset.sum_nonneg
  intro Q _
  have h1 : (0 : ℝ) ≤ (slack gates S Q : ℝ) := by exact_mod_cast h Q
  have h2 : (0 : ℝ) ≤ 1 - p := by linarith
  positivity

end PEqualNP.Outside.L_meta_951_aux.Continuous
