import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.F2Induct
import PEqualNP.W951.MinCERewire

/-!
# C2Gap: conjecture C2 as a Lean gap, and C2 ⇒ no minimal counterexample

Task board `boards/tasks/c2-under-no-rewire.md` (README item C2). A **gap**: a statement written in Lean
that still needs a proof (a `Prop` definition, no `sorry`).

* `AllRead n gates out`: every gate is read by a gate or is an output.
* `NoRewire S gates out` (no gate-saving rewiring, R6): no single rewire of a gate input that keeps every
  output correct leaves a gate unread.
* **`C2Stmt`** (OPEN): every correct one-NOT circuit on (1,1)-disjoint sets of size at least 2, with every
  gate read and no gate-saving rewiring, has at every cube `Q` with positive base a point `v ∉ Q` whose
  step over real-witness gates (F2) gains at least its cost (`GainF2`).
* `MinCE.allRead` (from `MinCE.no_dead`), `MinCE.noRewire` (from `MinCE.no_rewire`): a minimal
  counterexample satisfies both hypotheses.
* **`no_minCE_of_C2`**: `C2Stmt` ⇒ no minimal counterexample (via `no_minCE_of_gainF2`), so `C2Stmt`
  closes `no_minCE`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- Every gate is read by some gate or is an output (`n` inputs). -/
def AllRead {m : ℕ} (n : ℕ) (gates : List Gate) (out : Fin m → ℕ) : Prop :=
  ∀ k < gates.length, (∃ g ∈ gates, n + k ∈ g.inputs) ∨ ∃ w, out w = n + k

section C2Gap

variable {n m : ℕ}

/-- **No gate-saving rewiring** (R6): every single rewire of a gate input that keeps every output
correct leaves every gate read. -/
def NoRewire (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) : Prop :=
  ∀ j pos f : ℕ, (∀ (w : Fin m) (x : Fin n → Bool),
      val (rewire gates j pos f) x (out w) = decide (∃ v ∈ S w, x v = true)) →
    ∀ k < gates.length, (∃ g ∈ rewire gates j pos f, n + k ∈ g.inputs) ∨ ∃ w, out w = n + k

/-- **Conjecture C2** (OPEN, a gap): under every gate read and no gate-saving rewiring, the point step
over real-witness gates holds at every cube with positive base. -/
def C2Stmt : Prop :=
  ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
    (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) → AtMostOneNot gates →
    (∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)) →
    AllRead n gates out → NoRewire S gates out →
    ∀ Q, 0 < baseDQ S ∅ Q → ∃ v, v ∉ Q ∧ GainF2 gates S Q v

namespace MinCE

variable {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- A minimal counterexample reads every gate. -/
theorem allRead (M : MinCE S gates out) : AllRead n gates out := by
  intro k hk
  by_contra h
  push Not at h
  exact M.no_dead gates out le_rfl M.ce.hg M.ce.hU M.ce.hev hk h.1 h.2

/-- A minimal counterexample has no gate-saving rewiring. -/
theorem noRewire (M : MinCE S gates out) : NoRewire S gates out := by
  intro j pos f hev' k hk
  by_contra h
  push Not at h
  exact M.no_rewire j pos f hev' hk h.1 h.2

end MinCE

/-- **C2 closes 951**: `C2Stmt` ⇒ no minimal counterexample. -/
theorem no_minCE_of_C2 (H : C2Stmt) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  unfold C2Stmt at H
  exact no_minCE_of_gainF2 fun n m S gates out M =>
    H n m S gates out M.ce.h2 M.ce.hS M.ce.hg M.ce.hU M.ce.hev M.allRead M.noRewire

end C2Gap

end PEqualNP.Outside.L_meta_951_aux
