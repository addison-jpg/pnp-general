import PEqualNP.QuantumGravity.Helpers.Ctc

/-!
# Reset-to-start cycle (core of PSPACE ⊆ P_CTC)

If a step map reaches a halted configuration from every configuration, and halting is replaced
by a reset to `start`, then every Deutsch-consistent distribution of the reset map is supported
on the orbit of `start`.
-/

namespace PEqualNP.QuantumGravity.Open.CtcReset

open PEqualNP.QuantumGravity PEqualNP.QuantumGravity.Helpers

theorem reset_support_on_start_cycle {α : Type} [Fintype α] (step : α → α) (halted : α → Bool)
    (start : α) (hreach : ∀ a, ∃ t, halted (step^[t] a) = true) (μ : PMF α)
    (hμ : DeutschConsistent (fun a => if halted a then start else step a) μ) :
    ∀ r ∈ μ.support, ∃ t, (fun a => if halted a then start else step a)^[t] start = r := by
  classical
  set f : α → α := fun a => if halted a then start else step a with hf
  -- first halting time
  let τ : α → ℕ := fun a => Nat.find (hreach a)
  have hτ : ∀ a, halted (step^[τ a] a) = true := fun a => Nat.find_spec (hreach a)
  have hmin : ∀ a j, j < τ a → halted (step^[j] a) = false := by
    intro a j hj
    have := Nat.find_min (hreach a) hj
    simpa using this
  have hagree : ∀ a j, j ≤ τ a → f^[j] a = step^[j] a := by
    intro a j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega), hf]
      simp [hmin a j (by omega)]
  have hstart : ∀ a, f^[τ a + 1] a = start := by
    intro a
    rw [Function.iterate_succ_apply', hagree a _ le_rfl, hf]
    simp [hτ a]
  intro r hr
  set T : ℕ := Finset.univ.sup τ + 1 with hT
  obtain ⟨x, hx⟩ := mem_range_iterate_of_consistent hμ T hr
  have hle : τ x + 1 ≤ T := by
    have := Finset.le_sup (f := τ) (Finset.mem_univ x)
    omega
  refine ⟨T - (τ x + 1), ?_⟩
  rw [← hx, ← hstart x, ← Function.iterate_add_apply, Nat.sub_add_cancel hle]
