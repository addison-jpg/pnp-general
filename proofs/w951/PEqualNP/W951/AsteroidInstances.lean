import Mathlib
import PEqualNP.W951.Asteroid_first
import PEqualNP.W951.AsteroidSound
import PEqualNP.W951.AsteroidSound2
import PEqualNP.W951.AsteroidCheap
import PEqualNP.W951.ChainTelescope

/-! # Example instances of the asteroid soundness theorems

Sanity instances on the generated module `Asteroid_first` (`asteroid/examples/first.ath`). They live here so
that no library file (`AsteroidSound`, `AsteroidSound2`, `AsteroidCheap`) depends on a generated file. -/

namespace SearchCheck

open PEqualNP.CircuitLowerBounds (Circuit GateOp)
open PEqualNP.Outside.L_meta_951_aux (val F2 F2Wit mem_F2 aliveSets mem_aliveSets baseDQ baseDQ_empty slack)

/-! ## The instance: `asteroid/examples/first.ath` -/

/-- **End to end.** The circuit `tiny` written in `asteroid/examples/first.ath`
(`a = or 0 1`, `b = or a 2`, `c = or 2 3`, `set 0 1 2 -> b`, `set 2 3 -> c`), read as a gate list of the
project, computes its two ORs on every input, in the project's semantics. Proved from the generated
kernel check `Asteroid_first.tiny_claim0 : correctB tiny = true`. -/
theorem first_ast_tiny_correct (w : Fin Asteroid_first.tiny.sets.length)
    (x : Fin Asteroid_first.tiny.n → Bool) :
    Circuit.eval ⟨Asteroid_first.tiny.toGates, Asteroid_first.tiny.outs.getD w 0⟩ (List.ofFn x)
      = decide (∃ v ∈ Asteroid_first.tiny.setFin w, x v = true) :=
  correctB_sound_project Asteroid_first.tiny Asteroid_first.tiny_claim0 (by decide) w x

/-- The same, with everything written out: no `SearchCheck` object in the statement. -/
theorem first_ast_tiny_concrete (x : Fin 4 → Bool) :
    Circuit.eval ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [4, 2]⟩, ⟨GateOp.or, [2, 3]⟩], 5⟩ (List.ofFn x)
        = (x 0 || x 1 || x 2) ∧
    Circuit.eval ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [4, 2]⟩, ⟨GateOp.or, [2, 3]⟩], 6⟩ (List.ofFn x)
        = (x 2 || x 3) := by
  have h0 := first_ast_tiny_correct ⟨0, by decide⟩ x
  have h1 := first_ast_tiny_correct ⟨1, by decide⟩ x
  refine ⟨h0.trans ?_, h1.trans ?_⟩
  · change decide (∃ v ∈ (Finset.univ : Finset (Fin 4)).filter (fun v => v.val ∈ [0, 1, 2]),
      x v = true) = _
    rw [Bool.eq_iff_iff]
    simp [Fin.exists_fin_succ, or_assoc]
  · change decide (∃ v ∈ (Finset.univ : Finset (Fin 4)).filter (fun v => v.val ∈ [2, 3]),
      x v = true) = _
    rw [Bool.eq_iff_iff]
    simp [Fin.exists_fin_succ]

/-! ## The instance: `asteroid/examples/first.ath` -/

theorem first_ast_tiny_setsOk : Asteroid_first.tiny.SetsOk := by
  intro S hS
  simp only [Asteroid_first.tiny, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl <;> decide

/-- `claim forall cubes slack(tiny) >= 0 by lean`, read in the project's definitions -/
theorem first_ast_tiny_slack (Q : Finset (Fin Asteroid_first.tiny.n)) :
    baseDQ Asteroid_first.tiny.setFin ∅ Q
      ≤ (F2 Asteroid_first.tiny.toGates Asteroid_first.tiny.setFin Q).card :=
  slackNonnegAll_sound _ first_ast_tiny_setsOk Asteroid_first.tiny_claim4 Q

/-! ## The instance: `fano` of `asteroid/examples/first.ath` passes the side conditions -/

theorem first_ast_fano_hypsB : hypsB Asteroid_first.fano = true := by decide +kernel

/-- **The unbounded step for a checked literal.** `forall cubes slack(tiny) >= 0` (`tiny_claim4`) gives, by
`ChainTelescope.kstep_of_slack_nonneg`, a step from any cube `Q` to any cube `E` of smaller base with slack `0`. -/
theorem first_ast_tiny_kstep (Q E : Finset (Fin Asteroid_first.tiny.n))
    (hE : slack Asteroid_first.tiny.toGates Asteroid_first.tiny.setFin E = 0)
    (hb : baseDQ Asteroid_first.tiny.setFin ∅ E < baseDQ Asteroid_first.tiny.setFin ∅ Q) :
    ∃ Q', baseDQ Asteroid_first.tiny.setFin ∅ Q' < baseDQ Asteroid_first.tiny.setFin ∅ Q ∧
      slack Asteroid_first.tiny.toGates Asteroid_first.tiny.setFin Q'
        ≤ slack Asteroid_first.tiny.toGates Asteroid_first.tiny.setFin Q :=
  PEqualNP.Outside.L_meta_951_aux.ChainTelescope.kstep_of_slack_nonneg
    (fun Q => baseDQ Asteroid_first.tiny.setFin ∅ Q)
    (fun Q => slack Asteroid_first.tiny.toGates Asteroid_first.tiny.setFin Q) Q E
    (slack_nonneg_of_slackNonnegAll _ first_ast_tiny_setsOk Asteroid_first.tiny_claim4 Q) hE hb

end SearchCheck

#print axioms SearchCheck.first_ast_tiny_concrete
#print axioms SearchCheck.first_ast_tiny_slack
#print axioms SearchCheck.first_ast_fano_hypsB
#print axioms SearchCheck.first_ast_tiny_kstep
