import PEqualNP.W951.CrossWorld

/-! CrossWorldCex: hypothesis (ii) of `CrossWorldAt.ndep` cannot be dropped even for circuits with
every minimality property of a MinCE that is a property of the circuit alone (tractability's
question, 09:08).

The question was whether, at a MinCE, a cross-world gate under hypothesis (i) alone is N-dependent
(`MinCE.crossWorld_ndep`), via hypothesis (ii) `C0(g)(Zof (S a)) = 0` for every merge gate `g` of `a`
at a world-0 zero point. On the corpus (34,064 one-NOT circuits: front's allcirc + chist + cxrb +
scaffold's data-corpora; script and results: see the board entry) both fail:
* (ii) fails for some merge gate at a world-0 point in 1,476 circuits, 155 of them live (every gate
  read or an output), essential and clean;
* a cross-world gate under (i) is N-INDEPENDENT in 174 circuits, 60 of them live, essential, clean.
No failure among the essential clean circuits with `s - base ≤ 4` (842 circuits): every failure
of the live essential clean kind has `s - base ≥ 5`.

`cx3_counterexample` is the smallest live essential clean failure (scaffold corpus
`ess/ess_k4e_clean.jsonl:627`), checked here by `decide`: `n = 4`, sets the edges `{0,1}, {0,2},
{0,3}, {1,2}, {1,3}` of `K4` minus `{2,3}`, 10 gates (one NOT, reading `h = x0 ∨ x2`), all outputs
correct, every gate read or an output, no gate a copy of an earlier wire (`MinCE.clean`), and the NOT
gate essential (`MinCE.essential`). Wire `6 = x0 ∨ x1 ∨ x3` is the merge of `{0,1}` at the world-0
point `e2` and of `{1,3}` at the world-1 point `0`, `0` vanishes on `{0,1}` (hypothesis (i)), `C0`
of wire `6` is `1` at `Zof {0,1}` (hypothesis (ii) fails), and wire `6` is N-independent.
So `MinCE.crossWorld_ndep` needs a property of a MinCE beyond `clean`, `live` and `essential`
(near-optimality: the data has no failure with `s - base ≤ 4`). -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- `cx3`: wires `0-3` inputs; `4 = x0 ∨ x3`, `5 = x0 ∨ x2`, `6 = x1 ∨ 4`, `7 = x3 ∧ 5`,
`8 = ¬ 5`, `9 = x0 ∨ x1`, `10 = x1 ∨ 7`, `11 = 8 ∨ 10`, `12 = x1 ∨ x2`, `13 = 6 ∧ 11`. -/
def cx3Gates : List Gate :=
  [⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [3, 5]⟩,
    ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [6, 11]⟩]

/-- The sets of `cx3`: `{0,1}, {0,2}, {0,3}, {1,2}, {1,3}`. -/
def cx3S : Fin 5 → Finset (Fin 4) := ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}]

/-- The outputs of `cx3`. -/
def cx3Out : Fin 5 → ℕ := ![9, 5, 4, 12, 13]

/-- The point `e2`. -/
def cx3E2 : Fin 4 → Bool := fun i => decide (i = 2)

set_option maxRecDepth 10000 in
theorem cx3_hyps : ProblemHyps cx3S cx3Gates cx3Out := by
  refine ⟨by decide, by decide, ?_, ?_, by decide⟩
  · intro g hg
    simp only [cx3Gates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro i1 i2 h1 h2 e1 e2
    simp only [cx3Gates, List.length_cons, List.length_nil] at h1 h2
    interval_cases i1 <;> interval_cases i2 <;> simp_all [cx3Gates]

set_option maxRecDepth 10000 in
/-- **(ii) is necessary even for live, essential, clean circuits.** -/
theorem cx3_counterexample :
    ProblemHyps cx3S cx3Gates cx3Out ∧
      -- live: every gate is read by a gate or is an output
      (∀ k < cx3Gates.length, (∃ w, cx3Out w = 4 + k) ∨
        ∃ j < cx3Gates.length, 4 + k ∈ (cx3Gates.getD j ⟨GateOp.or, []⟩).inputs) ∧
      -- clean (`MinCE.clean`): no gate computes the same function as an earlier wire
      (∀ k j : ℕ, k < cx3Gates.length → j < 4 + k →
        ¬ ∀ x : Fin 4 → Bool, val cx3Gates x (4 + k) = val cx3Gates x j) ∧
      -- essential (`MinCE.essential`): both constant-NOT circuits are wrong
      (¬ ∀ (w : Fin 5) (x : Fin 4 → Bool),
        val (cx3Gates.map (constNot GateOp.or)) x (cx3Out w) = decide (∃ v ∈ cx3S w, x v = true)) ∧
      (¬ ∀ (w : Fin 5) (x : Fin 4 → Bool),
        val (cx3Gates.map (constNot GateOp.and)) x (cx3Out w) = decide (∃ v ∈ cx3S w, x v = true)) ∧
      -- the cross-world gate, hypothesis (i), the failure of (ii), N-independence
      CrossWorldAt cx3S cx3Gates 6 0 4 cx3E2 (fun _ => false) ∧
      (∀ v ∈ cx3S 0, (fun _ : Fin 4 => false) v = false) ∧
      val (C0 cx3Gates) (Zof (cx3S 0)) 6 = true ∧ ¬ NDep 4 cx3Gates 6 := by
  refine ⟨cx3_hyps, by decide, ?_, by decide, by decide,
    ⟨by decide, ⟨by decide, ?_, by decide⟩, ⟨by decide, ?_, by decide⟩⟩, by decide, by decide, ?_⟩
  · intro k j hk hj
    simp only [cx3Gates, List.length_cons, List.length_nil] at hk
    interval_cases k <;> interval_cases j <;> decide
  · intro p hp hn
    simp only [cx3Gates, List.length_cons, List.length_nil] at hp
    interval_cases p <;> first | decide | simp [cx3Gates] at hn
  · intro u hu p hp hn
    simp only [cx3Gates, List.length_cons, List.length_nil] at hp
    have hu' : u = 1 ∨ u = 3 := by simpa [cx3S] using hu
    rcases hu' with rfl | rfl <;> interval_cases p <;> first | decide | simp [cx3Gates] at hn
  · rintro ⟨x, hx⟩
    revert x
    decide

end PEqualNP.Outside.L_meta_951_aux
