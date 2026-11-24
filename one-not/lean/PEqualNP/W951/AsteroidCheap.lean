import Mathlib
import PEqualNP.W951.AsteroidSound2
import PEqualNP.W951.Continuous
import PEqualNP.W951.MinCE
/-!
# AsteroidCheap: short theorems on top of the asteroid soundness files (task `asteroid-cheap-proofs`)

Each theorem here connects two things that were already proved. Nothing here touches the open statement
`no_minCE`; where it appears it is a HYPOTHESIS (`hN`), never used as a theorem.

1. `not_isCE_of_slackGe`, `not_minCE_of_slackGe`: a circuit literal whose slack claim holds is not a
   counterexample to the Theorem, and not a minimal one, whatever its output wires are.
2. `slack_eq_asteroid`: the Lean `slack` (ContinuousAttach) is asteroid's `orWitnessAt − baseAt`.
   `slack_nonneg_of_slackNonnegAll`, `Phi_nonneg_of_slackNonnegAll`: the kernel check at every cube gives
   `0 ≤ slack` at every cube and `0 ≤ Φ(p)` on `[0, 1]`.
3. `F2_chain_sum`, `orWitnessAt_chain_sum`: the chain sum (ChainSum) for `F2` and for asteroid's count.
4. `hypsB`: a Bool checker for the remaining hypotheses of `L_meta_951`; `hypsB_sound`.
   `isCE_of_checks`: `correctB`, `hypsB` and `gates < base` make the literal a counterexample (`IsCE`).
   `exists_minCE_of_hunt_hit`: then a minimal counterexample exists.
   `base_le_gates_of_no_minCE`: if there is no minimal counterexample, every checked literal has `base ≤ gates`.
   `base_le_gates_of_LMeta951Stmt`, `not_LMeta951Stmt_of_hunt_hit`: the same against the statement of
   `L_meta_951` itself (copied verbatim as `LMeta951Stmt`).
-/
namespace SearchCheck

open PEqualNP.CircuitLowerBounds (Circuit GateOp)
open PEqualNP.Outside.L_meta_951_aux (val F2 baseDQ baseDQ_empty MUF2 card_F2_le F2_mono IsCE MinCE
  AtMostOneNot slack Phi exists_minCE bound_of_forall_not_minCE)

/-! ## 1. A circuit with nonnegative slack is not a counterexample -/

/-- **Not a counterexample.** If the kernel check `slack(c) >= 0` succeeds, the literal is not a
counterexample to the Theorem (`IsCE`), for any choice of output wires. -/
theorem not_isCE_of_slackGe (C : Circ) (hC : C.SetsOk) (h : slackGe C 0 0 = true)
    (out : Fin C.sets.length → ℕ) : ¬ IsCE C.setFin C.toGates out := fun M => by
  have h1 := base_le_gates_of_slackGe C hC h
  have h2 := M.hlt
  omega

/-- **Not a minimal counterexample.** -/
theorem not_minCE_of_slackGe (C : Circ) (hC : C.SetsOk) (h : slackGe C 0 0 = true)
    (out : Fin C.sets.length → ℕ) : ¬ MinCE C.setFin C.toGates out :=
  fun M => not_isCE_of_slackGe C hC h out M.ce

/-! ## 2. asteroid's slack is the Lean `slack` -/

/-- **The two slacks are one.** `slack` of ContinuousAttach, on the translated circuit at the cube `Q`,
is asteroid's `orWitnessAt − baseAt` at the mask of `Q`. -/
theorem slack_eq_asteroid (C : Circ) (hC : C.SetsOk) (Q : Finset (Fin C.n)) :
    slack C.toGates C.setFin Q
      = (orWitnessAt C (maskOf Q) : ℤ) - (baseAt C (maskOf Q) : ℤ) := by
  unfold slack
  rw [card_F2_eq_orWitnessAt C hC, baseAt_eq_baseDQ C hC]

/-- `forall cubes slack(c) >= 0 by lean` gives `0 ≤ slack` at every cube. -/
theorem slack_nonneg_of_slackNonnegAll (C : Circ) (hC : C.SetsOk) (h : slackNonnegAll C = true)
    (Q : Finset (Fin C.n)) : 0 ≤ slack C.toGates C.setFin Q := by
  have h1 := slackNonnegAll_sound C hC h Q
  unfold slack
  omega

/-- `forall cubes slack(c) >= 0 by lean` gives `0 ≤ Φ(p)` for every `p` in `[0, 1]`. -/
theorem Phi_nonneg_of_slackNonnegAll (C : Circ) (hC : C.SetsOk) (h : slackNonnegAll C = true)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ Phi C.toGates C.setFin p :=
  PEqualNP.Outside.L_meta_951_aux.Continuous.Phi_nonneg_of_slack_nonneg _ _
    (slack_nonneg_of_slackNonnegAll C hC h) hp0 hp1

/-! ## 3. The chain sum -/

/-- **Chain sum for `F2`.** Along any increasing chain of cubes `Q 0 ⊆ Q 1 ⊆ …`, the count at the start is
the count at step `N` plus the gates lost at each step. -/
theorem F2_chain_sum {n m : ℕ} (gates : List PEqualNP.CircuitLowerBounds.Gate)
    (S : Fin m → Finset (Fin n)) (Q : ℕ → Finset (Fin n)) (hQ : ∀ i, Q i ⊆ Q (i + 1)) (N : ℕ) :
    (F2 gates S (Q 0)).card = (F2 gates S (Q N)).card
      + ∑ i ∈ Finset.range N, (F2 gates S (Q i) \ F2 gates S (Q (i + 1))).card :=
  PEqualNP.Outside.L_meta_951_aux.ChainSum.card_eq_card_add_sum_gain
    (fun i => F2 gates S (Q i)) (fun i => F2_mono gates S (hQ i)) N

/-- The chain sum for asteroid's count `orWitnessAt`; the gains are counted in the project's `F2`. -/
theorem orWitnessAt_chain_sum (C : Circ) (hC : C.SetsOk) (Q : ℕ → Finset (Fin C.n))
    (hQ : ∀ i, Q i ⊆ Q (i + 1)) (N : ℕ) :
    orWitnessAt C (maskOf (Q 0)) = orWitnessAt C (maskOf (Q N))
      + ∑ i ∈ Finset.range N,
          (F2 C.toGates C.setFin (Q i) \ F2 C.toGates C.setFin (Q (i + 1))).card := by
  rw [← card_F2_eq_orWitnessAt C hC, ← card_F2_eq_orWitnessAt C hC]
  exact F2_chain_sum _ _ Q hQ N

/-! ## 4. The remaining hypotheses of `L_meta_951`, as a kernel check -/

/-- `Circ.SetsOk` as a Bool -/
def setsOkB (C : Circ) : Bool :=
  C.sets.all fun S => decide S.Nodup && S.all fun u => decide (u < C.n)

theorem setsOk_of_setsOkB (C : Circ) (h : setsOkB C = true) : C.SetsOk := by
  intro S hS
  have h1 := List.all_eq_true.mp h S hS
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h1
  exact h1

/-- the number of NOT gates (op code `≥ 2`), counted by position -/
def notCount (C : Circ) : Nat :=
  ((List.range C.gates.length).filter fun k => decide (2 ≤ (C.gates.getD k ⟨0, 0, 0⟩).op)).length

/-- **The side conditions of the Theorem, decidable**: well-formed sets, an output wire per set, at least
one gate, every set has at least 2 points, two sets share at most one point, at most one NOT gate. -/
def hypsB (C : Circ) : Bool :=
  setsOkB C && decide (C.sets.length ≤ C.outs.length) && decide (0 < C.gates.length) &&
  (C.sets.all fun S => decide (2 ≤ S.length)) &&
  ((List.range C.sets.length).all fun i => (List.range C.sets.length).all fun j =>
    i == j || decide (((C.sets.getD i []).filter fun u => (C.sets.getD j []).contains u).length ≤ 1)) &&
  decide (notCount C ≤ 1)

theorem inter_card_le (C : Circ) (i j : Fin C.sets.length) :
    (C.setFin i ∩ C.setFin j).card
      ≤ ((C.sets[i.val]).filter fun u => (C.sets[j.val]).contains u).length := by
  classical
  calc (C.setFin i ∩ C.setFin j).card
      = ((C.setFin i ∩ C.setFin j).map Fin.valEmbedding).card := (Finset.card_map _).symm
    _ ≤ (((C.sets[i.val]).filter fun u => (C.sets[j.val]).contains u).toFinset).card := by
        apply Finset.card_le_card
        intro s hs
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hs
        rw [Finset.mem_inter, mem_setFin, mem_setFin] at hv
        simp [hv.1, hv.2]
    _ ≤ _ := List.toFinset_card_le _

theorem toGate_not_iff (g : Gate) : g.toGate.op = GateOp.not ↔ 2 ≤ g.op := by
  rcases g with ⟨op, a, b⟩
  match op with
  | 0 => simp [Gate.toGate]
  | 1 => simp [Gate.toGate]
  | k + 2 => simp [Gate.toGate]

theorem atMostOneNot_of_notCount (C : Circ) (h : notCount C ≤ 1) : AtMostOneNot C.toGates := by
  intro i1 i2 h1 h2 e1 e2
  by_contra hne
  have l1 : i1 < C.gates.length := by simpa [Circ.toGates] using h1
  have l2 : i2 < C.gates.length := by simpa [Circ.toGates] using h2
  have p1 : decide (2 ≤ (C.gates.getD i1 ⟨0, 0, 0⟩).op) = true := by
    simp only [Circ.toGates, List.getElem_map] at e1
    simpa [List.getD_eq_getElem?_getD, l1] using (toGate_not_iff _).mp e1
  have p2 : decide (2 ≤ (C.gates.getD i2 ⟨0, 0, 0⟩).op) = true := by
    simp only [Circ.toGates, List.getElem_map] at e2
    simpa [List.getD_eq_getElem?_getD, l2] using (toGate_not_iff _).mp e2
  have key := two_le_filter (fun k => decide (2 ≤ (C.gates.getD k ⟨0, 0, 0⟩).op))
    (List.mem_range.mpr l1) (List.mem_range.mpr l2) hne p1 p2
  unfold notCount at h
  omega

/-- the `ι` form of "at most one NOT gate" used in the statement of `L_meta_951` -/
theorem iota_of_notCount (C : Circ) (hpos : 0 < C.gates.length) (h : notCount C ≤ 1) :
    ∃ ι : Fin 1 → Fin C.toGates.length, ∀ i : Fin C.toGates.length,
      (C.toGates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i := by
  have hU := atMostOneNot_of_notCount C h
  have hpos' : 0 < C.toGates.length := by simpa [Circ.toGates] using hpos
  by_cases hex : ∃ i : Fin C.toGates.length, (C.toGates.get i).op = GateOp.not
  · obtain ⟨i0, h0⟩ := hex
    refine ⟨fun _ => i0, fun i hi => ⟨0, ?_⟩⟩
    exact Fin.ext (hU i0 i i0.2 i.2 (by simpa using h0) (by simpa using hi))
  · exact ⟨fun _ => ⟨0, hpos'⟩, fun i hi => absurd ⟨i, hi⟩ hex⟩

/-- **Soundness of `hypsB`**: the hypotheses of `L_meta_951` other than correctness, for `C.setFin` and
`C.toGates`, in the exact shapes of `IsCE` and of `L_meta_951`. -/
theorem hypsB_sound (C : Circ) (h : hypsB C = true) :
    C.SetsOk ∧ C.sets.length ≤ C.outs.length ∧
    (∀ i : Fin C.sets.length, 2 ≤ (C.setFin i).card) ∧
    (∀ i j : Fin C.sets.length, i ≠ j → (C.setFin i ∩ C.setFin j).card ≤ 1) ∧
    AtMostOneNot C.toGates ∧
    (∃ ι : Fin 1 → Fin C.toGates.length, ∀ i : Fin C.toGates.length,
      (C.toGates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i) := by
  simp only [hypsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hs, hlen⟩, hpos⟩, h2⟩, hp⟩, hn⟩ := h
  have hC := setsOk_of_setsOkB C hs
  refine ⟨hC, hlen, ?_, ?_, atMostOneNot_of_notCount C hn, iota_of_notCount C hpos hn⟩
  · intro i
    rw [card_setFin C hC i]
    exact of_decide_eq_true (List.all_eq_true.mp h2 _ (List.getElem_mem i.isLt))
  · intro i j hij
    have h3 := List.all_eq_true.mp (List.all_eq_true.mp hp i.val (List.mem_range.mpr i.isLt)) j.val
      (List.mem_range.mpr j.isLt)
    have hne : i.val ≠ j.val := fun e => hij (Fin.ext e)
    simp only [Bool.or_eq_true, beq_iff_eq, hne, false_or, decide_eq_true_eq,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt,
      List.getElem?_eq_getElem j.isLt, Option.getD_some] at h3
    exact le_trans (inter_card_le C i j) h3

/-- **A hunt hit is a counterexample.** A literal that passes `correctB` and `hypsB` and has fewer gates
than the base is a counterexample to the Theorem in the project's terms (`IsCE`). -/
theorem isCE_of_checks (C : Circ) (hc : correctB C = true) (hh : hypsB C = true)
    (hlt : C.toGates.length < ∑ w, ((C.setFin w).card - 1)) :
    IsCE C.setFin C.toGates (fun w => C.outs.getD w 0) := by
  obtain ⟨-, hlen, h2, hS, hU, -⟩ := hypsB_sound C hh
  exact ⟨h2, hS, toGates_wf C, hU, fun w x => correctB_sound_project C hc hlen w x, hlt⟩

/-- **A hunt hit yields a minimal counterexample** (which `no_minCE` says does not exist). -/
theorem exists_minCE_of_hunt_hit (C : Circ) (hc : correctB C = true) (hh : hypsB C = true)
    (hlt : C.toGates.length < ∑ w, ((C.setFin w).card - 1)) :
    ∃ (n' m' : ℕ) (S' : Fin m' → Finset (Fin n')) (gates' : List PEqualNP.CircuitLowerBounds.Gate)
      (out' : Fin m' → ℕ), MinCE S' gates' out' :=
  exists_minCE _ _ _ (isCE_of_checks C hc hh hlt)

/-- **The day `no_minCE` is proved**: if there is no minimal counterexample (a HYPOTHESIS here), every
literal passing `correctB` and `hypsB` has `base ≤ gates`. -/
theorem base_le_gates_of_no_minCE
    (hN : ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate)
      (out : Fin m → ℕ), ¬ MinCE S gates out)
    (C : Circ) (hc : correctB C = true) (hh : hypsB C = true) :
    ∑ w, ((C.setFin w).card - 1) ≤ C.toGates.length := by
  by_contra hlt
  obtain ⟨n', m', S', gates', out', hM⟩ := exists_minCE_of_hunt_hit C hc hh (not_le.mp hlt)
  exact hN S' gates' out' hM

/-- The statement (type) of `PEqualNP.Outside.L_meta_951`, copied verbatim from Final.lean. -/
def LMeta951Stmt : Prop :=
  ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length

/-- **All hypotheses of `L_meta_951` hold for a checked literal**: from the statement of the Theorem,
`base ≤ gates` for every literal passing `correctB` and `hypsB`, with no further work. -/
theorem base_le_gates_of_LMeta951Stmt (H : LMeta951Stmt) (C : Circ) (hc : correctB C = true)
    (hh : hypsB C = true) : ∑ w, ((C.setFin w).card - 1) ≤ C.toGates.length := by
  obtain ⟨-, hlen, h2, hS, -, hι⟩ := hypsB_sound C hh
  exact H C.n C.sets.length C.setFin h2 hS C.toGates (fun w => C.outs.getD w 0) (toGates_wf C) hι
    (fun w x => correctB_sound_project C hc hlen w x)

/-- **What `hunt` searches for, formally**: a literal passing `correctB` and `hypsB` with fewer gates than
the base refutes the statement of `L_meta_951`. -/
theorem not_LMeta951Stmt_of_hunt_hit (C : Circ) (hc : correctB C = true) (hh : hypsB C = true)
    (hlt : C.toGates.length < ∑ w, ((C.setFin w).card - 1)) : ¬ LMeta951Stmt :=
  fun H => absurd (base_le_gates_of_LMeta951Stmt H C hc hh) (not_le.mpr hlt)

end SearchCheck

#print axioms SearchCheck.not_isCE_of_slackGe
#print axioms SearchCheck.not_minCE_of_slackGe
#print axioms SearchCheck.slack_eq_asteroid
#print axioms SearchCheck.Phi_nonneg_of_slackNonnegAll
#print axioms SearchCheck.F2_chain_sum
#print axioms SearchCheck.orWitnessAt_chain_sum
#print axioms SearchCheck.hypsB_sound
#print axioms SearchCheck.isCE_of_checks
#print axioms SearchCheck.exists_minCE_of_hunt_hit
#print axioms SearchCheck.base_le_gates_of_no_minCE
#print axioms SearchCheck.base_le_gates_of_LMeta951Stmt
#print axioms SearchCheck.not_LMeta951Stmt_of_hunt_hit
