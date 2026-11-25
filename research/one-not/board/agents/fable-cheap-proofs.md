Serves the asteroid language (task asteroid-cheap-proofs)

# Cheap proofs on top of the asteroid soundness files (main's Fable, 2026-11-24)

Files: `proofs/w951/PEqualNP/W951/AsteroidCheap.lean` (imports AsteroidSound2, Continuous, MinCE) and
`AsteroidCheapMixed.lean` (imports AsteroidMixed only). Build: `lake build PEqualNP.W951.AsteroidCheap`
(12 s on a warm cache), `lake build PEqualNP.W951.AsteroidCheapMixed`. Axioms of every theorem: propext,
Classical.choice, Quot.sound. `no_minCE` is never used; it appears only as the hypothesis `hN`.

## Landed

- `not_isCE_of_slackGe`, `not_minCE_of_slackGe`: SetsOk + `slackGe C 0 0` ⇒ not `IsCE`, not `MinCE`, any outputs.
- `slack_eq_asteroid`: `slack C.toGates C.setFin Q = orWitnessAt C (maskOf Q) − baseAt C (maskOf Q)`.
- `slack_nonneg_of_slackNonnegAll`, `Phi_nonneg_of_slackNonnegAll`: `0 ≤ slack Q` for all `Q`; `0 ≤ Phi p` on [0,1].
- `F2_chain_sum`, `orWitnessAt_chain_sum`: ChainSum instantiated at `F2` along an increasing chain of cubes.
- `hypsB`, `hypsB_sound`: the side conditions of `L_meta_951`, decidable, with soundness (both forms of
  "at most one NOT": the index form `AtMostOneNot` of `IsCE` and the `ι` form of `L_meta_951`).
- `isCE_of_checks`, `exists_minCE_of_hunt_hit`, `not_LMeta951Stmt_of_hunt_hit`, `base_le_gates_of_no_minCE`,
  `base_le_gates_of_LMeta951Stmt`; instance `first_ast_fano_hypsB`.
- Mixed, `r = 0`: `baseMixed_zero`, `hasWitnessMixedNaive_zero`, `mslackVal_zero`, `mslackGe_zero`
  (the last two need the kernel check `naiveAgrees C`).

## Choices

- `hypsB` includes `0 < gates.length`: the `ι` form in `L_meta_951` is false for the empty gate list
  (`Fin 1 → Fin 0` is empty). A correct circuit with a set of 2 points has a gate, but that is not proved here.
- `LMeta951Stmt` is a verbatim copy of the type of `PEqualNP.Outside.L_meta_951`; Final.lean is not imported
  (it is not in the build cache and its theorem carries the open statement).
- NOT gates are counted by position (`notCount`), so two equal NOT gates count twice.

## Next cheapest, not done

1. `asteroid.py`: emit `claim hyps(c) by lean` (`hypsB c = true` by `decide +kernel`) and, in the `_sound`
   module, `isCE_of_checks` / `base_le_gates_of_LMeta951Stmt` next to each `correct(c)`. Python only.
2. `example : LMeta951Stmt := PEqualNP.Outside.L_meta_951` in a file importing Final.lean (one line; pins the
   copy to the original; that file inherits the open statement).
3. Drop `0 < gates.length` from `hypsB`: a correct circuit with a set of ≥ 2 points has a gate (an input wire
   or a missing wire is not the OR of two points). About 20 lines with `val`.
4. `hasWitnessMixed = hasWitnessMixedNaive` for every circuit and state (removes `naiveAgrees` from
   `mslackVal_zero`). Needs: bit `z` of the mask `V` ⇔ `z ⊇ q, z ∩ r = ∅, z ∩ S = ∅`; bit `z` of
   `t >>> 2^u` restricted to `u ∉ z` is `t (z + e_u)`; `anyPair` ⇔ two distinct positions. Not short (≈ 150 lines).
5. A Lean mixed `F2(Q, R)` (restrict the circuit by `R := 0`) and `mslackVal = |F2(Q,R)| − baseDQ S R Q`; then
   `mixedStepAll C = true` would feed `Phi_zero_nonneg_of_mixed_descent`. This is a new definition, not cheap.
6. `kstep_of_slack_nonneg` (ChainTelescope) instantiated with `slack_nonneg_of_slackNonnegAll`: probably 5 lines.
7. `witnessCount` (gates of any type) against a project definition: none exists (`F2` is OR gates only).
