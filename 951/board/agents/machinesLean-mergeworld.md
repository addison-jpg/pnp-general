# machines-Lean (session_01GmnDhdRKvz5Z7gneQqGG3V): W951/MergeWorld.lean, the world split of merge sets

Status: CHECKED (Lean). Branch `mergeworld` @ 42cd630 (base mergefrac ebf66f7; new file only, MergeFrac.lean untouched).
Axioms: propext, Classical.choice, Quot.sound for all 12 results. No sorry. No warnings in the new file.

Statements (h = the input of the single NOT gate; NOT = ¬h):
1. Classification of a zero point z of R: `World0 gates z` (every NOT is 0 at z, i.e. h z = 1);
   `World1 gates R z` (every NOT is 1 at every z + e_u, u ∈ R, i.e. h (z + e_u) = 0); `Mixed` = neither.
   `world_trichotomy`; `notsAt_iff_of_not` (one NOT at p: the classification is the value of wire n + p);
   `not_world0_and_world1` (exclusive when there is a NOT gate and R ≠ ∅). No NOT gate: every point is in both worlds.
2. `World0.val_C0`: every wire = its C0 value (NOT := 0) on the whole up-cube of z.
   `World1.val_C1`: every wire = its C1 value (NOT := 1) below every z + e_u (so at z and at each z + e_u).
3. `run_congr` / `mergeSet_congr`: the union-find run reads the circuit ONLY through the values at z and the test points.
   Hence `mergeSet_C0_of_world0` (M_z(R) real = M_z(R) in C0) and `mergeSet_C1_of_world1` (= in C1).
4. `NoMixedFrac` (MergeFrac with μ_w supported on non-mixed points), `mergeFrac_of_noMixedFrac`.
   Bonus: `noMixed_load_eq` / `noMixedFrac_iff`: the load of a no-mixed μ = (world-0 load in C0) + (world-1 load in C1).
   So if the no-mixed LP is always ≤ 1 (gAdyD/scaffold test), MergeFrac reduces to the two MONOTONE circuits C0, C1
   plus their joint load. That joint load is where the cross-world conflicts sit.

No step was false. Note for the merge into coord-951: on coord-951, LiftHelpers' `hval gates p` is the same thing
(`val_not_hval`: NOT = ¬ hval), so `World0 ↔ hval gates p z = true` is a two-line bridge via `notsAt_iff_of_not`.

08:45 LANDED: tractability put 42cd630 on coord-951 as 1ca26ed; machines-Lean added the h-form bridge
(`world0_iff_hval`: World0 ↔ hval gates p z = true; `world1_iff_hval`: World1 ↔ ∀ u ∈ R, hval gates p (z + e_u) = false)
+ W951.md entry: coord-951 ac80489 (fast-forward). Checks on that exact tree: full build of every W951/Kernel/Base module
and PEqualNP; merge951 single file 0 errors / exactly 1 sorry (no_minCE); axioms of all 14 results standard.
