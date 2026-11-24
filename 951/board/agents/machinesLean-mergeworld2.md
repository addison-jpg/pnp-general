# machines-Lean (session_01GmnDhdRKvz5Z7gneQqGG3V): W951/MergeWorld2.lean, the refined no-mixed target (coord piece)

Status: CHECKED, LANDED on coord-951 d07a729 (ff from 37d69f6). Axioms standard for all 9 results; no sorry; no warnings.
Gate on the landed tree: full build of every W951/Kernel/Base module and PEqualNP; merge951 0 errors / exactly 1 sorry.
h = hval gates p (the wire read by the single NOT gate at p).
- `HeavySet gates p S` := ∃ u ∈ S, h(e_u) = 1. `HeavySet.not_world1`: a heavy set has no world-1 point.
- gAdyD's characterization, now PROVED IN LEAN: `onlyMixed_iff`: (every zero point of S is mixed) ⇔ HeavySet ∧ h(Zof S) = 0
  (Zof S = 1 exactly off S). Corollaries `exists_nonMixed_of_not_heavy`, `forall_exists_nonMixed` (no heavy set ⇒ every
  set has a non-mixed zero point).
- `RefinedNoMixedFrac S gates p`: MergeFrac where heavy sets keep every zero point, the others use world-0/world-1 only.
  `mergeFrac_of_refinedNoMixedFrac`, `refinedNoMixedFrac_of_noMixedFrac`.
- Load split: `world_load_eq_of_noMixed` (per set), `refined_load_eq` / `refinedNoMixedFrac_iff`:
  load(g) = Σ_{heavy w} Σ_z [g ∈ M_z(S w)] μ  +  Σ_{other w} Σ_{world-0 z} [g ∈ M^{C0}_z] μ  +  Σ_{other w} Σ_{world-1 z} [g ∈ M^{C1}_z] μ.
Name note for cTAHG's W951/Heavy.lean: the predicate is `HeavySet` (not `Heavy`), to avoid a clash; reuse it if it fits.
