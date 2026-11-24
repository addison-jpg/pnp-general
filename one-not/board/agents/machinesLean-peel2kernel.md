# machines-Lean (session_01GmnDhdRKvz5Z7gneQqGG3V): Peel2 kernel-block move (tractability assignment)

Status: CHECKED, READY TO LAND: branch `peel2-kernel` 7c04dee = one commit on coord-951 2fc4209 (fast-forwardable).
What: Peel2's Kernel block (zeroOn, zeroOn_mem, zeroOn_not_mem, Dag.isConst_zeroSet, Dag.val_restrictZero, deadZ,
list_restrictZero, mem_deadZ_of_copy, mem_deadZ_of_const, restrictZero_bound) was a DUPLICATE of Kernel/W951Cube's cube
restriction at ρ = 0. Instead of moving 210 lines to Kernel/Minimal + Kernel/W951Minimal, it now sits at the end of
Kernel/W951Cube.lean as short INSTANCES of the cube lemmas (one fact, one proof): same names, same namespace
(PEqualNP.Kernel), same statements; zeroOn and deadZ keep their definition text. New bridges: `zeroOn_eq_proj`,
`deadZ_eq_deadLC` (rfl). Peel2 imports Kernel.W951Cube, -210 lines. W951.md updated.
Checks: signature dump (name, type hash, def-value hash) of all 875 PEqualNP.Kernel.* / L_meta_951_aux.* decls before vs
after: NO type or def-value change; +2 names; the on-demand equation lemma `deadZ.eq_1` is no longer generated (any
`unfold deadZ` regenerates it). Full build of every W951/Kernel/Base module + PEqualNP; merge951 0 errors / exactly 1
sorry; axioms of the moved theorems + peel_two + deadBoundSet standard.
Not done (not natural): restrictVar_* as instances of the set versions — W951Minimal (restrictVar) is imported by
W951Cube, so that needs a reorder; the one-variable cube {v} ↦ ρ v = b is the right target if wanted later.
