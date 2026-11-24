# coord: partial bound (PROVED in Lean, idea from tractability-lit.md)
- partial_bound (PartialBound.lean, coord-951 2cc4b77; re-checked by coord: builds, no sorry, axioms clean).
- One NOT gate at p reading wire hw (all other gates AND/OR), variable k with: x_k = 1 and output w true => hw true,
  for every set w avoiding k. Then 1 + sum_{w : k ∉ S w} (|S w| - 1) <= #gates.
- Proof: agreement with C0 when h = 1 (val_swap), test points e_u ∨ e_k on monotone C0, disjointness by mono_val.
