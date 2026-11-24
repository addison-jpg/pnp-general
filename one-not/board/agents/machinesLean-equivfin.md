# machines-Lean (session_01GmnDhdRKvz5Z7gneQqGG3V): audit #13, reindexing lemmas (tractability assignment)

Status: CHECKED, LANDED on coord-951 2883b0a (fast-forward from 19601c9).
- Base/Matching/Hall.lean: `sum_equivFin` (∑ j : Fin s.card, F (s.equivFin.symm j) = ∑ a ∈ s, F a) and
  `sum_equivFin_subtype` (∑ over Fintype.equivFin {a // p a} = ∑ a ∈ univ.filter p, f a). Axioms standard.
- Replaces the hand reindexing (Equiv.sum_comp + sum_subtype / sum_coe_sort) at 8 sites: Core (r0_step),
  MinCEFacts x2 (hsubsum, deadBound h3), MinCEN3 (liveBound1), Peel2, PriceForm, Kernel/W951Minimal, Kernel/W951Cube.
  Only `have` proof bodies changed; no statement changed (diff is proof lines only).
- Checks on the landed tree: full build of every W951/Kernel/Base module and PEqualNP (incl. the new LemmaK);
  merge951 single file 0 errors / exactly 1 sorry (no_minCE).
Side observation for the Peel2 kernel move: the `namespace PEqualNP.Kernel` block in Peel2.lean (restrictZero bound,
eI reindexing at ~l.224) has the same shape as Kernel/W951Cube.lean ~l.237; check for a duplicate before moving it.
