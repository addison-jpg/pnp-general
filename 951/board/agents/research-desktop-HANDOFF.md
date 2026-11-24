> **OFF THE ROUTE (main, 2026-11-24 14:45): handoff notice from 08:50, delivered. Kept for the record; do not build on it.**

# HANDOFF: research-desktop -> research (session_01GmnDhdzjMKChKGfUadQDVf), 08:50

Owner 08:28/08:29 (relayed by Coord + warden): "1to1 squish, research -> research". Nothing is running in research-desktop.
Done, all on addison-jpg/pequalnp-work:
1. Resolution gadget, general form, Lean-checked (no sorry, clean axioms, board owner rebuilt it): branch gadget-research @ 5844d46,
   lean/PEqualNP/W951/Gadget.lean + research/gadget/STATEMENT.md; summary agents/research-desktop-gadget.md.
   OPEN: strict (A|y)&(A|~y) for MinCE (StrictGadget Prop); "dies under restriction" needs a W951Cube restriction lemma. Awaiting coord merge review.
2. Lemma K: an independent cross-check of the landed coord-951 19601c9 passed: agents/research-desktop-review-lemmaK.md.
   Branch lemmaK-research f47e66a is an ABANDONED duplicate. Do not merge it.
3. f_G / edge-function lane (Note 1), branch mirror/happy-hypatia-zz54tp, research/research/pnp-subproblem/:
   - Lean-checked S1, S4 and S2 (biclique-cover circuit with exact size, no NOT).
   - The s = bcs conjecture is the single level conjecture; Jukna TR05-021 and KPS arXiv:2603.28954 show it is false for large n.
   - Wegener 1987 has no |E|+tau-1. The Bublitz value s = 7 matches the printed value.
   - Lit reports: lit/GRAPH-COMPLEXITY.md and lit/EXACT-MINIMALITY.md.
4. board-unified (paused): lit/L4-primary-sources.md (39 papers; corrections A-F applied by the lead) and lit/L5-quantum-computing.md.
Tooling here: Lean 4.36 + the Mathlib cache are installed; python-sat; the synth2.py exact-SAT encoder (cross-checked n <= 5).
