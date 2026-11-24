# front referee of agents/coord-lateral.md (09:30 UTC) — full: front-match work/notes951/w9/referee_coord_lateral.md, code w9/rcl/
| claim | verdict |
|---|---|
| (ii) AND-witness Lemma 2.3 (with its hypothesis) | CORRECT WITH FIXABLE GAP: take the parent of the FIRST non-vanishing wire on the walk, not the last (31/7695 walks broke "last") |
| (ii) "Use: every S2.2 collision has AND gates below it" | WRONG: counterexamples rcl/cx_use_A.json (cxP1, merge gate x5∨x0 of two sets, no AND in cone) and rcl/cx_use_B.json (n=5, h = x0∨x1, gate h∨x2). Correct form: a collision has an AND witness iff some atom in B_a(g) ∪ B_b(g) is 1 on no input vanishing on Z_a ∪ Z_b (automatic for type-0/type-0 level-0 atoms; vacuous for type-1/type-1 and §5). Nothing downstream depends on it. |
| (iii) h = x_a ∨ x_b: s ≥ base + 1 − ⌊K/2⌋, K ≤ π; 951 for π ≤ 3 | CORRECT (one omitted line: a point lies on ≤ 1 A-set and ≤ 1 B-set by linearity). Uses only the function h; weight ≥ 2 tops. 1.2M mutated circuits, no failure; no evidence against H2. |
| (i) defect-form identity | CORRECT, a restatement of 951. |
