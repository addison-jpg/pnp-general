# Index of the agent notes: what is on the route, what is not (main, 2026-11-24 14:45)

Owner, 14:40: "the job now is to kill things at the bottom, but not too fast. we just need all these
parts to come together." A note that is off the route gets a first line `OFF THE ROUTE` and stays; only notes with
no content and no link to them are deleted. Object by one wall line on BOARD.md.

## The route (one proof, four parts)

| Part | Statement | State | Notes that feed it |
|---|---|---|---|
| 1. Lean reduction | `no_minCE` follows from the count `base(Q) ≤ |F2(Q)|` at Q = ∅ | checked: `no_minCE_of_gainF2_or_cubeLocal` (CubeF2.lean:353); cubes where the NOT gate reads one input or is constant are closed | coord-mince, coord-mergerun, coord-twoworld, coord-partialbound, coord-theoremP, machinesLean-*, lpfix-mergefrac-lean, kernel-index, tractability-kernel, tractability-audit |
| 2. The step | GainF2 at every cube Q where the input h of the NOT gate depends on ≥ 2 inputs | FALSE as a statement about correct circuits with R1-R5' and R+ (MATCH-C, fable-f2-nonlocal; also F4 / F5); OPEN only with gates < base in the hypothesis; false without the restriction too (TWIN-TREE) | fable-f2-nonlocal, fable-f2-step, dwV8p-synth-F1-F2, dwV8p-referee-F2-heavy, dwV8p-referee-F2-light, dwV8p-referee-hxp, research-F2-light, qg-d2-ucert, family-table (F4 / F5 pass the suite), front-A2-final-1223, front-A2-starcount, front-heavy |
| 3. The global count | lifted price inequality / LiftSDR for all correct circuits | proved where the U-game is won (Theorem G, paper); OPEN where it is lost (smallest: {0,1,2}, {0,3,4}, h = x1 ∨ x3) | fable-global-price, scaffold-mul-1235, front-A1-2G-lift-1230, dwV8p-referee-lemmaK, research-desktop-review-lemmaK, research-typeA-increment, research-concave-dual, coord-desktop-referee-CU |
| 4. Big picture | three layers; barriers; the NOT gate ladder; physics premises | drafts: SYNTHESIS.md, BIGPICTURE.md | tractability-axis, coord-knot, research-pnp-defs, research-fable-weight |

Parts 2 and 3 are open at the same place: a NOT input h that depends on at least two inputs.

## Literature (reference; not a proof part)
research-lit, research-crawl, research-nominCE-lit, research-hall-charging-lit, research-charging, research-hypergraph-hall,
research-and-replacement, research-negation-influence, research-partial, tractability-lit, research-fable-sokolov, coord-lateral,
front-referee-lateral.

## Off the route, first pass (first line of each file says why)
tractability-angle2, research-desktop-HANDOFF, research-desktop-lemmaD1, research-desktop-lemmaD1-killtest, dwV8p-referee-gadget,
opus-light-count, research-heredity-lit, research-induction-draft, research-typeA-menus, pnp-subproblem-puresdr-check.
Deleted (no content, no link): coord-sun3, scaffold-offer.

## Candidates for the second pass (written before the 12:27 retarget to lifted forms; marked only if nobody objects)
scaffold-hall-stress, scaffold-fable-fracmatch, scaffold-duals, tractability-duals, tractability-review, tractability-nominCE,
front-status, front-frontier, front-mergefrac, front-A2data, front-B-1220, front-C-verdict-1220, front612-supportB,
coord-adv16, coord-cycrank, coord-fixh16, scaffold-data, scaffold-overlap2, scaffold-coneD-opus, scaffold-payment,
scaffold-core-sat, scaffold-mu-ladder, scaffold-mu-ladder-1219, fable-mu-induction, menu-decision-check, referee-pappus,
research-relax, research-cores, research-referee-b-crosscheck, research-desktop-gadget, research-fable-sokolov,
qg-d2-nomixed, qg-d2-xgen, dwV8p-referee-nomixed, coord-desktop-referee-angle1, coord-desktop-referee-plan,
pnp-subproblem-referee-angle2, machinesLean-mergeworld2.
A note here that states a refutation is the record of that refutation: its result must be a row of 951/DEAD_ENDS.md before it is marked.
