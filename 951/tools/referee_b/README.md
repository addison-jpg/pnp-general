# referee_b: Python pre-check for sub-lane B (no_minCE, merge-tree charging)

Owner's Python rollout (phased): Python = discovery + witness preparation, NOT proof authority; anything landed in Lean
still needs `lake build`, no `sorry`, clean `#print axioms`.

`check_charge.py` takes a candidate charge (JSON: circuit, {gate: {set: weight}}, optional demand) and returns a JSON
verdict: circuit correctness on all inputs, merge gates per set (independent re-implementation of tools/w951
systems.system/merges, for cross-checking), per-gate load (must be <= 1), per-set coverage (must reach demand; default
= number of 3rd+ merges of each |S| >= 4 set), PASS/FAIL. Exact rationals (Fraction), so a verdict is a small,
deterministic witness that a Lean check could consume later.

Examples (front/work/notes951/scripts/w8b/cxr.json, gate 14 = 3rd merge of both 4-sets):
- example_cxr_split.json (1/2 + 1/2 on gate 14): FAIL, each set covered 1/2 < 1.
- example_cxr_double.json (1 + 1 on gate 14): FAIL, gate 14 load 2 > 1.
So on cxr no charge supported on the 3rd+ merge gates alone works: a B rule must charge gates outside them.

Referee use: front's B rules (when they land) are run here on the hand-built family (cxr, cx44_*, cxT*, cxU*, cxP2)
and the 41k data corpora before any paper verdict.

## support_survey.py (09:30): where can a B charge go? [computed, discovery only]
Demand(w) = #3rd+ merge gates of each |S| >= 4 set (canonical z_S). A charge is feasible iff a max flow with gate
capacity 1 meets the total demand when each set may charge only its support:
A = its own 3rd+ merges; B = all its own merge gates; C = gates of cone(out_w); D = cone(out_w) minus the first two
merges of EVERY set.

| corpus | circuits with a 4+-set | A | B | C | D |
|---|---|---|---|---|---|
| hand-built + instances in 951/ (some duplicated across folders) | 43 | 28 | 38 | 43 | 43 |
| scaffold data-corpora (ess, tri, q, climb, hard4; pequalnp-work data-corpora 2aa9856) | 296 | 294 | 296 | 296 | 296 |

Reading for sub-lane B (referee note, not a verdict on any claim):
- Charging inside the merge tree is NOT enough: support B (all own merge gates) fails on the cxU family
  (cxU6, cxU8, cxU_6_4, cxU_8_4) and cxP2. A "double counting over the merge tree" proof must charge some 3rd+ merges
  to gates that are not merge gates of that set.
- Support D (own output cone, excluding every set's first two merges) is feasible on all 339 circuits. Candidate
  statement for front's B lane: "the 3rd+ merge demand of the |S| >= 4 sets has a fractional matching into
  cone(out_w) \ (first two merges of all sets) with gate capacity 1". Data only; and it ignores how those cone gates are
  already used by the rest of the MergeFrac load, so it is a necessary-condition check, not the B inequality.
- Random/SAT corpora almost never stress this (A fails on 2/296; B never fails): the hand-built family is the test set.
Files: data/survey_handbuilt.txt, data/survey_corpora.txt, data/summary_*.json.

## Cross-check and literature (09:44)
- Independent cross-check (Research, w951 systems/merges/cone + own max-flow, none of this code): AGREE on all 339 circuits,
  0 disagreements; checks implementation, not definitions. `951/board/agents/research-referee-b-crosscheck.md`,
  script `951/tools/referee_b_xcheck/`.
- Literature (Research): no printed fractional-Hall / transportation lemma gives the D-shape (own cone minus every set's first
  two merges). Nearest template: Pippenger 1980, "On another Boolean matrix", Lemma 1 (cone-restricted path charging, load
  <= t^2 per edge, no capacity-1 step, no first-two-merges exclusion). Then Wegener 1987 sec 6.6 (Lemma 6.1 / Thm 6.2; check
  the PDF before quoting). Nechiporuk, Mehlhorn-Galil not opened. `951/board/agents/research-hall-charging-lit.md`.
- So the D-shape needs its own proof; Pippenger's Lemma 1 is the model to adapt.
