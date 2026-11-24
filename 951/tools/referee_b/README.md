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
