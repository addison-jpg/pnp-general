# referee_b: Python pre-check for sub-lane B (no_minCE, merge-tree charging)

Python = discovery + witness preparation, NOT proof authority; anything landed in Lean still needs `lake build`, no `sorry`, clean `#print axioms`.

`check_charge.py` takes a candidate charge (JSON: circuit, {gate: {set: weight}}, optional demand) and returns a JSON verdict: circuit correctness on all inputs, merge gates per set, per-gate load (must be <= 1), per-set coverage (must reach demand), PASS/FAIL. Exact rationals.

```bash
cd one-not/tools/referee_b && python3 -I check_charge.py example_cxr_split.json
```

`example_cxr_split.json` and `example_cxr_double.json` both FAIL: on cxr no charge supported on the 3rd+ merge gates alone works. `support_survey.py` asks where a charge can go (max flow, gate capacity 1). Other scripts here: `dichotomy.py`, `f2_test.py`, `i1_count.py`, `lifted_union.py`, `mu_slack.py`, `puresdr_check.py`.
