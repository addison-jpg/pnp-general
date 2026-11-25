# qg-d2: cTAHG's elim_vs_gain.py on the full corpus (13:58 UTC; cTAHG request 13:57; script unchanged, main e6a225d)
Run: python3 -I research/one-not/tools/kill_tests/elim_vs_gain.py --corpus <data-corpora, front w7/w8/w8b/chk/w9, research/one-not/data/witnesses>, Q = {}.
Output per circuit: research/one-not/data/ucert/elim_vs_gain.jsonl.gz. 46,097 correct one-NOT circuits (all n, deduplicated by the script).
- GE (some v with elim1(v) >= cost(v)): 46,097 / 46,097, 0 failures. F2 step: 46,089 (8 GE without step; never step without GE).
- best = max_v (elim1 - cost): min 2; distribution 2: 600, 3: 1,513, 4: 5,487, 5: 9,418, 6: 12,138, 7: 6,558, 8: 119, >= 10: 10,263.
- TIGHT (s <= base + 3): 2,112 circuits, all GE, and best = s - base EXACTLY on every one (599 at slack 2, 1,513 at slack 3).
  Overall best >= s - base on 46,029 / 46,097.
- CORRECTION (13:59 UTC, qg-d2): the earlier CAUTION here ("GE looks circular at a MinCE") was WRONG and is withdrawn. GE failing at a
  minimal counterexample is by design: MinCE.elim_lt gives elim1(v) <= cost(v) - δ there, which is exactly how GE for all correct
  circuits closes 951 (no_minCE_of_elimStep). What the tight data does say: at the best v the margin elim1 - cost equals the slack
  s - base exactly (all 2,112 circuits with s <= base + 3), i.e. x_v := 1 removes exactly cost + slack gates and the restriction is
  tight again. So a proof of GE has no room for loss: it must count the eliminated gates exactly, as a tight gate-elimination step.
  GE also holds on MATCH-C, where the F2 step fails at every point (cTAHG-slack.md), so on present data GE is the weaker, safer target.
