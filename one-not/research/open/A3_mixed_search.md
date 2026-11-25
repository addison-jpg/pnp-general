# A3: mixed-step search on irreducible read-NOT circuits

Script: `one-not/research/open/A3_mixed_search.py` (hill-free random generator: witness starts + OR trees, `extend` adds 1-3 inputs and 1-2 sets, junk, random-order `reduce`; keep correct, one NOT, all gates read, NOT gate read, no gate-saving rewiring (R6 / `no_rewire`), both NOT faces incorrect).
Check per circuit: `continuous.mixed_margin` (numpy) over all 3^n mixed states; MixedStep fails iff margin >= 1. Second, independent evaluation (`asteroid.ext_mixed.direct_mixedstep`, naive) on every circuit with n <= 7 and on any candidate.

## Region covered (4 runs x 1000 s, seeds 11-14, 4 CPUs)
- One NOT gate, irreducible, NOT read (seeds 11, 12, 13; n <= 10, reached n = 8, 9): 34 distinct circuits, 642,978 mixed states, 217,655 with positive base. Least slack seen: 0. Negative-slack states: 0. Worst MixedStep margin: 0 (holds). 
- Up to two NOT gates, no-rewire, all gates read (seed 14, n <= 9; outside the one-NOT theorem, to try to reach negative slack): 14 circuits, 188,082 states, 76,936 positive base. Negative-slack states: 0. Margin 0. Cross-checked by the naive evaluator on the 2 circuits with n = 7 (agree).
- n = 8, 9 circuits have more inputs than the 12 earlier no-rewire circuits (n = 7 to 9) in the same family; yield of irreducible circuits is about 1.2 per 100 reductions, so the sample is small.

## Result
No counterexample in this region. No state of negative slack was reached: every sampled circuit has least mixed slack 0, so this run does not test the missing arrow (mixed step at negative slack); it only extends the evidence where slack is >= 0. Finding nothing proves nothing. Raw logs: `A3_run_seed*.log`.
