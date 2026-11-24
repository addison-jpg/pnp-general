# qg-d2: cTAHG's elim_vs_gain.py on the full corpus (13:58 UTC; cTAHG request 13:57; script unchanged, main e6a225d)
Run: python3 -I 951/tools/kill_tests/elim_vs_gain.py --corpus <data-corpora, front w7/w8/w8b/chk/w9, 951/data/witnesses>, Q = {}.
Output per circuit: 951/data/ucert/elim_vs_gain.jsonl.gz. 46,097 correct one-NOT circuits (all n, deduplicated by the script).
- GE (some v with elim1(v) >= cost(v)): 46,097 / 46,097, 0 failures. F2 step: 46,089 (8 GE without step; never step without GE).
- best = max_v (elim1 - cost): min 2; distribution 2: 600, 3: 1,513, 4: 5,487, 5: 9,418, 6: 12,138, 7: 6,558, 8: 119, >= 10: 10,263.
- TIGHT (s <= base + 3): 2,112 circuits, all GE, and best = s - base EXACTLY on every one (599 at slack 2, 1,513 at slack 3).
  Overall best >= s - base on 46,029 / 46,097.
- CAUTION (reading): at the best v the restriction x_v := 1 keeps the slack: elim1 - cost = s - base means s1(v) = base(Q+v) + (s - base).
  If that pattern holds at a minimal counterexample (s - base < 0), best < 0 there and GE fails. So the corpus supports GE only
  through 951 itself (every corpus circuit has s >= base); it gives no independent evidence for GE at a MinCE. The elimination step
  needs an argument that removing x_v gains MORE than the slack, which the tight data says is not the typical behaviour.
