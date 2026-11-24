# MergeSDR certificates (Python finds, Lean checks)

`export.py` computes, for each circuit in `INSTANCES`, the menu of merge sets `M_z(w)` over all zero points (w951
`systems.system` + `systems.merges`), finds one zero point per set with pairwise disjoint merge sets (backtracking), and
writes the circuit, the points and the merge sets as Lean literals. `lean/PEqualNP/W951/SDRWitness.lean` is its output
(with the module header); every merge set is recomputed by the kernel (`decide`), so nothing from Python is trusted.

Regenerate: `cd 951/tools/sdrcert && python3 export.py /tmp/sdr.lean` (optionally a list of instance names), then paste
the output into `SDRWitness.lean` between the header and `end`. Add a circuit: one line in `INSTANCES`.

Current certificates (`n`, gates, sets, menu sizes, chosen merge sets):
- cfgI: n = 9, 25 gates, 3 sets, menus 5/3/2; {28,29,33}, {12,13,15}, {22}
- adv3: n = 12, 43 gates, 3 sets, menus 13/17/14; {18,21,27}, {14,19,50}, {15,39,53}
- adv4: n = 8, 22 gates, 2 sets, menus 3/3; {8,16,23}, {10,19,20}
- ce3: n = 8, 34 gates, 4 sets, menus 5/5/6/7; {10,17}, {32,34}, {11,26}, {39,40}
- hard4: n = 6, 9 gates, 2 sets, menus 1/2; {6,7,12}, {8,14}
- cxr: n = 8, 24 gates, 2 sets, menus 9/9; {12,13,14}, {28,29,30}
Correctness of the circuits (each output computes OR(S_w)) is checked in Python (w951 `is_correct`); in Lean it costs
about 25 s per circuit with n = 8 and grows as 2^n: `SDRWitnessCorrect.lean` checks it, with the set conditions,
for the five circuits with n <= 9 (about 2 minutes); ADV3 (n = 12, about 20 minutes) stays Python-checked.
