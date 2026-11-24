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
- hard4s (scaffold's HARD4): n = 6, 10 gates, 2 sets, menus 2/1; {8,11,15}, {6,9}
- uniq0, uniq2 (scaffold's smallest unique-SDR circuits): n = 4, 7 / 8 gates, 3 / 5 sets, every menu of size 1
- cxT2: n = 9, 29 gates, 3 sets, menus 16/10/13; {16,21,25}, {9,14,19}, {10,35,36}
- cxT4: n = 15, 47 gates, 3 sets, menus 190/82/81; {22,27,32,37,43}, {15,20,25,30,35}, {16,57,58,59,60}
Correctness of the circuits (each output computes OR(S_w)) is checked in Python (w951 `is_correct`); in Lean it costs
about 25 s per circuit with n = 8 and grows as 2^n: `SDRWitnessCorrect.lean` checks it, with the set conditions,
for every circuit with n <= 9 (about 2 minutes); ADV3 (n = 12) and cxT4 (n = 15) stay Python-checked.

Group `fixh16` (`python3 export.py OUT --group fixh16`, output in `SDRWitnessFixh16.lean` with correctness bundles): scaffold's
24 forced-h K4 circuits (data-corpora `fixh/fixh16_clean.jsonl`, 0-indexed lines 20, 66, 67, 169-178, 301-304, 1403, 1404,
1873-1877; `s = 16`, where L-flip fails), stored in `fixh16_forced.json`. n = 4, 16 gates, 6 pair sets each; menus of size 1-3.

# PureSDR certificates (`pure_export.py`)

`pure_export.py` builds, for each one-NOT circuit, the menu of PURE classes of `PROOF_PLAN_SUGGESTIONS.md` §0 as
defined in `lean/PEqualNP/W951/PureSDR.lean`: I1(w, Z) (union-find merges in C_1, zero point any Z avoiding S_w with
h(Z) = 0, atoms e_u) and I0(w, m) (merges in C_0, zero point top_w, atoms m_u | e_u, m_u a minterm of h with
m_u ∩ S_w ⊆ {u}, per atom, up to 4000 combinations per set). `tables` and `merges` are those of `kill_tests/canon.py`. It
then finds a pairwise disjoint choice and writes it with the classes as literals in LIFTED wire numbers (real wire
i < n + p is lifted wire i + 1; later wires keep their numbers). The kernel recomputes every class (`pureCls`, `decide`)
and checks validity (`PureValid`), so nothing from Python is trusted. Output: `lean/PEqualNP/W951/PureSDRWitness.lean`.

Regenerate: `python3 pure_export.py /tmp/p.lean` and `python3 pure_export.py /tmp/f.lean --group fixh16`, paste both
between the header and `end`. Current: cxT2, cxe3, ce3, hard4s, cxr, cfgI, adv3, adv4, hard4, uniq0, uniq2, cxT4, and the
24 fixh16 circuits: 36 PureSDRs, all kernel-checked (about 40 s). Pure menus are small (1-10 distinct classes per set).

Group `witness` (`python3 pure_export.py OUT --group witness`): every `*.json` in `951/data/witnesses` (one circuit per file,
dict with name, n, sets, gates, outs). Output in `lean/PEqualNP/W951/PureSDRWitnessLadder.lean`, with a correctness bundle per
circuit for small n. Current: pasch_s14_heavy_atmostone (n = 6, 14 gates, NOT gate 1, menus 1/2/1/2; worlds I1, I0, I1, I0).
