# pnp-subproblem: independent PureSDR check (coord assignment 11:35)

Checker: `951/tools/referee_b/puresdr_check.py` (own code; no tools/w951, no kill_tests). Definitions = Lean `PureValid`,
`pureI1`, `pureI0`, `runMT` (951/lean/PEqualNP/W951/PureSDR.lean, MergeRunT.lean) in real wire numbers: C_y = NOT output
forced to y; I1 = merge run at zero point Z (y = 1), test points e_u, valid iff Z = 0 on S_w and h(Z) = 0; I0 = merge run at
top_w (y = 0), test points m_u ∪ {u}, valid iff m_u ∩ S_w ⊆ {u} and h(m_u) = 1. Menus: I1 over maximal Z, I0 over all tuples of
minimal m_u (coord: minimal choices suffice). Test points are evaluated as themselves (Lean trRT), not OR-ed with the zero point.
VALIDATION: on the 36 kernel-checked PureSDRWitness circuits, my class for each Lean option equals Lean's literal class
(after real -> lifted wire map liftWire): 181/181 classes match, 0 mismatches.

## Corpus
pequalnp-work data-corpora 2aa9856 (ess, tri, q, climb, fixh16 clean/raw, hard4; 44,623 lines) + every circuit json/jsonl
in pnp-general 951/ (hand-built, w9, instances, sdrcert). Filter: exactly one NOT, n <= 16, correct on all inputs.
**44,713 circuits checked** (duplicates across folders not removed; 5 skipped: n > 16 or not one NOT; 0 incorrect).
NOT the same as scaffold's 75,619: pequalnp-work is no longer reachable from this session, and scaffold has not yet sent its
exact list. The 30,906 missing circuits are scaffold's additional corpora; rerun is one command once the files are on pnp-general.

## Results [computed]
(a) PURE SDR EXISTS on 44,713 / 44,713. 0 failures.
(b) EVERY VALID CLASS HAS EXACTLY d_w = |S_w| - 1 MERGES (all menu options of all sets): 0 violations. No empty menu.
(c) Type-A sets (h(top_w) = 1): 142,257. Colliding menu pairs (option of a type-A set w vs an option of another set w'):
| kind | colliding option pairs | circuits where it occurs | files |
|---|---|---|---|
| (i) I1 vs I1, a Z vanishes at >= 2 points of the other set | 6,668 | 5,019 | 50 |
| (ii) I0 vs I0, some m_u meets the other set | 21,937 | 1,331 | 28 |
| (iii) I1 vs I0 | 870 | 228 | 11 |
| other (outside (i)-(iii)) | 0 | 0 | - |
- NO KIND IS EXCLUDED: (i), (ii) and (iii) all occur. (iii) is the rarest (228 circuits; mostly fixh16 clean 568 pairs, tri_now 52,
  tri_all 48, tri_pasch 48, ess_k4_clean 41; 1 hand-built). Research's lane does not shrink.
- 'other' = 0 confirms on data the Lean disjointness lemmas (disjoint_pureI1_pureI1 / _pureI0_pureI0 / _pureI0_pureI1 with
  their pair conditions): every collision is of an open kind.
Per-file numbers: `951/tools/referee_b/data/puresdr_merged.json`.

## Addendum 12:20: like-for-like with scaffold's 75,619 (scaffold's list, 11:44)
- Scaffold's corpus = A data-corpora (40,533 records, its file list; fixh16_raw NOT included) + B scaffold-951 f15/named.jsonl (14)
  + C tools/w951/tests/instances (25) + D xgen dumps / adv (35,047, scaffold scratchpad only, in no repo); filter one NOT, n <= 12.
- My count on A (minus the 4 hard4 .log lines) + C with n <= 12: 40,554 records = 40,529 + 25, matching scaffold's per-file counts.
  All have a pure SDR (subset of the 44,713 above). Not independently checked: B (14, pequalnp-work unreachable here) and D (35,047).
- MERGE RULE: scaffold counts only OR gates as merges ("an OR gate whose two children carry atom sets from different
  components"); Lean's runMT (and this checker) counts ANY gate whose trace meets >= 2 labels. On these 40,554 circuits,
  0 of 753,321 valid classes contain an AND-gate merge, so the two rules agree on all data. (Not a proof that AND merges never
  occur; a referee point if the PureSDR proof uses 'merges are OR gates'.)
- Scaffold builds I0 only for type-A sets and caps I0 menus at 3000; this checker allows every valid I0 (a superset). Both: 0 failures.

## Distinct classes per set (coord 11:46) [computed; tools/referee_b/i1_count.py, validated 169/169 sets vs puresdr_check]
Corpus: scaffold's A + C, n <= 12: 40,554 circuits, 179,613 sets. Histograms (number of sets):
| count of distinct classes | 1 | 2 | 3 | 4 | max |
|---|---|---|---|---|---|
| (a) I1, D-maximal Z, atoms e_u | 173,766 | 5,847 | 0 | 0 | 2 |
| (b) I1, Lean's wide validity (any Z: h(Z) = 0, Z ∩ S_w = ∅) | 161,448 | 16,963 | 1,191 | 11 | 4 |
| (c) pure classes, (b) ∪ I0 | 129,545 | 45,231 | 4,763 | 74 | 4 |
| (c') pure classes, (a) ∪ I0 | 140,950 | 35,869 | 2,776 | 18 | 4 |
- 'EVERY SET HAS EXACTLY ONE I1 CLASS (D-maximal form)': FALSE on 5,847 sets, ALL of them type-A (h(top_w) = 1).
  Non-type-A sets: exactly one, 58,067 / 58,067 (as W1 predicts: top_w is then the unique D-maximal Z).
  Type-A sets: 1 class on 115,699, 2 on 5,847, never 3+. So per set: <= 2 D-maximal I1 classes + the I0 classes.
- SMALLEST COUNTEREXAMPLE: ess_k4e_clean.jsonl #2721 (n = 4, 11 gates), set [1, 3], type-A: D-maximal Z = {0} gives class {6},
  Z = {2} gives class {11} (real wires). Circuit: data/dmax2_smallest_ess_k4e_clean_2721.json
  {"n": 4, "sets": [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3]], "gates": [["or", 1, 2], ["or", 0, 3], ["or", 3, 4], ["and", 5, 6], ["not", 7], ["and", 0, 6], ["or", 2, 9], ["or", 1, 3], ["or", 0, 1], ["and", 5, 8], ["or", 10, 13]], "outs": [12, 14, 5, 4, 11]}
- scaffold's 2 adv records (inline 11:46, data/scaffold_adv.jsonl): pure SDR on both, classes exact, collisions (i) 3, (ii) 8,704,
  other 0; D-maximal I1 = 1 on all 5 sets.
