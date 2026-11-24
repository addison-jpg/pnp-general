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
