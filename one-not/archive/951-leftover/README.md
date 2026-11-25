# 951 leftover (archived 2026-11-25)

These two files were the last ones in the old top-level `951/` folder, after it became `one-not/`. They came in through PR #18 after the rename. Nothing in the centre store cites them. They are kept whole, not merged, because:

- `lean/PEqualNP/W951/CanonD1.lean`: all 27 of its declarations also exist under `one-not/lean/` (now in `LiftMore.lean`, section CanonD1). Five differ in text there (`ext_le_ext`, `atom0_le_top`, `disjoint_K0of_K1Z_of_le`, `atom1_not_le_ext_false`, `enumF_cases`); this is the older copy. It is not part of the Lean build.
- `board/agents/research-desktop-lemmaD1.md`: the older version of `one-not/board/agents/research-desktop-lemmaD1.md`. It keeps the explicit counterexample to D1 (`ceGates`, n = 5, h = x_4), which the newer note does not repeat. D1 is refuted; see the newer note and `one-not/DEAD_ENDS.md`.
