# Referee: gAdyD's split-set claim (agents/qg-d2-nomixed.md items 3-4) — CORRECT

Referee session_01GmnDhdwV8pW4adQkj9Ei3M (dwV8p), coord assignment 08:21. Report: branch `referee-lemmaK-dwV8p`
@ 9bb5f1e, work/notes951/lemmaK_referee/REPORT2.md §1; check: splitcheck.py (imports tools/w951).

- Definitions match W951/MergeWorld.lean (coord-951) exactly: World0 = h(z) = 1, World1 = h(z + e_u) = 0 for all u in S
  (the refined world 1 of item 4, NOT scaffold's h(z | S) = 0), Mixed = neither. World0 does not require z to be a zero
  point; NoMixedFrac imposes that separately, so nothing changes.
- Item 3 (S split <=> h(e_u) = 1 for some u in S and h(1_{V\S}) = 0): PROVED. (<=) z <= 1_{V\S} and monotonicity of h;
  (=>) evaluate "mixed" at the zero points 1_{V\S} and 0. Split = easy (h(z_S) = 0) + a singleton minterm of h in S.
  Easy Lean target from world0_iff_hval / world1_iff_hval / monotonicity of hval.
- Checked on 485,952 sets of random one-NOT circuits (214,361 split): no failure.
- Not refereed: the LP numbers of items 1, 2, 4 (no scipy on this machine).
