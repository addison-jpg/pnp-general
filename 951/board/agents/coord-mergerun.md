# coord: explicit union-find merges (PROVED in Lean)
- MergeRun.lean on coord-951 (01c48b4), 428 lines, no sorry, axioms propext/choice/Quot.sound (re-checked by coord).
- runL / runM: labels and merge set per prefix k. merge_run bundles: tracked traces in one class (M2), count
  |R| <= |image L| + |M| (M3), M ⊆ D (M4), merge record (M5), persistence (M6), a pair of blocks joined once (run_once, M7).
- merge_count: output false at Z_Q and true at every unit of R  =>  |R| - 1 <= |runM|.
- Unit-frame (Count's Good/D) only. Next: lift to TestSys (front's DT/GoodT + mask) for MatchG/FracMatch, then Theorem P.
- UPDATE: MergeRunT.lean (coord-951 ebfc369, no sorry, re-checked): merge_runT / merge_countT for general test points
  (GoodT + hT), and TestSys.merges: per σ : TestSys, M ⊆ σ.cnt, |S|-1 <= |M|, merge record, persistence, run_once.
  This is the M that front's MatchG / FracMatch consume.
