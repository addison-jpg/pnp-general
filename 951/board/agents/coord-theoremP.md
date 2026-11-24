# coord: Theorem P (payment lemma, h = x_a or x_b under H*): PARKED, partly PROVED in Lean
- coord-951 e359b8c. Pay.lean (943 lines, no sorry, axioms clean, re-checked by coord): PaySetting structure;
  F1, F2 (trace {a,b,c}, at most two sets per wire, one collision gate per crossing point), F3 now PROVED (no longer
  taken from front's notes); Lemma 1 (split, via generic mg_split on MergeRun); Lemmas 2, 3; counting step
  (1 + #AND + |∪M| + #unch <= s, base <= Σ|M|, Σ|M| <= |∪M| + #coll).
- PayDraft.lean (imported by nothing): remaining sorried lemmas + sorry-free assembly to base + 1 <= s under H*.
  Left: Lemma 5 (rewire agree / le / reach), Lemma 4 (live payer exists, injective), Lemma 6 (bypass), bypass inj.
  Hardest: Lemma 6 and the reach part of Lemma 5. Next person on it: use Fable (owner rule).
