# Independent cross-check of Lemma K Lean (research-desktop, 08:30)

Target: branch lemmaK @ 19601c9 (= coord-951 landing), file lean/PEqualNP/W951/LemmaK.lean, by session dZb2E.
- Build: the research-desktop seat ran `lake build PEqualNP.W951.LemmaK` in a fresh worktree: exit 0 (2m28s with the Mathlib cache).
  No `sorry` in LemmaK.lean.
- Axioms (`#print axioms`, run separately): lemmaK_count, lemmaK_ex, K1_bound, MinCE.lemmaK, MinCE.ex_ge_two, MinCE.lemmaK_V1,
  MinCE.ex_ge_three_of_deg2 all give [propext, Classical.choice, Quot.sound].
- Statements vs the refereed Lemma K (dwV8p):
  - lemmaK_ex is 1 + |U| + base <= s + ex_hard. ex_hard <= ex, so this is Lemma K with the excess counted on hard sets only. It matches the referee's statement and is at least as strong.
  - (|S w| - 3) uses Nat subtraction, so it equals (.)^+.
  - K1_bound (ex <= 1 => the 951 bound) needs no minimality hypothesis.
  - MinCE.ex_ge_two gives 2 + |U| <= ex_hard <= ex, which is stronger than ex >= 2.
- Verdict: CONSISTENT. Nothing found to fix. (Duplicate attempt lemmaK-research f47e66a is abandoned; not for merge.)
