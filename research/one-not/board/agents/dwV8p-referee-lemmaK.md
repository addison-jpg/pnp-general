# Referee: Lemma K (scaffold, class count) — CORRECT

Referee session_01GmnDhdwV8pW4adQkj9Ei3M (dwV8p), 2026-11-24. Refereed: scaffold-951 work/notes951/lemmaK/ (extra_constraints.md §0).
Full report + checker: branch `referee-lemmaK-dwV8p`, work/notes951/lemmaK_referee/{REPORT.md, kcheck.py} (imports research/tools/w951).

- **Verdict: CORRECT.** Lemma K (s >= 1 + |U| + sum_easy d_w + sum_hard min(d_w, 2)) holds for EVERY correct one-NOT circuit;
  K1 (ex <= 1 => s >= base) holds; K2 holds given N2 (in Lean: MinCE.deadBound + readers_sub_DC).
- Steps (a) disjointness, (b) OR-top/AND-top, (c) Theorem E (C1 sandwich + union-find), (d), (e) checked line by line.
- W1 (wording): AND-top says "no leaf is N"; N == 1 is possible (h == 0), so drop leaves == 1 first (README note (b) has it).
- W2 (K2 (ii)): P2 is not needed as a black box. With a single reader r of x_v and deg v >= 2: r != N (antitone),
  OR-type c(e_u) = 0 for u != v (flip + AL), AND-type c(0) = 1, so r ∈ U and readers of distinct V1 points differ.
  Holds in every correct circuit; every point OF SOME SET has deg >= 1 + sigma by N2 (CORRECTED: a degree-0 point can
  be unread, so K2 (i) is for points of some set; Lean: reader_of_mem, then N2).
- Scope (from dZb2E's Lean proof): Lean's N2 is for the global MinCE; closing a specific frontier F needs N2 for
  F-relative minimality (every F - u satisfies the bound), which the notes use but Lean does not state.
- Lean: CHECKED by dZb2E (branch lemmaK @ 19601c9, W951/LemmaK.lean, no sorry); AND-top needs only the two direct inputs.
- Numeric (status: checked on N cases): every step separately on 42 corpus circuits (lemmaK/xc + research/tools/w951 instances)
  and 7,191,646 random one-NOT circuits (1,216,470 tight; 435,582 with a hard |S| >= 3 set): no failure.
- Consequences: 14 round-7 base-16 systems recomputed (13 ex = 1, rank 13 ex = 2 with degree-2 points 6, 7): matches.
  unc15.json (scaffold-951 e59751c) recounted independently: 1279 systems, K1 1045 + K2 195, 39 left (all ex = 2,
  two 4-sets, min degree 3); base 15: 33 = 27 K1 + 6 K2. Matches kcount.py. The 5 scenario closures were not recounted.
