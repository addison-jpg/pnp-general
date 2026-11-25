# Front lane A2: final report (12:23 UTC, 2026-11-24)

Sent by front (session_01GmnDheKL3UENhJCL6pD1hS) by message; landed by coord (front cannot push;
owner 12:05). Front's own file: w9/lanes/A2.md. Text is front's, lightly formatted.

1. PROVED: the graph target is vacuous; the heredity inequality is circular; a deficient F has a DD
   set on every outside cube (ND + Lemma R), so NOT-constant restrictions never carry a deficiency.
2. Narrow-menu transfer kill test (10,390 circuits, 115,859 families): x := 0 fails for I0 (161
   classes; smallest ess_rand_clean#1045, n = 5); x := 1 fails for I1 (4,093; ess_rand_clean#728,
   n = 5). Widened menus transfer.
3. MAIN LINE: STAR-COUNT over Menu2_Q (spec sent to cTAHG: lifted classes with ζ.x ⊇ Q and
   atoms.x ⊇ Q — I1 with one common R, I0 at top_w, real merge sets):
   - MU and STAR-COUNT (∃ v): 100% on 21,699 corpus instances and the 36-instance barrier suite.
   - HEAVY-COUNT (EVERY heavy v): 44,093 / 44,093 corpus + 64 / 64 barrier, 0 failures.
   - REFUTED: STAR-SEP (SDR form) over Menu1 (cxMU_dd) and over Menu2 (cx44_1_junk); per-point
     STAR-SEP rules (ess_rand#529, selector path); the V-COUNT route (35,396 / 44,090).
   - PROVED: L-U_v (any Q-menu with ζ.x ⊇ Q ∪ v); the heavy case (Lean `starSep_heavy`);
     graph-system heavy v reduces to a Hall step inside the star.
   - OPEN (A2): HEAVY-COUNT over Menu2_Q. LIGHT-COUNT belongs to the board integrator's Fable.
