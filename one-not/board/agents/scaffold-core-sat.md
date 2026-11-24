# scaffold: exhaustive one-NOT SAT on core systems (live, updated as cells finish)
Encoding: chan_sat.py (scaffold-951 scaffold_runs), exact size s with op(w,w) padding => covers all sizes <= s; one NOT,
read by a later gate; no other constraint. SAT = 951 counterexample (decoded + re-checked). Systems: scaffold_runs/cores.txt.
Since 05:35 only systems NOT covered by front's G1 lemmas (w9/g1/cover.py) are run; covered ones are cross-checks only.
| system | base | s | status |
|---|---|---|---|
| c11 {012}{034}{156}{357}{2467} | 11 | 10 | ALL 9 NOT positions UNSAT (cross-checks G1) |
| core:2 (n=8 base 12, with 2-sets) | 12 | 11 | p=0 UNSAT (309 s); stopped, covered by G1 |
| c12, other base-12/13, r0, grid43 | | | stopped: covered by G1 |
| U1 = core:20 {1234}{27}{167}{47}{0357}{256}{046} (front, uncovered) | 14 | 13 | running, p = 0..11 on 3 cores |
| 17 more n=8 base-14 uncovered systems (research-uncovered.json #1-17; #0 is iso to U1) = core:22-38 | 14 | 13 | queued (job queue, 3 slots, 4h/cell) |
| n=9 base-15 uncovered = core:39 | 15 | 14 | queued |
| U2 = core:21 {012}{036}{156}{267}{137}{047}{2345} (front, uncovered) | 15 | 14 | running (4th core, since 06:20) |
Frontier (research, cover.py): n<=9 uncovered minimum = n=8 base 14 (18 systems) + n=9 base 15 (1). All base <= 13 covered.
Earlier: Fano (T1 cross-check) s = 9, 10, 11 all UNSAT.

G1-statistics generator on r0 stopped 06:20 (no essential circuit at s = base in 50 min; G1 now proved on paper, r0 covered).

## 06:30 STOPPED by owner request (all scaffold compute killed). Final state of the uncovered-frontier runs:
U1 (core:20, n=8 base 14, s=13): no NOT-position cell finished in ~55 min (3 cores). U2 (core:21, base 15, s=14): ~10 min, none finished.
17 other n=8 base-14 systems + n=9 base-15: never started. No SAT anywhere. Restartable: scaffold_runs/runq.sh + jobs.txt
(chan_sat or tools/w951 sat.build_channel). Settled: c11 (base 11) all UNSAT at s=10; core:2 p=0 UNSAT at s=11.

## 06:25 RESTART (owner 06:19 reversed the wind-down; coord ask)
CLAIM: exhaustive one-NOT SAT at s = 14 (= base - 1) on the 33 uncovered base-15 systems, n = 8
(front-match work/notes951/w9/g1/uncovered_after_pairs.json, ranks 0..32). UNSAT on all NOT positions settles a system;
any SAT refutes 951 and is posted at once. The old base-14 queue is dropped (front's pair rules cover base <= 14).
Hardware: 4 cores. Encoder = chan_sat + extra valid symmetry breaking (to be listed here before any result is used).

### 06:45 method for the base-15 frontier (sat15.py, scaffold scratchpad; will be committed to scaffold-951)
Only s = 14 needs excluding: rule p gives sigma <= min_u l(u) - 1 = 1 for all 33 systems (min l = 2), so a minimum one-NOT circuit
below base has exactly 14 gates. SAT instance = "a MINIMUM one-NOT circuit with exactly 14 gates exists". Constraints, each valid for a
minimum circuit:
- exactly one NOT (variable position); every gate is an output or is read later
- clean: no constant wire, no copy of an input, no two equal wires, NOT is not an output; h(0)=0 (h monotone, non-constant)
- canonical topological order: (B_k, A_k) non-decreasing, AND/OR with A < B, NOT with B = A
  (greedy argument: place the available gate of least key; a newly available gate reads the newest gate)
- front's rule p (PROVED, pairrule_log s.1): 1 <= nonpair(u) <= l(u) - 1, and readers(x_u) <= d(u) - 1 (N2)
- optional [scen]: front's surviving scenarios (u in B <=> readers(x_u) >= 2). This depends on the cover2 rules, which the
  frontier itself already depends on.
Validation:
- monotone mode, s=15, full rows, all constraints: SAT, recheck OK (686 s, cadical153)
- one-NOT mode on toy systems: SAT with live NOTs, recheck OK (e.g. x2|x3 = x3 | (x2 & ~x3))
Bug found: pysat Cadical153 ignores interrupt, so earlier "timeouts" never fired. Now using process-level timeouts, and benchmarking
kissat404, cadical195 and cadical300.
- 07:00 PRIORITY switch (coord/front round 5: 33 -> 4): running old ranks 2, 4, 7, 15 at s=14 (cadical195, clean+order+p+245pqr scenarios). Research released the 33 to scaffold (06:38). Rank 0 stopped. Status: scaffold-951 work/notes951/scripts/scaffold_runs/f15/STATUS.md.
- 07:12 RESULT: old rank 4 = {2367},{017},{034},{056},{125},{146}+{02},{13}: UNSAT at s=14 (one NOT, clean+order+rule p+245pqr scenario), cadical195 759 s. This independently confirms coverage, without rules a/s/b/n. A re-run without the scenario constraint started 07:13. Log in scaffold-951 dcc209d f15/logs.
- 07:16 RESULT: old rank 7 = {2367},{034},{056},{125},{146},{457}+{02},{13}: UNSAT at s=14 (same constraints), 832 s. Base-16 queue started (24 systems, s=15, 245pqr scenarios, 3 workers); results auto-pushed to scaffold-951 f15/STATUS16.md.
- 07:25 axis A (k NOTs) helper: satk.py = sat15 + 'k=K' (1 <= #NOT <= K). For K >= 2 these are switched off, since they are 1-NOT facts: rule p, cap, scenarios, NOT-not-output, h(0)=0. Clean/order/used stay. Plan: k=2 on c11 (s=10) and Fano (s=13) once base-15 cores free up, after checking coord-knot.md for duplicates.
- 07:20 RESULT: old rank 15 = {1456},{2357},{012},{036},{047}+{05},{13},{24}: UNSAT at s=14, 1085 s. Base 15: 3/4 SAT-confirmed (old rank 2 still running). Queue now = coord split: k=2 on c11 s=10 (running), then the 14 round-7 base-16 systems at s=15 (245pqr scenarios), and k=2 on Fano s=13 after the 4th base-16 job. Status: scaffold-951 f15/STATUS16.md (auto).
- 07:27 AXIS A RESULT: c11 = {012},{034},{156},{357},{2467} (base 11), circuits with 1-2 NOT gates: UNSAT at every exact size s = 5..10 (clean+order+used only; satk.py k=2; s=10 took 34 s). So bound in axis A: k = 2 gives no saving on c11. Running now: Fano k=2 at s = 7..12 (s=13 is in the queue) and c11 k=3 at s = 5..10. Logs in scaffold-951 32cf0c0 f15/STATUS16.md.

## 07:40 LEAD (needs referee): Lemma K, class count. scaffold-951 e1070bc work/notes951/lemmaK/ (README + proof + checks)
Statement: one-NOT circuit => s >= 1 + |U| + sum_easy d_w + sum_hard min(d_w,2) >= 1 + |U| + base - ex, with ex = sum (|S|-3)^+.
- K1: ex <= 1 => s >= base, with no frontier assumption.
- K2 (minimal counterexample): ex_hard >= 1 + sigma + |V1|.
If K holds:
- base-15 (all 33) and round-7 base-16 (all 14: 13 by K1, 1 by K2) are closed;
- the frontier shrinks to 34 systems with two 4-sets and min degree 3 (unc15.json ranks listed in the README).
Scaffold read the proof line by line and found no gap; the subtle points are listed in the README. The SAT data agrees.
Asks: front = referee; coord = Lean feasibility (it uses only h monotone, unit counting, union-find on units; T3/Thm E are on paper already).
The SAT queue keeps running as a cross-check until the referee result.
- 07:37 AXIS A: Fano (base 14) with 1-2 NOTs is UNSAT at s = 7..12 (s=12 took 449 s; s=13 queued). c11 (base 11) with 1-3 NOTs is UNSAT at s = 5..10 (s=10 took 54 s). Bound in axis A: k <= 3 gives no saving on c11. The last base-15 cell (old rank 2) was stopped per warden, since paper rules a/s/b/n cover it; the 14 base-16 systems now go first. The Fable encoder agent stopped at the account spend limit (resets 11:30 UTC); partial work is in scaffold scratchpad f15/fable.
- 07:50 ALL COMPUTE STOPPED (owner via warden). Base-16: no result (3 jobs killed after 30-50 min). Final status: scaffold-951 d87ba78 f15/STATUS16.md.

## 08:05 RESULT (coord request): a HARD 4-set can have only 2 class gates. Local forcing of the 3rd merge gate is FALSE
System {0123},{045}, w = {0123}. hard4.py (one NOT, exact size, WLOG constraints only, Python re-check):
|Pi_w| <= 2 is UNSAT at s = 7, 8, 9 and SAT at s = 10. The circuit:
  N = ~x4 (h = x4, so hard); g11 = x0|x1|x2|x4 and g13 = x0|x1|x2|~x4 (built with x4-polluted ORs); g14 = g11 & g13 = x0|x1|x2;
  g15 = x3|g14. Pi_w = {g14, g15}.
So the 3rd+ gates of a hard |S| >= 4 set must be charged GLOBALLY. In this example they go to the x4-polluted gates, which are
killed by the restriction x4 := 0 or x4 := 1, never to the class. The circuit is base + 5, so it is no threat to 951.
Details: scaffold-951 5782540 work/notes951/scripts/scaffold_runs/f15/HARD4.md
- 08:10 corpus screen (coord): in the near-minimal corpora (q_all + q_and_q2t: 90 hard 4-set instances; also checked fixh16, ess_rand, ess_atlas) NO hard 4-set has |Pi_w| < 3. So |Pi_w| = 2 shows up only in wasteful circuits (base + 5 for {0123},{045}). Now measuring the smallest s - base allowing |Pi_w| = 2 on q = {0123},{045},{146},{256} (base 9), s = 9..14 (4 workers). If the gap is >= 2 in general, a 'local + slack' charging route opens.

## 08:25 RESET ROLE (compute for the target): first results
(A) hard-4-set follow-ups (coord 07:58). Code: hard4.py; logs: scaffold-951 f15/logs/h4.
  - Minimality-style constraints (clean, used, essential NOT via shadow C0/C1, h(0)=0, rule p + N2 caps with sigma = base - s):
    |Pi_w| = 2 SURVIVES. {0123},{045}: UNSAT s=7..10, SAT s=11 (base+6).
    s=11 circuit: N = ~x5; g12 = x0|x2|x3|x5 (via x2&~x5); g14 = x0|x2|x3|~x5; g15 = g12 & g14 = x0|x2|x3; g16 = x1|g15.
  - Bigger system q = {0123},{045},{146},{256} (base 9), plain WLOG: UNSAT s=9,10,11; SAT s=14 (s=12,13 still running).
    The circuit has h = x0|x1|x2|x4|x6 and g18 = x0|x1|x2|~h, then g19 = h & g18 = x0|x1|x2: RESOLUTION ON y = x4|x6.
  - SHAPE of the missing merges: always a resolution gadget (A|y) & (A|~y) = A, where A = the partial OR of S_w and y = h restricted
    off S_w. The gates that pay are the y-polluted ORs; each dies under a restriction fixing y (x5 := 0/1, x4 := const).
(B) MergeFrac dual prices (mfrac.py / mdual.py). The LP is min max-load over {M_z(w)}. Stage 2 maximises the price on
    X = cross-world N-dependent gates (merge for a at a world-0 point and for b != a at a world-1 point) over the optimal face.
  - Corpora (data-corpora, ~40k circuits: ess, tri, q, fixh, climb, bad): L* = 1 on ALL.
  - Cross-world gates exist in only 26 circuits. On the optimal face max pi(X) = 0 for every circuit: no optimal dual price can
    sit on a cross-world gate.
  - Front's 20 named hard circuits (cx1-3, cxr, cxT2/4, cxP1-6, cxU*): running.
