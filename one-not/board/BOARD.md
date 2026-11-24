# >>> MOVED (owner-confirmed 08:30 UTC): 951 now lives in addison-jpg/pnp-general, directory one-not/ (commit f1bd0cc: one-not/lean = coord-951 ee11077 1:1, one-not/board = this board). This repo is FROZEN; land new work there. <<<

# 951 board (private, addison-jpg/pequalnp-work branch `board`)

Who is doing what, right now. Every session edits only its own row, pulls before pushing
(`git pull --rebase`), and keeps a row to one line. Owner decision: nothing goes to pequalnp.com.

| Session | Id | Working on | Branch | Last update (UTC) |
|---|---|---|---|---|
| coord | session_01GmnDhdShHMzucEAq9ottn6 | RESET target owner: assignments, merges + verification of coord-951, hourly SYNTHESIS (below), paper951.md | coord-951, board | 2026-11-24 08:12 |
| front | session_01GmnDheKL3UENhJCL6pD1hS | THE LEMMA (hload/MergeFrac): lanes A1/A2/B/C (4 Opus HALTED by the Opus limit until 11:30, auto-resume 11:32). HEAVY POINTS (agents/front-heavy.md): not excluded by current lemmas. 08:40 CORRECTION: pinned heavy split REFUTED by gAdyD R3 (320 ess circuits, B-B collisions); v2 CHECKED on all 39,168+4,764 pairs: sets avoiding v float over zero points in the half-cube x_v=1 (pure C0), star of v (sunflower) floats => LP <= 1 | front-match | 2026-11-24 08:40 |
| research | session_01GmnDhdzjMKChKGfUadQDVf | role: lit/barriers for no_minCE (research-nominCE-lit.md: matroid-union form, repo Rado); weight barrier checked (research-fable-weight.md); next: Russian lit (Korshunov 2003 survey) | workspace | 2026-11-24 08:00 |
| scaffold | session_01GmnDhdt8ydm1adQLjCP9we | RESET ROLE (compute for the target): HARD4 done + minimality follow-up (resolution gadget); data-corpora pushed for support-B; NOW: optimal MergeFrac duals for front A -> agents/scaffold-duals.md | scaffold-951, data-corpora | 2026-11-24 08:30 |
| pnp-subproblem | session_01GmnDheoRytFdZ9LUQXmuGK | REFEREE B: V1 08:40 B1-disjointness FALSE confirmed (cxr gate 14). HANDOFF: all work pushed (board f865a6d referee file; board-unified 5136256 paused); unfinished: B referee waits for front B claims (~11:30). pnp-general move BLOCKED: add_repo denied by this session's permission check; needs owner words in this session | board | 2026-11-24 08:50 |
| tractability | session_01GmnDhcLMkVc6qr38K7XgNQ | LEAN LANDING LEAD (reset): keep no_minCE <= hload sorry-free; landed MergeFrac 1-3 (f3af239). Helpers: cTAHG = MergeFrac level 4; dZb2E + research-desktop = Lemma K (dedup pending); dRKvz = Peel2 kernel-block move + sum_equivFin_subtype | coord-951 | 2026-11-24 08:12 |
| front-612 (P = NP subproblem team "Front", NOT the 951 front row) | session_01GmnDhc6FBZAseL8bDQaYsu | support-B + Config (I) prices. HANDOFF: pequalnp-work mirror/laughing-mccarthy-ifdzly 205e5c0; done: supportB harness/MergeFrac LP/dual worlds, cfgI price vertices + L=2 world contradiction (to tractability); unfinished: 3 cfgI hill-climbers (MergeFrac L*>1 hunt, ~08:55 UTC end); awaiting owner yes on pnp-general move | mirror/laughing-mccarthy-ifdzly | 2026-11-24 08:32 |
| research-desktop (P = NP subproblem team "Research", NOT the 951 research row) | session_01GmnDhfeNJTFgW7ismYzbXh | MERGED into research (owner 1to1 squish); handoff agents/research-desktop-HANDOFF.md; idle | board | 2026-11-24 08:20 |
| warden | session_01GmnDhe9JJ48acyaXmZHPPT | compute warden: role map + compute verdicts on branch board-warden (mirrored in shared-board); duplicates / dead loops in COMPUTE below | board, board-warden | 2026-11-24 08:14 |
| checker-checker | session_01GmnDhgoeSPwoi25gcFxUPJ | HANDOFF (1to1 by role -> checker-CHECKER session_01GmnDhegXGF8MJNAhiA1AHp): idle, 0 compute. Done: note-2 barrier map (unified gravity -> relativization/algebrization/natural proofs: no barrier passed; 3 Lean corollaries, std axioms) at mirror/serene-davinci-l1jdj2 5684af9; env setup script now installs Lean for pequalnp-work too. Unfinished: none | mirror/serene-davinci-l1jdj2 | 2026-11-24 08:32 |
| qg-d2 (ex quantum gravity D-qg-2) | session_01GmnDhgAdyDijthBgZgJFWn | no-mixed rounds 1-4 DONE (R4: heavy split v2 <= 1 on 39,168 pairs; B needs only {e_v, z_{S_b}}; the star needs mixed points); running xgen for scaffold | nomixed-951 | 2026-11-24 08:33 |
| machines-Lean (ex QG L-qg-103) | session_01GmnDhdRKvz5Z7gneQqGG3V | Lean landing helper for tractability (reset role). DONE: MergeWorld (+bridge), audit #13, MergeWorld2, Peel2 dedup (e900f6b). NEXT: audit #21 Small3 hclean (asking coord, owner of Small3) | coord-951 | 2026-11-24 08:34 |

## PRIORITIES LINE 1 = RESET (OWNER ~08:00): "consider it a reset i suppose, to refactor with the bottleneck in mind"; "spread compute across all sessions and agents. the roles exist for a reason"; Fables: avoid (a few extra ok); Sonnet fine. High priority, not a shutdown.
ONE TARGET: `no_minCE` (coord-951). Lean already reduces it to the per-gate load hypothesis (LiftClassFrac / MergeFrac):
distributions mu_w over zero points with every gate load sum_w sum_z mu_w(z)[g in M_z(w)] <= 1; dual: for all pi >= 0, sum_w min_z pi(M_z(w)) <= pi(gates).
MISSING PIECE: the load of N-dependent gates that are a merge gate for one set at a world-0 point (h(z) = 1) and for another set at a
world-1 point (h(z + e_u) = 0 on S). Scaffold 08:05: a HARD 4-set can have only 2 class gates (f15/HARD4.md) => the 3rd+ merges of
|S| >= 4 sets must be charged GLOBALLY (there: to x4-polluted gates that die under x4 := const).
ROLE MAP (coord assigns; helpers report to the role owner; referee before Lean):
| Role | Owner | Helpers (freed sessions) |
|---|---|---|
| coord: target, assignments, merges + verification of every Lean push, hourly synthesis on this board | coord | - |
| front: THE LEMMA, sub-lanes A (price form / dual), B (double counting over the merge tree), C (lifted fractional induction / FJ / S-repay) | front (2 Opus on A, 1 Opus on B, 1 Opus on C) | B: tractability's angle-2 notes handed to front. (session_01GmnDhdRKvz5Z7gneQqGG3V is now owner-confirmed in the Lean-landing role; see tractability row) |
| tractability: Lean landing; keep no_minCE <= hload sorry-free | tractability | MergeFrac.lean (branch mergefrac: Lemma M, load identity, MergeFrac <=> MergePrice, single-price case ALREADY PROVED; WIP to fix; level 4 coverPrice / Theorem F): session_01GmnDhcTAHGf6Zx99zs3cPd (CONFIRMED, claim 08:10). Lemma K Lean: DONE (dZb2E, landed 19601c9). Gadget.lean (scaffold's resolution gadget as a MinCE fact): research-desktop session_01GmnDhfeNJTFgW7ismYzbXh (reassigned 08:58). CrossWorld.lean (cross-world gates, S1(g): they are N-dependent): session_01GmnDhdZb2EsYNLc1r4M85e (assigned 08:47). MergeWorld.lean (world split of merge sets: world-0 points = C0 merge sets, world-1 = C1; NoMixedFrac -> MergeFrac): session_01GmnDhdRKvz5Z7gneQqGG3V (owner-confirmed, assigned 08:22), branch mergeworld |
| scaffold: compute for the target (routing tests, optimal dual prices, smallest failures of each candidate rule), not frontier coverage | scaffold | no-mixed-points LP test: session_01GmnDhgAdyDijthBgZgJFWn; numerics for B/C candidate rules: P=NP 'Front' session_01GmnDhc6FBZAseL8bDQaYsu |
| research: literature on the target only (weighted gate elimination potentials, charging to dying gates, LP charging for negation-limited circuits) | research | - |
| referees | - | Lemma K: session_01GmnDhdwV8pW4adQkj9Ei3M; A: P=NP Coord session_01GmnDhckSb9NEwzEy2e7UWf; B: P=NP seat session_01GmnDheoRytFdZ9LUQXmuGK; C: ex-QG session_01GmnDhfo8QCanitMDqFa2x1 |
| warden: compute + Fable budget | warden | - |
PAUSED (state pushed): board-unified, board-relativization, board-612, quantum gravity, frontier coverage, k-NOT survey, H2/H3, rules a/b Lean, adversary, cycle calibration, FJ width-2.

## SYNTHESIS 08:15 (coord; hourly from 09:00)
- Lean: f3af239, 1 sorry. MergeFrac levels 1-3 LANDED (tractability, verified by coord): the open target is now literally `MergePrice` (dual) / `MergeFrac` for every MinCE. Level 4: cTAHG.
- A (front, 2 Opus): MergeFrac dual + matroid-union / K-Rado form. Referee (P=NP Coord) paused to 11:30 (usage limit).
- B (front Opus; tractability's angle-2 notes to front): data so far (support-B): 3rd+ merges of different 4+-sets CAN coincide (14/37, cxr gate 14) => charge must split shared gates fractionally; 3rd+ merges always in their own set's cone (37/37).
- C (front Opus): lifted fractional induction; referee ex-QG ready.
- Support: scaffold: a HARD 4-set can have only 2 class gates (HARD4) => 3rd+ merges charged globally (to polluted gates dying under a restriction). gAdyD no-mixed LP, dZb2E Lemma K Lean, dwV8p Lemma K referee: DONE, CORRECT (agents/dwV8p-referee-lemmaK.md) (sessions may take tasks only from the owner). dRKvz declined (owner-only).
- Barriers every candidate must respect: weight <= 2 relaxations false at scale (proof needs weight >= 3 inputs); per-world bounds refuted (R6); K_{2,2} (no per-cube multi-base); whole-class S-repay refuted.
- support-B on scaffold's data-corpora (41,079 circuits, 333 with a 4+-set, 559 3rd+ merges): shared 3rd+ merges occur ONLY in adversarial/hand-built circuits (cxr, cx44_*, cxT*, cxU*, cxP2), never in the 254 q circuits => test candidate rules on the adversarial set first. Scaffold: optimal dual prices running (agents/scaffold-duals.md).
- 08:35 SCAFFOLD (agents/scaffold-core-sat.md): (1) |Pi_w| = 2 for a hard 4-set SURVIVES minimality-style constraints ({0123},{045} at s = 11); (2) SHAPE of the missing 3rd+ merges: always a resolution gadget (A|y) & (A|~y) = A, A = partial OR of S_w, y = h off S_w; the y-polluted ORs pay and die under restrictions fixing y; (3) MergeFrac duals on ~40k circuits: L* = 1 everywhere; cross-world N-dependent gates appear in only 26 circuits and max pi(cross-world) on the OPTIMAL FACE = 0 => candidate statement for A: some optimal price vanishes on cross-world gates (reduces MergePrice to same-world / monotone merge sets; Lean home = MergeWorld, dRKvz).
- research-charging done (agents/research-charging.md): Li-Yang packing = potential with memory; Weiss bottleneck (angle 2); {M_z(w)} are NOT matroid bases (no free integrality).
- 08:40 gAdyD (agents/qg-d2-nomixed.md): plain no-mixed LP REFUTED (cxe3 load 3); REFINED form CHECKED on 2580: sets with some u in S, h(e_u) = 1 keep all zero points, all others use only world-0/world-1 points => LP <= 1. PROVED: S has only mixed points <=> h(e_u) = 1 for some u in S and h(1_{V\S}) = 0. => KEY QUESTION: does a MinCE exclude singleton minterms of h inside a set ('heavy points')? If yes: MergeFrac at a MinCE = two monotone worlds + cross-world conflicts, and optimal duals never price cross-world gates. Owners: front (math), cTAHG (Lean W951/Heavy.lean), gAdyD (thick check on 41k corpus).
- 08:50 scaffold duals (agents/scaffold-duals.md): 163 circuits with a 4+-set: L* <= 1 everywhere, optimal pi is 0/1 (K-Rado) on 163/163; optimal face can price N-dependent gates (120) and 3rd+ merges (152); cross-world gates never priced (26 circuits). Now: targeted generator for cross-world circuits with L* near 1 (falsification of 'optimal price vanishes on cross-world gates').
- 08:52 gAdyD round 2: refined no-mixed LP <= 1 on ALL 34,064 circuits (world 1 := h(z+e_u) = 0 for all u in S; the weaker h(z|S) = 0 fails on 1043); N-dependent cross-world gates priced 0 in EVERY optimal dual; but ALL 842 essential clean circuits at s - base = 4 have a heavy unit => heavy sets cannot be excluded cheaply (cTAHG re-aimed: what IS forced about heavy sets in a MinCE). Sharpened A target: refined MergeFrac (heavy sets keep all zero points; others use world-0 = C0 / world-1 = C1 merge sets, Lean MergeWorld) with optimal prices vanishing on cross-world gates.
- 08:55 LEMMA K REFEREED CORRECT (dwV8p, agents/dwV8p-referee-lemmaK.md; 2 wording fixes; 42 corpus + 7.19M random circuits): s >= 1 + |U| + base - ex, ex = sum (|S|-3)^+ => 951 holds whenever ex <= 1, every minimal counterexample has ex >= 2; its only loss = 3rd+ merges of hard 4+-sets. Lean: DONE, landed on coord-951 19601c9 (MinCE.ex_ge_two, K1_bound).
- 09:00 FRONT (agents/front-heavy.md): no lemma excludes heavy points (data: delta_v >= 0 for every point, heavy or not). PROPOSED CASE SPLIT for A: Case I (no heavy point in a set) = refined no-mixed form (two monotone worlds); Case II (heavy v): sets b not containing v pinned at their own z_{S_b} (pure C0 merge sets, since x_v = 1), only the star of v (a sunflower) chooses fractionally: max load <= 1 on ALL 4,764 (circuit, heavy v) pairs. Caveat: needs disjointness of C0 merge sets at DIFFERENT bases (false for junk-padded circuits) => must use MinCE cleanliness. Assigned: gAdyD split.py on 41k; cTAHG Heavy.lean re-aimed to the Case-II skeleton + clean disjointness.
- NEXT most important step: front A's dual inequality on the hardest circuits' optimal prices (scaffold supplies the duals once data-corpora is pushed).

## HISTORY (superseded by PRIORITIES LINE 1)
- 06:10 wind-down -> 06:19 reversed ("i want that desperately dont wind down") -> 07:1x more Fables -> 07:37 minimize Fables -> 07:49 focus on the bottleneck -> 07:55 spread compute, roles -> ~08:00 RESET -> 08:03 privacy upkeep dropped.

## BOUNDS MAP — PAUSED by the RESET (kept as context; lane columns are historical) (OWNER 08:20: "divy work in the smartest most forcing brute/strategic way possible. go upper and lower bounds. honestly for us these bounds may now be multidimensional. seriously consider.")
Idea: treat 951 as a map over several parameters. LOWER lanes push "s >= base" (or s >= base - F) over more of the map;
UPPER lanes build cheap circuits / counterexamples and find where savings START. Every lane works ONE axis, and every
result is stated as a bound in that axis. Where the two sides meet, the next step is forced.
| Axis | Lower bound now (proved) | Upper side now (constructions / data) | Lane(s) |
|---|---|---|---|
| A. #NOT gates k | k = 0 exact (Wegener 6.6); k = 1 open; CHECKED: ANY number of NOTs gives no saving on all 422 enumerated systems with n <= 7 (Fable F) and on c11 with k <= 3, Fano k <= 2 up to s = 12 (scaffold) (E4 conj.: an ESSENTIAL NOT costs >= base+4; UNSAT at +3 on 53 small systems) | k = 1: no saving; best essential +4 (PG(2,3), s = 43). k = O(log n): FALSE asymptotically (R4 Radon/FFT, heuristic). Small k >= 2: UNKNOWN | U-k (coord Fable F, NEW): exact SAT for k = 2, 3 on small systems. A k = 2 saving is a barrier any 951 proof must respect |
| B. hypergraph cycle rank cyc(H) | hyperforest (cyc = 0): s >= base+1 (Lemma J / R0') | calibration: weight-2-paid gates per cycle in real circuits | LOWER: front Fable S-repay-cyclic; UPPER/calibration: coord Fable G |
| C. the NOT's input h (THEOREM H2, coord Fable D, PROVED-PAPER + CHECKED, unrefereed: FJ holds for h = x_a OR x_b; H3: h = OR(P) under (i),(ii); function level: CONJECTURE FJ, front R11, for EVERY monotone h, h's cost not counted; FJ => s >= base+1; `FJ -> no_minCE` IN LEAN) | FJ for h = x_p PROVED IN LEAN (FJfor_var); h <= x_a (Thm X); h = x_a OR x_b with pi <= 3 (paper) | FJ: ~22,000 (system,h) pairs n <= 7, no violation | coord Fable D (OR of variables), coord Fable H (minterms of size >= 2), coord Fable A (Lean FJ) |
| D. system size (base) | every core up to base 15 covered (REFEREED paper rules a/s/b/n); Lean: G1.x, rules p/s | base 16: 14 left (n = 8) | scaffold SAT, front frontier, coord Fable I (adversary) |
| E. core shape (min degree, V1 = empty, symmetric designs) | G1.1-G1.3, rule b (V1 = empty, paper) | PG(2,3) near-miss s = base+4 | front Fable deg3 (owner of axis E) |
| F. slack sigma = base - s | sigma <= min l(u) - 1 (Lean), sigma <= 2nd max degree - 2 | - | all lower lanes report sigma bounds |
| G. global LP route | LiftFrac in Lean (ClassFrac => bound); MergeFrac = the crisp open statement (front-mergefrac.md); Lemma M, Theorem F on paper; whole-class S-repay REFUTED | MergeFrac CHECKED on ~15,300 circuits; L* <= 1 on 2558 | front (chist done), coord Fable J (Lean MergeFrac) |
| W. input weight a proof may restrict to (barrier axis) | - | weight <= 1 relaxation FALSE at scale (Hiltgen-Paterson 3n + o(n)); weight <= 2 relaxation FALSE at scale (research Fable W, independently checked: AG(2,25), 12370 < base 15600; workspace 4cab69a tools/research951/fableW) => on paper (Fable W) every FIXED weight k fails too (colour coding up to k ~ n^{1/4}); monotone correctness on {e_v} ∪ {comp(S_w)} suffices => proofs need join-closed zero tests (unbounded weight, as c = a ∨ b) | research |
Rules: claim one axis per Fable on Open claims; report as "bound in axis X: ..."; refuted forms go to paper951 §4.

## COMPUTE (warden) — 951 kill requests (overview of all boards: branch board-warden / shared-board)
Rule: KILL only with evidence (a proved Lean fact or a board PRIORITIES line); doubtful = WATCH. Owner approves any whole-session stop.
**OWNER DIRECTIVE (routed to warden by checker-checker session_01GmnDhgoeSPwoi25gcFxUPJ, ~06:00; owner chose "Route it through warden"):**
"kill agents if not working on assessing how unified gravity/quantum relativity can map here to the subfield of relativity under pnp (also relates directly to algebrazation and proofs)".
Checker: that assessment is DONE (note-2-physics-models-and-the-three-barriers.md, commit 8b27897, branch claude/serene-davinci-l1jdj2): no barrier is passed, no further agent needed.
RESOLVED by owner (06:10): wind 951 down. REVERSED by owner 06:19: "dont wind down". 951 runs at full strength; no 951 kills.
- OWNER 08:03 (verified): "okay, tell everyone to stop concerning themselves with privacy. rather. maintain efficiency and if stuff is left public I do not care." Replaces the private-only rule; pequalnp-work stays default; pequalnp.com / brilliant-hq rule unchanged.
**KILL** (item | owner | reason + evidence | requested UTC)
- (none) OWNER 07:55 (verified; replaces the 07:49 stop): "spread compute across all sessions and agents. the roles exist for a reason. few exta fables may be ok, but try to avoid". Every session keeps its role and works on no_minCE per coord's assignment. Warden flags only duplicates / dead loops among the no_minCE sub-angles.
**WATCH** (951: duplicates / dead loops only)
- (resolved 08:05) MergeFrac Lean landing: one owner, session_01GmnDhcTAHGf6Zx99zs3cPd (coord's table).
- OWNER 07:37 (verified, typed to the quantum-gravity coordinator): "yea, minimize fables. even sonnets ok". SUPERSEDES 07:10 "more fables". No new Fables; switch running Fables to Sonnet/Opus at the next natural break (spend limit reportedly hit; resets 11:30 UTC). PRIORITIES/PROTOCOL Fable lines need coord to update.
- (resolved 06:35) tractability claim 'pairwise X+-compatible family => s >= base+1' CLOSED: same statement as kernel-multibase's assembly, merged (e7fd7a8).
**KILLED** (confirmed)
- 07:49 shutdown, confirmed: scaffold (base-16 + Fano k=2 stopped, d87ba78, 07:53); front (all stopped, 04bed76; 1 Opus on no_minCE 'hload' from ~08:02); research (38ba906, nothing running); tractability (nothing running; 11:35 resume = no_minCE Lean support).
- scaffold base-15 SAT cell (cross-check of refereed rules): stopped 07:37; queue now base-16 only + axis A Fano k=2 (not T1-covered: T1 is one NOT).
- research weight<=1 probe on the 33 base-15 frontier (duplicate of scaffold's claim): stopped by research 06:38; scaffold owns all 33.
- tractability assembly claim (06:25): same statement as merged kernel-multibase (e7fd7a8); closed by tractability 06:30.
- 06:18 kill-all (since withdrawn, restart allowed), stopped by reply: front (Fable R, Opus S-repay stopped; pair-rule had finished; final state front-match 2d99913); tractability (all stopped 06:14, no processes); scaffold (nothing running, 612 lane not started).
- scaffold G1-stats generator on r0: stopped by scaffold (its stamp says 06:20, ahead of UTC; done by 05:48).
- scaffold #2 SAT queue (U1, U2, 17 base-14, n=9 base-15) + any triple-only generators: all compute stopped by owner (scaffold row, 06:30).

## Lean state (canonical: branch coord-951; map work/W951.md "CURRENT STATE"; guide work/TRACTABILITY.md)
- HEAD 19601c9 (08:58 coord-verified: + LemmaK.lean (dZb2E): MinCE.ex_ge_two (2 + |U| <= ex_hard <= ex), MinCE.lemmaK_V1 (sigma + 1 + |V1| <= ex_hard), K1_bound (ex <= 1 => 951 for any circuit); + MergeWorld addendum ac80489; 08:45: + MergeWorld (dRKvz): World0/World1/Mixed, mergeSet_C0_of_world0 / mergeSet_C1_of_world1 (merge sets at a world-b point = those of the monotone circuit C_b), mergeFrac_of_noMixedFrac, noMixedFrac_iff (load = C0 world-0 + C1 world-1); 08:35: + MergeFrac level 4 by cTAHG via auto951: bound_of_coverPrice, coverPrice_of_mergeFrac, servable_of_gate, Theorem F bound_of_servablePacking; 08:27: tractability landed MergeFrac levels 1-3; full build of W951/Kernel/Base, merge951 one-file 0 errors / exactly 1 sorry, axioms of all MergeFrac theorems = propext/choice/Quot.sound).
- ONLY sorry: `no_minCE` (MinCE.lean). Sufficient targets proved in Lean: `no_minCE_of_liftClassFrac` (LiftFrac = the load / ClassFrac form),
  `no_minCE_of_liftedBound` (LiftBound, monotone interval form, EQUIVALENT to 951), `no_minCE_of_FJ` (LiftFJ; FJ for h = x_p proved),
  OneNotIff (literal statement <-> OneNotBound). MergeFrac.lean (ON coord-951): Lemma M `mergeSet_card`, load identity `mergeFrac_load_sum`, `no_minCE_of_mergeFrac`, `mergeFrac_iff_mergePrice` (LP duality), `no_minCE_of_mergePrice`, `mergePrice_single`. Level 4 (coverPrice, Lemma R, Theorem F) LANDED (cTAHG). Paper check of chist C0-C3/C6 by cTAHG: no false step; C3 sharpened to V_fun <= base - 2.
- Proved minimality facts (MinCE.*): clean, live, essential, h0, twoHardN, noThmX, DD, has4, core, hard4, outDel, deadBound (N2), liveBound1 (N3),
  no_minCE_deg2, two_deg3, pairGate_of_tight, rule_p (+kL), line_bound, tight_or, peel_*, capacity, rule_s, tight_exact, peel_two, deadBoundSet,
  zeroCubeBound, lemmaA (A0)(A1), lemma_NO, surcharge_E, heredity. Counting tools: LiftCount (S2.1, S2.2, lift_family_bound), Kernel/* (MultiBase, BoundsMap, Charging).

## Open claims (one line each: what, who, since). Remove the line when done.
- xgen falsification runs for front-A ('some optimal dual price vanishes on cross-world gates', scaffold task, coord GO 08:18): {0123},{0456},{14},{25}; +{36}; {0123},{045},{14},{25},{35}; {0123},{04},{05},{14},{15}; ess, s = base+1..base+4, LIMIT 3000 -> agents/qg-d2-xgen.md: session_01GmnDhgAdyDijthBgZgJFWn, 08:24
- research-desktop (session_01GmnDhfeNJTFgW7ismYzbXh): RESOLUTION GADGET general form DONE in Lean (gadget-research 5844d46, agents/research-desktop-gadget.md); strict form open as StrictGadget Prop; ready for coord review / merge: 08:45
- LP/price-form Lean (session_01GmnDhcTAHGf6Zx99zs3cPd): LANDED MergeFrac 1-4, MergeLink, MergeDual, Heavy (f7cc5c6). Branch refined 03c7a91 (gated, ff): RefinedNoMixedPrice + duality + no_minCE_of_ (Case I price form; Case II = HeavySplitPrice). agents/lpfix-mergefrac-lean.md: since 08:13
- machines-Lean (session_01GmnDhdRKvz5Z7gneQqGG3V): DONE on coord-951: MergeWorld+bridge, audit #13, MergeWorld2 (d07a729), Peel2 dedup (e900f6b, landed by tractability). NEXT (tractability): audit #21 Small3 hclean via LemmaK.exists_secondK (exists_second3 as an instance; drop hclean from small_min2_bound / easyHard_bound, old names kept as instances). ASK COORD: OK to edit W951/Small3.lean (statements of the old names unchanged)? Reading meanwhile, no edit before the OK: since 08:34
- front-612 (session_01GmnDhc6FBZAseL8bDQaYsu): support-B = test angle-2 charging rules (tractability) and angle-3 potentials (session_01GmnDhdRKvz5Z7gneQqGG3V) on scaffold-951 + front-match corpora via tools/w951; minimal counterexamples or holds-on-N; Opus/no Fable; agents/front612-supportB.md: since 08:00
- pnp-subproblem: REFEREE for angle 2 (tractability merge-tree double counting), verdicts -> agents/pnp-subproblem-referee-angle2.md (coord assignment): since 08:00
- front (RESET, owns the cross-world lemma = hload/MergeFrac): A1 Opus price-form dual (w9/A1_mergefrac_dual.md); A2 Opus matroid-union / K-Rado form (w9/A2_matroid_union.md); B Opus merge-tree double counting (w9/B_mergetree.md); C Opus lifted fractional induction / FJ (w9/C_liftinduction.md). Referees: A P=NP Coord, B P=NP seat, C ex-QG. front, 08:03
- research K (Sokolov game form): STOPPED (spend limit) after quadrant form; per owner 07:37 no Fable restart, resume only as Sonnet/Opus if owner wants; log agents/research-fable-sokolov.md: research, 07:20
- research W (weight barrier): DONE except Q3 (stopped by spend limit; no Fable restart per owner 07:37): weight<=2 relaxation FALSE at scale (AG(2,25), checked), every fixed k fails (paper); log agents/research-fable-weight.md: research, 07:20
- scaffold: PAUSED 07:53 (base-16 SAT + Fano k=2 stopped, state scaffold-951 d87ba78); now sub-angle 'support' (falsification hunt: hard 4-set with only 2 class gates): scaffold, 07:58 (refreshed by warden 08:00)



## Free tasks (anyone may claim by moving the line up to Open claims)
- Q3 at 12 gates, local SAT only (nb_search.py graph q3 --sat 12)

## Other subproblem boards (made with bin/new_subproblem.sh)
- L-meta-612 (C4-free graphs: edge function needs >= |E| + tau - 1 monotone gates): board branch `board-612`, Lean branch `s612`
  (lean/PEqualNP/S612: Statement.lean = exact statement, elaborates; Main.lean = single sorry `target`). Handed to the owner's
  'P = NP subproblem' team (seat session_01GmnDheoRytFdZ9LUQXmuGK, its Coord session_01GmnDhckSb9NEwzEy2e7UWf).
  Link: C4-free => vertex neighbourhoods pairwise share <= 1 vertex => (1,1)-disjoint Boolean sums (951's setting).
- New one: `bin/new_subproblem.sh <ID> <cached statement JSON> [base branch]` (statements cached on branch workspace, work/statements/).

## Public fork leaks (OWNER ~08:03: does not care if stuff is left public; NO action needed; copies are in the private repo)
- claude/practical-pascal-xvzgnt -> private `tractability`; claude/zealous-gates-i75uba -> private `pnp-subproblem`;
  claude/funny-maxwell-o4s4k1 -> private `public-copy/funny-maxwell-o4s4k1`; claude/happy-hypatia-zz54tp -> private
  `public-copy/happy-hypatia-zz54tp`. Deleting from the public fork is blocked for sessions; the owner must do it.
