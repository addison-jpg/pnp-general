# Dead ends for `no_minCE`: check here before starting a route

One line per refuted or exhausted route, with where it is recorded. Seeded 2026-11-24 by the board
integrator from the board and notes as they stand; the wording is the source's, so read the source
for the exact statement. Add a line whenever a kill test fails. coord and research own this file.

| Route | Status | Witness or reason | Source |
|---|---|---|---|
| Canonical Hall; two-world Hall (= the fixed 1/2-1/2 coin rule) | refuted | canonical Hall: w8 cx1 (n = 9), cx2 (n = 7 sunflower {0,1,4},{0,2,5},{0,3,6}, s = 18: a family's counted union 5 < demand 6), cx3; coin rule: w9/tw/cxtw3c (n = 9, s = 34). CAVEAT: cxtw3c has a Theorem-X zero-set family, so it lies OUTSIDE the MinCE case | `951/board/agents/front-status.md`; front HANDOFF §3 |
| R* (z = z_{S_w}, unit atoms, K = all) | refuted | w8b/cxr ('inner-product' junk design); (the coin rule is row 1; 'cxE' as an R* witness unconfirmed by front) | `front-status.md`; front |
| Π* | refuted | cxP1 to cxP6 | `front-status.md` |
| ★ | refuted | cxstar5 | `front-status.md` |
| Relative sandwich, restricted reading | refuted | cxT4 | `front-status.md` |
| Whole-class S-repay; whole-class lifted charging | refuted | v2whole_cx; cxT2, cxT4 | `front-status.md`; SORRY_DISSECTION §20 |
| Every circuit-independent zero-point distribution tried (uniform, biased, h-adapted) | refuted | cxrb(k), cxU_8_4 (n = 20) | SORRY_DISSECTION §20 |
| Fixed two-point menu `{0, top_w}` | refuted | ADV3 (ESSENTIAL, verified by front and front-612): load 1.2 | `951/research/front612/fable_worlds.md`; BOARD.md 09:40 |
| Plain NoMixedPrice (no mixed zero points for any set) | refuted | 62,256 failures: split sets have no world-0 or world-1 zero point | BOARD.md, 09:20 scaffold |
| Pinned heavy split, first version (B pinned at own z_{S_b}) | refuted | 320 essential circuits, B-B collisions; smallest ess_k4e_clean:248, g10 = x3 ∨ (x0 ∧ x1). (Heavy split v2, B floating over z_v = 1, SURVIVES; menu {e_v, z_{S_b}} suffices; common base e_v alone FAILS on c.jsonl#264; integral star-at-0 FAILS) | `agents/qg-d2-nomixed.md` Round 3 |
| "3rd and later merge gates of different sets of size ≥ 4 are disjoint" | refuted | cxr, gate 14 | BOARD.md, referee B |
| CU alone gives MergePrice | refuted | `cu_counterexample` (Lean) | BOARD.md, 10:15 |
| 0/1 (single-gate) prices suffice for the dual | not valid | the dual objective is concave in the price; layer-cake gap | referee angle 1; `research-concave-dual.md` |
| L-greedy-avoid ('any avoiding choices are pairwise disjoint') | fails without repair | 18,875 circuits; smallest n = 4, s = 9 (gate x2 ∨ (x0 ∧ x3)) | BOARD.md, 10 UTC synthesis |
| Classical hypergraph Hall (Haxell, Aharoni-Haxell) for MergeSDR | conditions fail | research | BOARD.md, 10 UTC synthesis |
| Gate-by-gate elimination with a memoryless potential | fails | increments above 1 | coord, s_fable S4 |
| Per-world bounds (R6); per-cube multi-base K_{2,2}; fixed class lists; weight ≤ k relaxations for EVERY fixed k | refuted | see source; research Fable W: AG(2,25) at k = 2, 12,370 < base 15,600 | `951/board/paper951.md` §2 to §4 |
| Local point rules (p, q, r, a, s, b and later rounds) as the whole proof | stall | regress at the 3rd and later merge gates of sets of size ≥ 4 | `paper951.md` §3 |
| Fourier / influence bounds (few negations) | no gate-count consequence | influence does not see size | pnp-general issue 11 |
| Infinite series, martingales on Cantor space, zeta-type sums | no route | no coherence between input lengths; parity and IP are linear size | pnp-general issue 12 |
| Physics maps (closed timelike curves, low-degree amplitudes, holographic complexity) | no route past the barriers | rows L-lib-061/062, 065/076, 086 | `951/PIPELINE.md` §3 |
| P2 acyclic forcing with labels monotone in GATE INDEX order | refuted | fixh16_clean#20: forcing path {02}-{12}-{23}-{13} through gates 5, 13, 8 | referee (desktop Coord) 10:30, `951/board/agents/coord-desktop-referee-plan.md` |
| Full (non-cone) D counting; full-D ChargeOK; clean-only ChargeOK | refuted | 3 counterexamples | front w7 |
| 'No gate is ever double counted' | refuted | doubles in essential circuits, always x_c ∨ h | front |
| Per-read substitution of N; Wegener-style local top-down AND elimination with the NOT; first-kill-AND injection; variable-fixing induction | refuted / fails | per-read substitution false at base + 5; fan-out < degree | front |
| Gap-G and Two-World at FUNCTION level (choice depending only on (sets, h)) | refuted | K4, h minterms {02,12,03,13,23}; 9/1162 (graph, h) at n = 4 | front |
| Type-B-only test systems; Rado instead of Hall | refuted / no gain | K4, h = Th_2, s = 41, excess 9; B8(1) | front |
| {M_z(w)} as matroid base families (free integrality, K-Rado => MergeFrac) | false | 13/19 named, 135/163 support-B circuits | research-charging §d; front |
| No-mixed with the weak world-1 definition h(z restricted to S) = 0 | fails | 1,043 circuits | `agents/qg-d2-nomixed.md` Round 2 |
| S1(g) for MERGE SETS without (i) + (ii); N-dependence of cross-world gates from clean + live + essential alone | false | CrossWorld.lean cx1/cx2; 155 / 60 circuits, all s - base >= 5; Lean cx3_counterexample | CrossWorld.lean, CrossWorldCex.lean |
| As general laws: 'shared 3rd+ merges never downstream of the NOT', 'no mixed conflicts', 'staircase disjointness' | refuted | ADV4 | `951/research/front612/fable_worlds.md` (b3, C3) |
| Free-candidate lemma; research's no-chain lemma; single-flip repair L-flip | fail | cxT2 / cxT4; 2,454 circuits; 24 fixh16 K4 circuits | scaffold / research, 09:50 |
| Unbounded loose LAugment as an easier target | not easier | equivalent to MergeSDR (Lean mergeSDR_iff_avoid_augmentLoose) | Augment.lean |

## NOT dead ends (open or supported; do not list as refuted)
Heavy-point exclusion is OPEN (no lemma excludes it; 842/842 essential clean circuits at s - base = 4 have a heavy unit); heavy split v2;
refined no-mixed form; StrongCU / ChainPick; MergeSDR (0 failures on 75,619; kernel-checked on 35); L-avoid; L-augment_2 (= LAugmentK 2).
