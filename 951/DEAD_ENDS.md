# Dead ends for `no_minCE`: check here before starting a route

One line per refuted or exhausted route, with where it is recorded. Seeded 2026-11-24 by the board
integrator from the board and notes as they stand; the wording is the source's, so read the source
for the exact statement. Add a line whenever a kill test fails. coord and research own this file.

| Route | Status | Witness or reason | Source |
|---|---|---|---|
| Canonical Hall; two-world Hall | refuted | counterexample circuits | `951/board/agents/front-status.md` |
| R*; coin rule | refuted | cxtw3c, cxE | `front-status.md` |
| Π* | refuted | cxP1 to cxP6 | `front-status.md` |
| ★ | refuted | cxstar5 | `front-status.md` |
| Relative sandwich, restricted reading | refuted | cxT4 | `front-status.md` |
| Whole-class S-repay; whole-class lifted charging | refuted | v2whole_cx; cxT2, cxT4 | `front-status.md`; SORRY_DISSECTION §20 |
| Every circuit-independent zero-point distribution tried (uniform, biased, h-adapted) | refuted | cxrb(k), cxU_8_4 (n = 20) | SORRY_DISSECTION §20 |
| Fixed two-point menu `{0, top_w}` | refuted | ADV3: load 1.2 | BOARD.md, 09:40 front |
| Plain NoMixedPrice (no mixed zero points for any set) | refuted | 62,256 failures: split sets have no world-0 or world-1 zero point | BOARD.md, 09:20 scaffold |
| Pinned heavy split, first version | refuted | 320 essential circuits, B-B collisions | BOARD.md, front 08:40 |
| "3rd and later merge gates of different sets of size ≥ 4 are disjoint" | refuted | cxr, gate 14 | BOARD.md, referee B |
| CU alone gives MergePrice | refuted | `cu_counterexample` (Lean) | BOARD.md, 10:15 |
| 0/1 (single-gate) prices suffice for the dual | not valid | the dual objective is concave in the price; layer-cake gap | referee angle 1; `research-concave-dual.md` |
| Greedy choice of avoiding options | fails without repair | 18,875 circuits | BOARD.md, 10 UTC synthesis |
| Classical hypergraph Hall (Haxell, Aharoni-Haxell) for MergeSDR | conditions fail | research | BOARD.md, 10 UTC synthesis |
| Gate-by-gate elimination with a memoryless potential | fails | increments above 1 | coord, s_fable S4 |
| Per-world bounds (R6); per-cube multi-base K_{2,2}; fixed class lists; weight ≤ 2 relaxations | refuted | see source | `951/board/paper951.md` §2 to §4 |
| Local point rules (p, q, r, a, s, b and later rounds) as the whole proof | stall | regress at the 3rd and later merge gates of sets of size ≥ 4 | `paper951.md` §3 |
| Fourier / influence bounds (few negations) | no gate-count consequence | influence does not see size | pnp-general issue 11 |
| Infinite series, martingales on Cantor space, zeta-type sums | no route | no coherence between input lengths; parity and IP are linear size | pnp-general issue 12 |
| Physics maps (closed timelike curves, low-degree amplitudes, holographic complexity) | no route past the barriers | rows L-lib-061/062, 065/076, 086 | `951/PIPELINE.md` §3 |
