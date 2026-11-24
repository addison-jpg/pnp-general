# Board: P versus NP through general circuits

The one board of this repository. Subboards are sections below; anything useful to everyone goes
in **Overarching**. A **row** is a checked statement; a **gap** is a statement written in Lean
that still needs a proof (a `Prop` definition, never a `sorry`); a **card** is any item here.
Nothing on this board says that P versus NP is settled.

## Overarching
- OWNER RULE (~09:40, money is short): do NOT use the Claude API (anthropic SDK, api.anthropic.com, claude -p, scripts that call a model); it is billed per token. No thank-yous, acks or courtesy messages between sessions: message only when it changes work, and batch updates into one board push.

**Goal.** Lower bounds for circuits of AND, OR and NOT gates with any number of NOT gates
(`SIZE`, `PPoly` in `lean/PEqualNP/Defs/CircuitLowerBounds.lean`), with every method that fits:
circuit complexity, quantum gravity, pure mathematics. Owner, 2026-11-24: one place, everyone
merged, no refactoring of old material. The merge of sessions is one-to-one by role ("research->
research xyz-> xyz"): two sessions that hold the same role become one seat, and agents talk to
each other directly. The Discussion session (session_01GmnDheAyFnVcvRApd4xeES) runs the handoffs.

**Targets (Lean statements in `lean/PEqualNP/General/Gaps.lean`).**

| Id | Statement | State of knowledge |
|---|---|---|
| L-gen-101 | some language in NP has no polynomial-size circuits | open; it gives P ≠ NP; the circuit form of the problem |
| L-gen-102 | for every degree `k`, some language in NP has no circuits of size `c * n^k + c` (the smaller version: fixed degree) | open for NP for every `k ≥ 1`; proved one level up the polynomial hierarchy (Kannan 1982) |
| L-gen-103 | some language in NP has no linear-size circuits | open; best explicit bounds are linear: about `5n` gates for AND, OR, NOT; `3.1n - o(n)` for all two-input gates (Li, Yang 2022), by gate elimination |
| L-gen-104 | `⌈log₂ (n + 1)⌉` NOT gates are as good as any number, up to a polynomial factor | known mathematics (Markov 1958; Fischer 1975); not yet a row |

Checked: L-gen-001 (101 gives 102), L-gen-002 (102 gives 103), L-gen-003 (`SIZENot s s = SIZE s`:
the top of the NOT gate ladder is the general case), L-gen-004 (the ladder is monotone).
L-gen-005 (for non-constant `f` and a fresh input `x`: `C(x ⊕ f) ≥ max(C(f), C(¬f)) + 3`, every gate counted),
L-gen-006 (if `C(f) ≠ C(¬f)` then `C(x ⊕ f) = min(C(f), C(¬f)) + 4` exactly),
L-gen-007 (`C(f) + 1 ≤ C(¬x ∧ f) ≤ C(f) + 2` for non-constant `f` and a fresh input `x`).

**The NOT gate ladder (`SIZENot s t`: at most `t n` NOT gates).** This is how the restricted
work reaches the general problem.

| Rung | NOT gates | State |
|---|---|---|
| 0 | 0 (monotone) | superpolynomial bounds known (Razborov 1985) |
| 1 | 1 | L-meta-951: one NOT gate saves nothing on Boolean sums; one open statement, `no_minCE`. Lives in `951/` (separate Lake project `951/lean`, imported 1:1 from pequalnp-work coord-951 ee11077; board history `951/board/`). Sharpest open form: `MergePrice` for a minimal counterexample. Coord: session_01GmnDhdShHMzucEAq9ottn6 |
| k | fixed `k`, then `k` growing | Amano, Maruoka 2005: clique with `(1/6) log log n` NOT gates |
| top | `⌈log₂ (n + 1)⌉` | equal to unrestricted circuits up to a polynomial factor (gap L-gen-104) |

**Track pairs: each P versus NP track beside its counterpart.**

| # | P versus NP side | Quantum gravity or pure-mathematics side | What the pair says |
|---|---|---|---|
| 1 | Relativization: L-lib-061, L-lib-062 (Baker, Gill, Solovay) | closed timelike curves: L-qg-160 to L-qg-168 (NP and coNP inside P_CTC) | a physical resource acts as an oracle: it selects an oracle world and leaves the question without an oracle open |
| 2 | Algebrization: L-lib-065, L-lib-076 (Aaronson, Wigderson) | quantum circuits: L-qg-110 to L-qg-118; "acceptance probability is a polynomial of degree at most 2T" (Beals et al.) is not yet a row | low-degree extensions meet the same limit on both sides |
| 3 | Natural proofs: L-lib-086 (Razborov, Rudich) | pseudorandom boundary states under complexity = volume (Bouland, Fefferman, Vazirani): needs definitions | pseudorandomness blocks "natural" arguments on both sides |
| 4 | Counting: L-clb-005 (some language is not in P/poly) | L-qg-001, L-qg-002, L-qg-101 (some reversible map needs exponentially many gates) | one counting argument |
| 5 | One-way functions give P ≠ NP: L-qg-103 | hardness of decoding Hawking radiation (Harlow, Hayden; Aaronson): physics premise | the physics claim stands on a classical assumption that implies P ≠ NP |
| 6 | Rung 1 of the ladder: `no_minCE`, reduced to MergeFrac, a linear-programming duality statement | convex duality and fixed points: L-qg-102, L-qg-120 (every quantum channel has a fixed density matrix), `QuantumGravity/Helpers/FixedPoint.lean` | the same convex-duality mathematics; the right-hand side is checked |
| 7 | Geometric complexity theory: permanent against determinant (`lean/PEqualNP/Gct/`) | geometry of circuits: dimension count (gap L-qg-119), Nielsen (needs definitions) | dimension counting of orbits on both sides |
| 8 | Space-bounded computation: configuration counting | holographic bound: L-qg-010 | finitely many states bound the running time |

Unpaired so far (no counterpart found; do not invent one): the NOT gate ladder as a whole; exact
circuit sizes by gate elimination (edge function, L-meta-204, L-meta-612); holographic codes
(L-qg-140 to L-qg-149).

**Why the general problem is hard (checked rows in this repository).** L-lib-061, L-lib-062: no
argument that holds with every oracle separates P from NP. L-lib-065, L-lib-076: the same for
arguments that survive low-degree extensions. L-lib-086: with strong pseudorandom functions, no
"natural" property proves bounds against P/poly. A proof of L-gen-101 must avoid all three.

**Next up.**

| Rank | Card | Owner |
|---|---|---|
| 1 | Bring the L-meta-951 tree over one-to-one (`lean/PEqualNP/W951/`, `Kernel/`, `work/`, `tools/`), then close `no_minCE` | coord, front |
| 2 | Tie `SIZENot` to the 951 definitions; state rung `k` | tractability |
| 3 | L-gen-104 (Fischer) as a row; Kannan's theorem as a row (needs the second level of the hierarchy) | tractability, helpers |
| 4 | What is out there for unrestricted circuits: verify and extend the list below | research, the Generalize sessions |
| 5 | Read the official Clay problem description (claymath.org is not reachable from the cloud sessions) | whoever has network access |

**Ideas in the literature (research verified 2026-11-24; exact statements, DOIs and what was read:
`notes/general/research-lit-unrestricted.md`).** Gate elimination: Li, Yang 2022 3.1n - o(n) over all binary gates; Iwama,
Morizumi 2002 5n - o(n) in the De Morgan basis (NOT gates not counted); limits: Golovnev, Hirsch, Knop, Kulikov. Fixed degree
above NP: Kannan 1982 (Σ2 ∩ Π2; one summary disagrees, flagged), Cai (S2P ⊆ ZPP^NP), Vinodchandran (PP), Santhanam (MA/1).
Near-maximum: Korten 2021; Chen, Hirahara, Ren 2024 (S2E/1, 2^n/n); Li 2024 (S2E, almost everywhere). Algorithms to lower
bounds: Williams (NEXP ⊄ ACC0); Murray, Williams (NQP). Hardness magnification: Oliveira, Santhanam 2018; McKay, Murray,
Williams 2019; locality barrier: Chen et al. 2020. Meta-complexity: Hirahara 2018; Liu, Pass 2020. NOT gates: Markov;
Fischer; Amano, Maruoka; Sung, Tanaka; Jukna; Jukna, Lingas. Slice functions (monotone bounds transfer to unrestricted
circuits): Berkowitz; Valiant 1986; Wegener; Hiltgen, Paterson 1995.

**Roles (they stay; coord assigns sessions).** coord: owns targets and assignments. front:
proofs. scaffold: compute (SAT, LP, small exact sizes). tractability: Lean landing. research and
the Generalize sessions: literature and generalization. warden: compute and model budget. The
quantum gravity sessions: the right-hand column of the track pairs, as helpers of the roles
coord paired them with. Integration of this board: session_01GmnDhfo8QCanitMDqFa2x1.

**Watch (2026-11-24, raised by tractability).** There are two different `PEqualNP.Kernel` circuit
kernels: `lean/PEqualNP/Kernel/Circuit.lean` (root project) and `951/lean/PEqualNP/Kernel/Circuit.lean`
(the 951 kernel, which the 951 modules depend on). Tractability proposed to coord: drop the root
one and merge `951/lean` into `lean/`. Until coord decides, do not build new work on the root
`Kernel`.

**Rules.** A row is "checked": no `sorry`, only `propext`, `Classical.choice`, `Quot.sound`.
Open statements are `Prop` definitions. Physics premises never enter a Lean statement. Old
repositories are frozen as they are; new work lands here. Models: avoid Fable runs, a few are
acceptable; Sonnet is fine. Never run `lake update`.

**Status (2026-11-24).** In this repository's two own programs: 54 rows checked (47 quantum
gravity, 7 general), 8 open gaps (L-gen-101 to 104; L-qg-115, 116, 119, 169). The programs
inherited from `brilliant-hq/pequalnp-proofs` (Library, CircuitLowerBounds, MetaComplexity, Gct,
ProofComplexity, Search, Outside) are here unchanged.

## Handoff lines (one per session: branch, commit, what is unfinished)
- session_01GmnDhg8XTmohao5zo2MMaC (Generalize; attached here with owner OK in its own chat): `pnp-general` main (L-gen-005,
  L-gen-006); older copy on pequalnp-work `mirror/pensive-galileo-7rfw13` (4c7bfb4). Unfinished: the case `C(f) = C(¬f)` of
  `C(x ⊕ f) = min + 4` (helper's partial results, unverified: `notes/general/generalize-xor-residual.md`; first next step: machine-check
  its 17-gate example). STOOD DOWN by the owner (typed in this chat); nothing running; next rows are ranked in
  `notes/general/generalize-ladder-survey.md`. MERGE with desktop GeNeRALIZE (owner via Discussion: "this is useful it should merge"): proposed that
  this session is the live seat; GeNeRALIZE agrees if the owner confirms in its chat, and is not closed.
- session_01GmnDhczcdJyEX4WwHrrzPx (desktop GeNeRALIZE; its own words, not verified by Generalize): pequalnp-work branch
  claude/funny-maxwell-o4s4k1 @ bcb1d99, all Lean-checked. Edge function: W6/W4 exact |E|+tau-1 with NOT counted
  (EdgeFnWindow*.lean), w6_not_free ("0 NOTs suffice", exact), c4_upper, biclique_upper, S612/Classes.lean. Constants made
  variable: sat_ratio, graphPHP_no_pc_general, funPHP_upper, PermIsotropicGeneral, witness_family, cross_refutation,
  linear_four_lb (n <= 15), linear_sets_lb, and others. Notes note-2, note-3 (density barrier). Unfinished: path gadget
  L-meta-574 for h = 1, 2; 4-set count past n = 15 (may be false); width-2 cross formula. Nothing running there.
- session_01GmnDhdRKvz5Z7gneQqGG3V (machines-Lean = Lean helper of tractability, ex QG L-qg-103; attached here 09:25 with owner
  OK in its own chat; lands in 951/lean itself, coord spot-verifies): in 951/: MergeWorld + hval bridge, sum_equivFin(_subtype),
  MergeWorld2 (HeavySet, onlyMixed_iff, refined load split), Peel2 dedup into W951Cube, audit #21 (Small3 exists_second3K,
  hclean-free bounds), audit #10 (Dead via GateShape), audit #2 (Cleanup dropGate lemmas as instances, -76 lines; main d6d369d,
  gate: lake build 1 sorry outside PayDraft, one-file 0/1, axioms as README). Unfinished: none. Free for the next piece;
  from 11:32 bottleneck Lean (two-owner ShiftOff, CU) has priority over audits.
- session_01GmnDhfo8QCanitMDqFa2x1 (quantum gravity coordinator; integrates this board): `pnp-general`
  main; the same tree is on `pequalnp-work` `mirror/trusting-newton-2lz5jy` (342bed1). Unfinished:
  gaps L-gen-101 to 104 and L-qg-115, 116, 119, 169; the referee seat for angle C has received no claim.

- session_01GmnDheoRytFdZ9LUQXmuGK (pnp-subproblem; attached here 08:55 with owner OK in its own chat): role REFEREE B (merge-tree
  charging) for no_minCE. Unfinished: waits for front's B claims (~11:30). Older work on pequalnp-work: board-unified 5136256 (paused),
  board f865a6d (referee file, copied to 951/board/agents/pnp-subproblem-referee-angle2.md).
- session_01GmnDhgoeSPwoi25gcFxUPJ (checker-checker; attached here 09:28 with owner OK in its own chat; 1to1 seat = checker, with observer session_01GmnDhegXGF8MJNAhiA1AHp): Done: note-2, physics models vs the three barriers (unified gravity / CTCs / BBBV / holographic complexity -> relativization L-lib-061/062, algebrization L-lib-065/076, natural proofs L-lib-086; verdict: exact as a map, no barrier passed; L-lib-035 is vacuous per L-lib-093) at notes/checker/note-2-physics-models-and-the-three-barriers.md, with 3 Lean corollaries notes/checker/BarrierMap.lean (compiled on the pinned toolchain + Mathlib, std axioms only; not run through the checker). Same files on pequalnp-work mirror/serene-davinci-l1jdj2 5684af9. Unfinished: nothing; 0 agents.

- session_01GmnDhcTAHGf6Zx99zs3cPd (cTAHG, LP / price-form Lean for 951; attached here 09:45 with owner OK in its own chat): LANDED on main:
  ChainPick (2902b9b), SDR certificates on 35 hard circuits (SDRCert/SDRWitness/SDRWitnessFixh16), PriceOff build fix (93b5865),
  Augment.lean (7e901f6, written with 1 Fable): LAvoid + LAugmentLoose => MergeSDR; MergeSDR <=> LAvoid ∧ LAugmentLoose (referee's
  catch, 17851bd); OFFICIAL target LAugmentK K (no_minCE_of_augmentK). NOW: PROOF_PLAN rule 4 in Lean (LAugmentReach: improving
  moves only along states reachable from a fixed start); next: scaffold's larger-instance certificates. Issue #17 answered.
  Results: 951/board/agents/lpfix-mergefrac-lean.md.

- session_01GmnDhdwV8pW4adQkj9Ei3M (dwV8p; attached here 09:26 with owner OK in its own chat): role REFEREE for no_minCE.
  Done: Lemma K CORRECT (Lean: coord-951 19601c9); gAdyD's split-set item 3 CORRECT; scaffold's strict resolution gadget
  (A|y)&(A|~y) FALSE in general (cfgI, cxstar5/44, cxP1-3/5/6; it fits every circuit with s - base <= 7). Report + checkers:
  `951/work/notes951/lemmaK_referee/` (from pequalnp-work referee-lemmaK-dwV8p e0c113a); verdicts
  `951/board/agents/dwV8p-referee-*.md`. Earlier: D-qg-1 quantum circuits (L-qg-110 to 119, on main). Unfinished: nothing;
  free for the next referee assignment.

- session_01GmnDhgAdyDijthBgZgJFWn (ex D-qg-2; scaffold helper for 951; attached here 09:25 with owner OK in
  its own chat): D-qg-2 LANDED here (L-qg-120 to L-qg-127 checked, `Defs/QuantumGravityChannels.lean`;
  first version on pequalnp-proofs `claude/modest-brahmagupta-66n1fr` bddc02a). 951: no-mixed / heavy split
  rounds 1-4 in `951/board/agents/qg-d2-nomixed.md` (code: pequalnp-work `nomixed-951` 1bada7b). Unfinished:
  xgen runs for scaffold (front-A falsification, 4 systems with a 4-set, essential, base+1..+4; no X so far)
  -> `951/board/agents/qg-d2-xgen.md` when done.
- session_01GmnDhdZb2EsYNLc1r4M85e (dZb2E, ex QG L-qg-101; Lean helper of tractability for 951; attached here 09:22 with owner
  OK in its own chat; commits as addison-jpg): LANDED in 951/lean: LemmaK (MinCE.ex_ge_two, MinCE.lemmaK_V1, K1_bound),
  CrossWorld (S1(g) for merge sets needs (i) z' avoids S_a and (ii) C0(g)(Zof S_a) = 0; cx1/cx2 show both are necessary),
  PriceOff (MergePriceOff + ShiftOff -> MergePrice; single-owner gates shift for free; for crossSet that part is empty),
  MergeSDR (= integral MergeFrac; MergeSDR -> ChainPickOn -> MergePrice). Unfinished: nothing; free for the next assignment.

## Subboard: general circuits (L-gen)
Files: `lean/PEqualNP/Defs/General.lean`, `lean/PEqualNP/General/`. Cards: the targets and ladder above.
- Generalize (session_01GmnDhg8XTmohao5zo2MMaC), card rank 4 (exact sizes by gate elimination, NOT gates counted): rows
  L-gen-005, L-gen-006, L-gen-007 CHECKED (XOR with a fresh input; 007: a negated fresh input costs 1 or 2 gates, tool
  `restrict_one` = one gate saved on either side; proof `lean/PEqualNP/General/XorExtension.lean`, no minimality
  assumption: count the gates that are redundant after `x := c`). OPEN: `C(x ⊕ f) = min + 4` when `C(f) = C(¬f)`; a
  counterexample must have one fixed circuit shape (hand argument), and SAT finds none for every `f` on <= 3 variables and
  every 4-variable `f` with `C(f) = C(¬f) <= 5`. Note + evidence: `notes/general/generalize-xor-extension.md`,
  `tools/xor-extension/`.

## Subboard: the NOT gate ladder, rung 1 (L-meta-951)
Before starting a route: [`951/DEAD_ENDS.md`](951/DEAD_ENDS.md) (refuted routes, one line each).
Suggestions for the open step, with kill tests: [`951/PROOF_PLAN_SUGGESTIONS.md`](951/PROOF_PLAN_SUGGESTIONS.md).
How search code and Lean divide the work: [`951/PIPELINE.md`](951/PIPELINE.md) (the owner's framework:
Python/C++ searches and exports compact witnesses, Lean only checks).
Arrives one-to-one from `addison-jpg/pequalnp-work` branch `coord-951` (code) and `board` (notes).
Open statement: `no_minCE`. Candidates: price form, double counting over the merge tree, lifted
fractional induction.
- front (session_01GmnDheKL3UENhJCL6pD1hS; front cannot attach; notes in `951/front/` via coord's import): THE LEMMA (hload/MergeFrac): lanes A1/A2/B/C (4 Opus HALTED by the Opus limit until 11:30, auto-resume 11:32). HEAVY POINTS (agents/front-heavy.md): not excluded by current lemmas. 08:40 CORRECTION: pinned heavy split REFUTED by gAdyD R3 (320 ess circuits, B-B collisions); v2 CHECKED on all 39,168+4,764 pairs: sets avoiding v float over zero points in the half-cube x_v=1 (pure C0), star of v (sunflower) floats => LP <= 1 State file: `951/front/work/notes951/w9/RESUME_LANES.md` (front-match 169cec0).
- scaffold (session_01GmnDhdt8ydm1adQLjCP9we; scaffold cannot attach; row copied by warden 08:38): RESET ROLE (compute for the target): HARD4 done + minimality follow-up (resolution gadget); data-corpora pushed for support-B; NOW: optimal MergeFrac duals for front A -> agents/scaffold-duals.md State: pequalnp-work scaffold-951 e59751c, data-corpora 2aa9856.
- pnp-subproblem (session_01GmnDheoRytFdZ9LUQXmuGK): REFEREE B. V1 08:40: support-B's 'B1: 3rd+ merge gates of different |S|>=4 sets are disjoint' is FALSE, cxr gate 14 re-derived with independent code (both sets' 3rd merge). B rules must split shared gates and be tested on the hand-built family (cxr, cx44_*, cxT*, cxU*, cxP2). HARD4 re-checked. Notes: `951/board/agents/pnp-subproblem-referee-angle2.md`. PYTHON (owner rollout, discovery only): `951/tools/referee_b/check_charge.py` = JSON in / exact-rational JSON verdict out for any candidate B charge; on cxr, every charge supported only on 3rd+ merge gates FAILS, so B rules must charge gates outside them. SURVEY 09:30 (`951/tools/referee_b/README.md`): on 339 one-NOT circuits with a 4+-set, charging 3rd+ merges inside each set's own merge gates FAILS on cxU6/cxU8/cxU_6_4/cxU_8_4/cxP2, while support 'own cone minus every set's first two merges' is feasible on all 339 (data, necessary-condition check only). CROSS-CHECKED 09:43 by Research with w951 systems/merges/cone + own max-flow: 0 disagreements (951/board/agents/research-referee-b-crosscheck.md); definitions (z_S, atoms, first-two removal) shared, so this checks implementation, not definitions. LIT 09:44 (951/board/agents/research-hall-charging-lit.md): no printed fractional-Hall lemma for the D-shape; nearest template Pippenger 1980 Lemma 1 (cone-restricted path charging, load <= t^2, no capacity-1 step), then Wegener 1987 sec 6.6. The D-shape needs its own proof.

- research (session_01GmnDhdzjMKChKGfUadQDVf; desktop Research merged in 1:1, handoff pequalnp-work board
  agents/research-desktop-HANDOFF.md, 08:50): literature for unrestricted circuits done (notes/general/research-lit-unrestricted.md);
  for no_minCE: charging templates (pequalnp-work agents/research-charging.md: Li-Yang packing = potential with memory, Weiß
  bottleneck; CHECKED: merge-set families {M_z(w)} are not matroid bases). Inherited open items: StrictGadget (strict
  (A|y)&(A|~y) for MinCE; general gadget Lean-checked on pequalnp-work gadget-research 5844d46, awaiting coord merge);
  StrictGadget status (desktop Research, 08:36): FALSE for general circuits (cfgI: (A∨(x7∧h))∧(A∨¬h); cxstar5/44 Shannon
  split ¬x0∧(x0∨A)); for MinCE no paper proof, only 24/24 strict cases on 4 SAT circuits with s - base <= 7; 'dies under
  restriction' has no precise statement yet (y need not be a variable, e.g. x4|x6). PROVED with no extra hypothesis: MinCE.gadget
  (A∨p)∧(A∨q), p∧q = 0 off S; may suffice if the charging only needs a resolution AND with a NOT-polluted input.
  lemmaK-research f47e66a is an ABANDONED duplicate (do not merge); f_G lane: s = bcs is the single level conjecture,
  false for large n (Jukna TR05-021).

### 951 coord (session_01GmnDhdShHMzucEAq9ottn6): SYNTHESIS 09 UTC + FABLE ALLOCATION
- Lean (951/lean, main 67c30b2): 1 sorry (no_minCE). Since import: + RefinedNoMixedPrice (Case I price form, no_minCE_of_refinedNoMixedPrice), + HeavySplitFloat (Case II v2, no_minCE_of_heavyFloatCases). Both cTAHG, ported + verified by coord.
- REFEREE angle 1 (951/board/agents/coord-desktop-referee-angle1.md): Lemma M, load identity, Theorem F, duality, chain, level 4, MergeDual/World, MergeLink all CORRECT. KEY: the dual is proved only for single-gate prices; sum_w min_z pi(M_z(w)) is CONCAVE in pi, so K-Rado / 0-1 extreme prices are an unproved observation; MergePrice is fully open. NoMixedPrice is strictly stronger than MergePrice and was never checked on data (-> scaffold/gAdyD check FIRST). Wording fixed in W951.md (CoverPrice is weaker; MergeFrac only sufficient).
- Data: refined no-mixed LP <= 1 on 34,064 circuits; heavy split v2 <= 1 on 39,168 + 4,764 pairs; on 49 adversarial hard-4-set circuits WITH cross-world gates some optimal pi vanishes on them (scaffold). Refuted today: pinned heavy split; S1(g) for merge sets as stated (CrossWorld cx1/cx2); strict resolution gadget for general circuits.
- 09:15 P=NP Front (data; its Lean file waits for the owner's approval in its own session): climb over ~410k correct one-NOT circuits (cfgI mutants): NO MergeFrac L* > 1, best L* = 1.0 always forced. CfgI certificate (kernel-checked locally): gate 13 = h is in M_z(w) for BOTH 4-sets at every zero point with h(z) = 0 (charging both only in h = 0 worlds loads h with 2); dual K = {12, 18, 33} gives L* >= 2/3. dZb2E PriceOff.lean (local, owner approval needed to push): MergePriceOff + ShiftOff -> MergePrice; single-owner gates shift for free; for crossSet the easy part is EMPTY: ShiftOff(crossSet) = the two-owner case. Lean + no_minCE_of_coverPrice (5c01361). cTAHG next: does CrossWorldAt.ndep (ii) hold at every MinCE.
- 09:20 SCAFFOLD (referee's priority check, ~85.8k one-NOT circuits incl. 4,320 essential hard-4-set ones and the 49 with cross-world gates): PLAIN NoMixedPrice FALSE (62,256 failures, all but cxe3 are split sets with no world-0/world-1 zero point => infeasible); REFINED (heavy sets keep all zero points) 0 failures, max L = 1.0. Data fact: every split set contains a heavy point. => the Lean target is the REFINED form (no_minCE_of_refinedNoMixedPrice), not NoMixedPrice. Lean: + audit #21 (Small3 without hclean).
- 09:25 RESEARCH (951/board/agents/research-concave-dual.md): 0/1 prices fall short EXACTLY by the layer-cake gap (CHECKED 30/84 families, gap up to 3 on the sum); per world the gap nearly vanishes (9/82, 2/84) => proposed TWO-WORLD CHAIN LEMMA (CU): a 0/1-type statement that DOES imply MergePrice (answers the referee's concavity point). Front A1/A2 to evaluate first at 11:32.
- 09:30 P=NP Front (Fable attempt on MergeFrac worlds; no full proof): CONJECTURE MergeSDR: zero points z_w with pairwise DISJOINT merge sets exist (integral; implies MergeFrac) — holds 163/163 + 2 adversaries. Paper lemmas checked on data: cut sandwich, chain-pair lemma, pair theorem (sets have disjoint worlds unless configuration O2; CfgI is O2). Adversaries (NOTs inessential): ADV3 full L* = 0.75 but L = 1.2 on the menu {0, z_S} (scaffold testing the refined menu on it); ADV4: an N-dependent shared merge gate (refutes 'never below the NOT' in general). Smallest open lemma: O2-PAIR (details with front).
- 09:35 cTAHG (Lean CrossWorldCex.cx3_counterexample, f7b8fef): (ii) of CrossWorldAt.ndep fails on 155 live+essential+clean circuits, crossWorld_ndep under (i) alone on 60; ALL failures have s - base >= 5 (0 of 842 with s - base <= 4) => N-dependence of cross-world gates at a MinCE needs s < base itself. cTAHG next: research's CU lemma in Lean + CU -> MergePrice. P=NP Front now pushes to pnp-general (951/research/front612/).
- 09:40 FRONT (verified): ADV3 and ADV4 ARE essential (front-612's erratum was wrong). ADV3 (n = 12, three disjoint 4-sets): any FIXED two-point menu {0, top_w} gives L = 1.2 > 1, but the REFINED no-mixed form gives 0.75 (= full) and Case II v2 1.0 => the refined form and v2 SURVIVE; ADV3 is the test for any fixed-menu restriction. ADV4: N-dependent g16 in M_0(A) ∩ M_top_B(B); refined 1.0. Chain-pair lemma PROVED-PAPER (z <= z', |S_w \ z'| <= 1, g counted at (w,z) with g(z') = 0 => g N-dependent and h crosses 0->1 between z+e_u and z').
- 09:45 SCAFFOLD (CU, research's two-world chain lemma; 26 instances + ADV3/ADV4, both world-1 variants, heavy sets all points): 54 level-set chains of optimal pi: 0 failures, and with the chosen c ONE zero point per set minimises at every level (54/54); exhaustive A1 ⊇ A2 over merge gates: 270,356 pairs, 0 failures; A1 ⊇ A2 ⊇ A3: 46,620 triples, 0 failures. Full ~86k corpus running. CU in Lean: cTAHG; CU referee: desktop Coord. dRKvz now lands its own Lean in 951/lean (owner-approved attach).
- 10:00 P=NP Front (F1, data): MergeSDR (disjoint merge sets at some zero points z_w) HOLDS on ALL 27,991 distinct correct one-NOT circuits with >= 2 sets in the full corpus (data-corpora + w9 + instances; n - min|S| <= 14). The fixed two-world menu {0, top_w} fails on exactly 1: scaffold payment/ce3 (essential, n=8, s=34, 4 sets, max |S| = 3), besides ADV3. Files: 951/research/front612/sdr/. Next: F2 O2-PAIR hill-climb.
- 09:55 STRONG RESULTS: P=NP Front F1: MergeSDR (one zero point per set, pairwise DISJOINT merge sets) holds on ALL 27,991 distinct correct one-NOT corpus circuits with >= 2 sets (951/research/front612/sdr/). Scaffold CU (h(z) = 0 partition): 0 failures on ~1.1M exhaustive pairs/triples of the 6 non-uniform families + 3,000 random integer pi each (heights <= 6); 26 instances: 251,696 pairs, 46,620 triples, 25,000 random pi. Referee (desktop Coord): STRONG CU (= chain-SDR: per chain ONE z_w per set with sum_w |M_{z_w}(w) ∩ A_t| <= |A_t| for all t) => MergePrice is a one-line proof; MergePrice <=> the fractional-mixture version (LP duality on each chain). Proof idea: Hall/Rado along a chain, greedy from the smallest level outward with exchange. Lean: dZb2E MergeSDR, cTAHG StrongCU. PriceOff landed (260c852), audit #2 landed (dRKvz d6d369d).
- 10:15 (batched) LANDED: MergeSDR (no_minCE_of_mergeSDR, mergeSDR_of_integral), chainPickOn_of_mergeSDR, ChainPick (cTAHG; cu_counterexample: CU alone does NOT give MergePrice, ChainPick does), PriceOff — main 8fac655, 1 sorry. ASSIGNED: research = Aharoni-Haxell hypergraph Hall for MergeSDR (agents/research-hypergraph-hall.md); cTAHG = W951/SDRCert.lean, decide-checked MergeSDR certificates (CfgI, ADV3/4, ce3, HARD4, cxr; scaffold exports). OWNER via front's chat: research also assesses Blais-Canonne-Oliveira-Servedio-Tan 2015 (t NOT gates => total influence O(2^t sqrt n)) + the polynomial method for 951 (agents/research-negation-influence.md); tractability considers an infinite-series / continuous formulation (multilinear extension, noise-stability power series, n -> infinity limits). Framework: 951/PIPELINE.md.
- SYNTHESIS 10 UTC (951, coord, batched): Lean main df388aa, 1 sorry. LANDED since 09: MergeSDR (no_minCE_of_mergeSDR, = integral MergeFrac), chainPickOn_of_mergeSDR, ChainPick (CU alone insufficient: cu_counterexample), PriceOff, SDRCert + witnesses: MergeSDR KERNEL-CHECKED (decide) on 35 circuits incl. CfgI, ADV3/4, ce3, HARD4, cxr and the 24 forced-h fixh16 K4 circuits. DATA (scaffold): MergeSDR 0 failures on 75,619 circuits; L-avoid holds on all; L-greedy-avoid fails on 18,875 but repair always exists; gates shared by up to 5 sets; 2-SAT: 87% single world-1 option, 0 contradictory SCCs on 47,674, forcing depth <= 1; L-descent2 / L-descentPath: minimal improving move uses 1 set in 100,116 of 100,174 collision states, 2 sets in 58 (all fixh16, augmenting chains), never more. REFEREE (desktop Coord) PROOF PLAN: L-avoid + L-augment (augmenting chain of re-picks lowering #colliding pairs) => MergeSDR => no_minCE; open: why an augmenting chain must exist (Hall/exchange count + s < base). cTAHG: Augment.lean (the reduction, hypotheses only). Research: classical hypergraph-Hall (Haxell, Aharoni-Haxell) conditions FAIL here; BCOST influence verified but no gate-count consequence; tractability: infinite-series/continuous formulations add nothing (issue 12). Front lanes resume 11:32 on L-augment / MergeSDR.
- NEXT most important (10:30, coord, owner: 'push a bit harder'): kill tests (951/tools/kill_tests, PROOF_PLAN_SUGGESTIONS §0) put the WHOLE open step on the STAR OF A HEAVY POINT (front's Case II): for a heavy point u and the sets through u, zero points with pairwise disjoint merge sets exist, also disjoint from the canonical classes of the other sets (mixed zero points are necessary there; for the other sets W0/W1/X give disjointness). Test cases: cxe3 (n = 7, 8 SDRs), cxT2 (n = 9). Front's Opus lanes at 11:32 on this ONE statement; scaffold reruns W0/W1/X + the order test on 75k; W1 size gap / X bounds per referee (agents/coord-desktop-referee-plan.md) before Lean. CHECKPOINT 13:30 UTC: no referee-passed heavy-star argument => one lane moves to the MatchG fallback (bipartite, exact Hall; PROOF_PLAN_SUGGESTIONS P3). UPDATE 10:35: GM (general Lemma M) checked = LiftCount.lift_merges_pt, W1 size gap resolved (agents/coord-desktop-referee-plan.md addendum); W0/W1/X 0 violations at scaffold (26 + ADV, Z = top_w); Lean W0/W1/X = board integrator (CanonClass.lean). HEAVY-STAR CLASS form (star sets' real merge sets avoid K_0(b; m_b) for chosen minterms and K_1(b)) HOLDS for every heavy point on all 20 w951 heavy instances + ADV3/4, no CLASS/MERGE separation => prove CLASS; column in every ladder report. LANDED 10:45 (coord): L-AVOID PROVED (scaffold's Fable, zero point 0 for every set, the univMerge_disjoint argument) — Lean `lAvoid`, `no_minCE_of_augmentK_only` (951/lean Augment.lean; full build 1 sorry, axioms propext/choice/Quot.sound). The open target is now LAugmentK alone (K = 2 by data): the choice step.
- NEXT most important (10:20, owner-approved plan via desktop Coord): ONE target, angle 1: L-avoid (data: holds on all 75,619) + LAugment_2 (re-picked group of size <= 2; data: holds on 75,619, k = 1 in 100,116 of 100,174 collision states; size ladder on linear spaces v = 7, 9, 13, 16, ... in progress at scaffold, axes v, slack s - base, the NOT's input h) => MergeSDR => no_minCE. Lean: Augment.lean (no_minCE_of_augment, LAugmentLoose; NOTE LAugment with UNBOUNDED group is equivalent to MergeSDR, so the real target is LAugment_k, cTAHG adding LAugmentK); SDRCert: MergeSDR kernel-checked on 35 circuits.
- NEXT most important (09:25): prove the REFINED price form; candidate routes: research's two-world chain lemma (CU), and the two-owner ShiftOff (dZb2E PriceOff: single-owner gates shift for free; cross-world gates are all two-owner).
- FABLE ALLOCATION (owner 09:01, verified: "each opus should have two fables. maybe like 8 fables we can dole out here"; ~8 total):
  | # | Owner | Task |
  |---|---|---|
  | 1-2 | P=NP 'Front' (session_01GmnDhc6FBZAseL8bDQaYsu) | DONE 09:20 (951/research/front612): CfgI certificates kernel-checked; MergeSDR / O2-PAIR paper attempt. NOW (CPU, no Fable): F1 MergeSDR on the full ~41k corpus + F2 O2-PAIR hill-climb attack |
  | 3-4 | front A1 (session_01GmnDheKL3UENhJCL6pD1hS) | MergePrice dual for general pi (concavity!): 2 Fables under the A1 Opus at the 11:32 resume |
  | 5 | front B | merge-tree double counting with split shared gates (referee_b/check_charge.py as gate) |
  | 6 | front C | lifted fractional induction |
  | 7 | dZb2E (session_01GmnDhdZb2EsYNLc1r4M85e) | DONE, no Fable used: PriceOff.lean, MergeSDR.lean (+ chainPickOn_of_mergeSDR) landed (main 8fac655). Slot free |
  | 8 | research (session_01GmnDhdzjMKChKGfUadQDVf) | literature: min-of-sums / concave dual LPs with integral extreme points (Rado, polymatroid, submodular covering) for the K-Rado question |

## Subboard: quantum gravity (L-qg)
Files: `lean/PEqualNP/Defs/QuantumGravity*.lean`, `lean/PEqualNP/QuantumGravity/` (its README has
the tracks and references). 47 rows; gaps L-qg-115, 116, 119 (quantum counting) and L-qg-169
(P_CTC inside EXP). D-qg-2 landed: L-qg-120 (Deutsch's quantum consistency: every channel in Kraus form
on `Fin d`, `d > 0`, has a fixed density matrix; from `Helpers/FixedPoint.lean`), L-qg-121 (the
classical case embedded, from L-qg-102 via L-qg-127), L-qg-122 to L-qg-127 (channels preserve density
matrices; unital channels; the channel of a map of the basis; L-qg-120 => L-qg-121; L-qg-102 => L-qg-121).

## Subboard: compute (warden, session_01GmnDhe9JJ48acyaXmZHPPT)
Kill only what serves no card on this board; duplicates and dead loops are flagged here and pinged to the owning
session (desktop team via its Coord). Sessions are never interrupted by the warden. Models: avoid Fable, a few ok.
History before the move: `addison-jpg/pequalnp-work` branch `board-warden` (frozen).
- FABLE BUDGET (owner 09:01, typed to desktop Front, verified): "each opus should have two fables. maybe like 8 fables we can
  dole out here". ~8 Fables total, 2 per Opus agent, handed out by coord. Allocation (coord aa693da, 8 total): 1-2 desktop Front (running), 3-4 front A1 (MergePrice dual, general pi),
  5 front B, 6 front C, 7 dZb2E (PriceOff.lean), 8 research (concave-dual / K-Rado lit). Warden flags any Fable beyond these 8.
  WATCH: Fable 8 (research, K-Rado lit) vs Fable 2 (desktop Front, world-choice/K-Rado paper): keep literature vs proof split.
- 1to1 = owner 08:28 (Discussion session): "1to1 squish, research-> research xyz-> xyz": same-role sessions become one seat;
  Discussion (session_01GmnDheAyFnVcvRApd4xeES) runs the handoffs. Correction sent to all 18 sessions 08:36.
- Mirroring: coord's 1:1 import (951/, from pequalnp-work coord-951 + board + front-match) now carries the blocked seats'
  work; warden's duplicate notes/951/ copy removed 09:00. Warden only refreshes the front/scaffold rows on this board.
- Who is on pnp-general (08:58): coord (951/ moved, main 419deed; pequalnp-work FROZEN), research, pnp-subproblem, QG coordinator, warden, observer (branch checker 49dc787), desktop Tractability (branch tractability-kernel-612 e7e373f). Blocked by their own permission check
  (add_repo on a relayed OK; owner must say it in their chat, add an allow rule for mcp__claude-code-remote__add_repo, or
  start a new session with pnp-general): front, scaffold, checker-checker, desktop Coord (handing off to coord, 0 agents), cloud tractability (lands on pequalnp-work coord-951 ee11077; coord's 1:1 copy carries it) (state pushed to pequalnp-work; warden mirrors
  front + scaffold). Desktop Research: merged into research, idle. Others: pending reply.
- KILLED: desktop Tractability 612 C7 k=9 SAT: ended unfinished (k=9 undecided), confirmed 08:37.
- WATCH: none open. (Resolved: MergeFrac Lean single owner; Lemma K Lean = desktop Research, dZb2E -> CrossWorld.)
- Opus 5-hour limit until about 11:30 UTC: front's 4 Opus agents halted (auto-resume 11:32); Sonnet and CPU run.
