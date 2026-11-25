# Board: P versus NP through general circuits

Refactored 2026-11-25 (seat R1) bottom-up: findings (`findings.jsonl`) → `boards/TREE.md` → this file → task boards. The text before the refactor is in git: `git show 1f3cc11:BOARD.md`.

- **TOP NOW (Addison, 2026-11-25): asteroid.exe becomes a real terminal (mintty, like Git Bash) on a native backend, less Python, no matplotlib, minimal Lean.** Five seats in order, one Sonnet each. [`asteroid-term`](boards/tasks/asteroid-term.md)
- **FILES FOR ADDISON (2026-11-25): give a direct link, not only a file card.** Commit the file (a .vsix, a logo, a PNG) and give `https://github.com/addison-jpg/pnp-general/raw/main/<path>`.

## CURRENT STATE (formal style, one line per program; every claim is a finding in [`boards/TREE.md`](boards/TREE.md) or a task board)

- **one-NOT** ([`open-one-not`](boards/tasks/open-one-not.md)). Checked chain: `BottomPay → LightAbsorb → DDAbsorb → MixedCount → no_minCE → L_meta_951` (`LightAbsorb.lean`, `DDAbsorb.lean`, `MixedStepNegIff.lean`, `MinCE.lean`; the step DDAbsorb + no-DD count ⇒ MixedCount is paper, A4 note §2). Open: **BottomPay**, a Hall condition on the bottom forests of DD sets (0 failures at about 1.27 million DD states; bottom runs of two DD sets overlap, so a matroid-union re-choice is needed). `no_minCE` is NOT proved; the general one-NOT theorem is NOT proved.
- **several-NOT** ([`open-many-not`](boards/tasks/open-many-not.md)). Proved, any number of NOT gates: OR of n inputs needs n−1 gates (`Or4ManyNot`), OR systems need n − comp (`OrSystemManyNot`), S3(a) per-set flip lemma (`FlipLemma`), Hall core and point-lemma ingredients (`FlipHall`, `PointLemma`); C4w refuted at 4 NOT gates. Open: **the point lemma** for two sets, reduced to **rule R2** (S3(b) reduces to it via the thin-basis lemma).
- **quantum gravity** ([`open-qg`](boards/tasks/open-qg.md), [`qg-frontier`](boards/tasks/qg-frontier.md)). Proved (standard axioms): L115 (C = 4), L116 from L115, L169 (P_CTC ⊆ EXP), L119 in the weak forms 16k and 15k+1 (`KnillParam15.lean`) and conditional on `KnillParametrization`, `CtcReset`, `GateNet`, `ApproxCount` (Knill count for continuous two-qubit gates). Open: the exact **9k+3n+1** form (`KnillParametrization`, KAK for U(4), not in Mathlib) and the **PSPACE encoding** into P_CTC.
- **limits** (below, `one-not/research/open/limits_*`). L1: obstacle found, |F2| is an exact sum over gates of an "exists context Z" indicator, not a bounded-size pattern sum. L2: literature rows (LITERATURE.md §L), no circuit-side limit theory found. L3: STOPPED (container restart), partial script kept. No theorem here.
- **philosophy** ([`philosophy-formal`](boards/tasks/philosophy-formal.md)). Three checked files: `Deleuze.lean`, `Fisher.lean`, `Bridge.lean`. Bridge finding: Φ is a projection of the slack table, not the whole virtual (`PhiT_not_injective`, `corners_not_injective`). A formal analogy; it claims nothing about Deleuze or circuits.
- **asteroid** ([`asteroid-term`](boards/tasks/asteroid-term.md), [`asteroid-exe`](boards/tasks/asteroid-exe.md), [`asteroid-vscode`](boards/tasks/asteroid-vscode.md), [`asteroid-cli-logo`](boards/tasks/asteroid-cli-logo.md), [`ath-prompt-quant`](boards/tasks/ath-prompt-quant.md)). Python front end (`python3 -m asteroid`, kernel-checked claims, `eval_sound`); native Lean binary with `.bench` reader, `repl` and `plot phi` (SVG), both tested against Python; `asteroid.exe` at the root (PyInstaller; the workflow is being rewritten to build the 6 MB native Lean binary, TAKEN); `.ath` highlighting published on the VS Code Marketplace (`asteroid.asteroid` v0.1.0, Open VSX not yet). Open: native-small, the mintty bundle, the CLI logo.
- Between this and P versus NP lie the general one-NOT case, every further NOT gate, and the known barriers (relativization, algebrization, natural proofs). Nothing here says P versus NP is settled or near.

## TOP: THREE LEVELS, BOTTOM TO TOP (Addison, 2026-11-25: "at the bottom its variable, at the middle its absurd polynomial feild, and at the top it becomes crazy overlapping infinities that we bound and match")

Assessment (main): rational; a known proof pattern, flag algebras plus stability plus a finite check.
- **Bottom, variable (finite n):** circuits, sets, cubes. Everything checked lives here; tests reach n ≤ 11 exhaustively, n ≤ 16 sampled (evidence, never a proof for all n).
- **Middle, polynomial field:** densities of small patterns are polynomials (Φ(p) of degree n in p). Tried alone on 2026-11-24 and closed: on the cubes every continuous route is the count again or refuted (twin trees, Fano corpus); [`continuous-mapping`](boards/tasks/continuous-mapping.md). Only the bridge.
- **Top, limits:** n → ∞; "gates ≥ base" becomes an inequality between pattern densities, proved by finite computation (flag algebras, Razborov 2007; hypergraph limits). Gives only gates ≥ (1 − o(1)) · base; the exact statement needs a stability step plus the bottom check. Risk: the count is exact and integer, limits lose o(n); the Fano corpus (245 non-up-set tight cubes) is the place to look.
- DECIDED L1 (Sonnet): density form tested on 17 circuits: base is an exact pattern count; |F2| is an exact sum over gates of an "exists context Z" indicator (Z = 0 local form misses up to 21 of 30 gates); linear forms are one-sided (necessary pi1 ≥ beta, sufficient pi1 − pi2 ≥ beta). -> `one-not/research/open/limits_density_form.md`
- DECIDED L2 (Sonnet): literature rows for flag algebras, hypergraph limits, flag-algebra-plus-stability results, limit theory for circuits: LITERATURE.md section L, 13 rows, search-result-only; an unopened Oxford thesis lead.
- STOPPED L3 (container restart; partial `limits_local_witness.py` kept; reopen as OPEN) (Opus): bounded local witness for F2 (adjusted after the L1 obstacle); was: attempt a flag-algebra certificate on the smallest pattern size; list the tight limit objects. -> `one-not/research/open/limits_certificate.md`

## RULES

- **SEAT SIZE (Addison, 2026-11-25: "some agents are too big here ... refactor with more sonnets").** A seat is one narrow task with one output file and one DECIDED line; parts become seats. Sonnet by default. Opus only for a single paper-proof attempt whose exact target is already written on the board. No Fable. An Opus that finds sub-lemmas writes each as `- OPEN (Sonnet): <exact statement> -> <file>` and stops.
- **QUIET UNTIL ADDISON SAYS IT IS READY (Addison: "i rlly dont wanna accidentally notify the entire planet befoore its ready").** Full speed on the work; pushing commits to main is fine. Nothing that notifies anyone outside this repo: no issues, PRs, comments, releases, tags, `@name` mentions, posts or requests to outside sites. Addison announces; agents never do.
- **PHILOSOPHY (Addison, "take very seriously").** Build crudely from existing logical formalisations up to Deleuze, Mark Fisher if cheap, synced through the boards. Deleuze's virtual / actual reads onto the three levels (actual = finite circuits, virtual = polynomial and limit levels). A formal model of a cited reading, never a claim about what Deleuze meant. [`philosophy-formal`](boards/tasks/philosophy-formal.md)
- **QG FRONTIER (Addison, "extremely good").** One research line: complexity = volume / action, holographic codes, CTCs, circuit-complexity growth, Brown–Susskind; what the repository proves; next formal targets reachable in Lean. [`qg-frontier`](boards/tasks/qg-frontier.md)
- **THE AIM IS P VERSUS NP. SAY SO (owner, 2026-11-24: "dont hedge").** Write the aim plainly, no "merely" or "only a toy". The work is public so that a result on this problem is readable and checkable by anyone, not paywalled or owned; do not water that down. The project has NOT proved P ≠ NP or P = NP, and nothing here may say or suggest that it has or is nearly there. What is proved is an exact bound for circuits with one NOT gate in three cases; between it and P versus NP lie the general case, every further NOT gate, and the known barriers.
- **STATE RESULTS AT FULL STRENGTH. NO HEDGING BEFORE REVIEW.** The one-NOT question is OPEN in the literature (Jukna and Sergeev 2013 §7, Blum 2024) and no result on it has been published: write that as a fact, and that the results here are the first. Write what is proved as proved, without "it seems". The one line that does not move: proved means the proof checker accepted it; the general one-NOT theorem is NOT proved (`no_minCE`); strong wording never upgrades tested or conjectured to proved.
- **THE BOARDS ARE A DATA STRUCTURE. NO MORE GRAFFITI (owner, 2026-11-24).** A finding is a record in `findings.jsonl` in the directory of its evidence: id, who, README item served, ONE word (checked / paper / tested / refuted / open / premise), one statement, evidence (`file` or `file.lean::theorem_name`), who confirmed. VERIFIED when its evidence exists (`checked` needs a theorem in a `.lean` file; anything else needs a second seat in `by`). Only verified findings propagate up to [`boards/TREE.md`](boards/TREE.md) (generated; the root shows what the repository has verified). Commands, repo root: `python3 -I boards.py add DIR WHO ITEM WORD "STATEMENT" EVIDENCE...` · `python3 -I boards.py confirm ID WHO` · `python3 -I boards.py` (rebuild; after any merge). Evidence names must be the bare theorem name found in the file (a namespace-qualified name fails the check). Task files say what to do (statement, done-when, OPEN/TAKEN/STOPPED, one "Decided" list, one "Refuted / dead" list); results are findings.
- **NOBODY ASKS ADDISON. USE THE BOARDS.** A question is an `[ASK]` line on the task board; unanswered after 15 minutes, DECIDE and write `[DECIDED] what and why`. One task = one file in [`boards/tasks/`](boards/tasks/) with one statement and one done-when; new task = new file and one row in the table below; do not grow this file. One writer per file where possible; do not rewrite another seat's lines.
- **MERGE CONFLICTS are never a reason to ask.** `git fetch origin main && git merge --no-edit FETCH_HEAD` (never force-push, never rebase others' commits). Boards, `LITERATURE.md`, `DEAD_ENDS.md`, `INDEX.md` merge by union (`.gitattributes`); `NAMES.md` is generated (`python3 -I names.py` after a merge); `README.md`: keep the other side, re-apply your item by hand; Lean or Python: keep BOTH, a clashing declaration goes in a new file `<Module>_<seat>.lean`. Rejected three times: write `[BLOCKED]` and take another task.
- **NAMES: FORMAL PROOF STYLE.** One formal name and one role per item (Definition, Lemma, Theorem, Conjecture, Open, Refuted, Counterexample). Property `UpperCamelCase` (`MinCE`, `CubeLocal`), object `lowerCamelCase` (`realWitness`), theorem `conclusion_of_hypotheses` (`no_minCE_of_ugame`), minimal-counterexample fact `MinCE.no_rewire`, counterexample `Cex.<name>`, refuted statement `Refuted.<name>`. No bare F2 / R6 / cxT2 in new text (old code in brackets once). [`NAMES.md`](NAMES.md) is GENERATED from [`names.py`](names.py).
- **LITERATURE FIRST.** One index: [`LITERATURE.md`](LITERATURE.md). Read it before you prove or search; add what you read with its read status. Never drop a literature note.
- **THE README IS THE PROOF.** [`README.md`](README.md) has numbered items (D1 to D7, L1 to L4, T1 to T9, C1, C2, the refuted table). Results go up as findings, with their word; every agent, note and finding says which item it serves; work that serves no item stops. One seat edits README.md; nobody else touches it; if your work changes a fact stated there, write one line on your task board. Boards: this file, [`boards/one-not.md`](boards/one-not.md), [`ladder.md`](boards/ladder.md), [`physics.md`](boards/physics.md), [`ops.md`](boards/ops.md); a README is not a board.
- **PULL, DO NOT PUSH (coming for the whole repository, when the open asteroid tasks land):** agents pull, work, and hand results to the one integrating seat that pushes. Until Addison switches it on, seats keep pushing small commits, their own files only.
- **PROCESS LIMITS (2026-11-24, in force until lifted):** at most 2 solver or search processes per container; no new subagent unless its task board exists; kill background jobs that serve no board; one push per result; no message where a board line will do. Do NOT call the Claude API (billed per token); no acks between sessions. Late stage: ambition over thoroughness, messy is ok, but checked still means checked (no `sorry`, standard axioms) and refuted claims stay off the board. Build on a capable agent's claim without rerunning it; spend refuting effort only where it blocks or contradicts your work.
- **Smallest agent that can do the job, always** (Addison, 2026-11-24). Proved means the proof checker accepted it; the pure-Lean check (`cd one-not/lean && lake build PEqualNP.Verify.All`) must keep passing.

## SUPERSEDED OR CLOSED (one line each; full text in git, `git show 1f3cc11:BOARD.md`)

- CURRENT TARGETS, REOPENED (nine seats), and the 22:49 "ONLY ASTEROID … CLOSED" section: replaced by CURRENT STATE above; the three open problems stay open (seats on their task boards).
- WHAT ASTEROID CANNOT YET SAY (ten-row wish table): the live list is `grep -rn "# WISH:" asteroid/` (21 lines); whoever adds the words deletes the line. Rows 1 to 10 are in the old file.
- PRIORITY table (L5 chain sum, C3 k-point step, D9 / C4(t), L6 gravity link, literature for C4, Millennium statement, Python as outward search): the status lives in README items and findings (`ChainSum.lean`; C4w refuted at t ≥ 4, C4g open for t ≥ 2); table in the old file.
- THE WALL (2026-11-24 graffiti, walls "non-discrete physics" and "anything else"): closed; non-discrete physics results are in `notes/phys/nondiscrete-lit.md` and `notes/phys/RealOracle.lean`; the rest is the day-1 session log.
- NEXT STEP: A MESSY CONTINUOUS MAPPING, SUBAGENTS SHOULD CHECK BOARD: superseded by the findings tree; `continuous-mapping` is closed (below).
- Roles of sessions (coord, front, scaffold, tractability, research, warden) and the 2026-11-24 status count (54 rows, 8 gaps): history, in the old file.

## Tasks (the small boards)

| Task board | Serves | Statement | Seats |
|---|---|---|---|
| [`asteroid-bench`](boards/tasks/asteroid-bench.md) | the asteroid language | Circuits in ONE pre-existing format: ISCAS ` | one Fable of main |
| [`asteroid-native`](boards/tasks/asteroid-native.md) | the asteroid language | asteroid with no Python: a command-line program written in Lean (one Lake executable) that reads an  | one Fable of main |
| [`asteroid-look`](boards/tasks/asteroid-look.md) | the asteroid website and terminal output | A colour scheme chosen by the owner: a small page with a colour picker per role (background, surface | coord, with small agents |
| [`open-one-not`](boards/tasks/open-one-not.md) | the Theorem (one NOT gate) | the general case, `no_minCE`; open: BottomPay | A1 to A14 |
| [`open-many-not`](boards/tasks/open-many-not.md) | C4 (several NOT gates) | S3(b); open: point lemma for two sets, rule R2 | B1 to B11 |
| [`open-qg`](boards/tasks/open-qg.md) | T9 | L-qg-115, 116, 119, 169; open: the 9k+3n+1 form | C1 to C5 |
| [`qg-frontier`](boards/tasks/qg-frontier.md) | T9 | frontier survey and ranked formal targets | Q1 to Q4 |
| [`philosophy-formal`](boards/tasks/philosophy-formal.md) | the three levels (Deleuze, Fisher) | formal model of a cited reading, bridge to Phi | P1 to P4 |
| [`asteroid-term`](boards/tasks/asteroid-term.md) | asteroid | asteroid.exe as a mintty terminal on the native backend | five seats |
| [`asteroid-exe`](boards/tasks/asteroid-exe.md) | asteroid | double-clickable `asteroid.exe` linked from the front page | one Sonnet |
| [`asteroid-cli-logo`](boards/tasks/asteroid-cli-logo.md) | asteroid | the 4STeroid logo as text art in the CLI | coord's Sonnet |
| [`asteroid-vscode`](boards/tasks/asteroid-vscode.md) | asteroid | `.ath` highlighting in VS Code (published) | coord's Sonnet |
| [`ath-prompt-quant`](boards/tasks/ath-prompt-quant.md) | `ath_prompt_method.md` | a quantitative version of one prompting claim | Sonnet |

**Closed on 2026-11-24 by the owner ("close all nonsense being done that isnt asteroid related").** Their files stay as the record; nobody works on them: `asteroid-bridge`, `asteroid-mixed-slack`, `asteroid-corpus`, `lean-eureka-asteroid`, `asteroid-cheap-proofs`, `asteroid-programs`, `beyond-one-not`, `edges`, `all-not-gates`, `rewire-read-not`, `c2-under-no-rewire`, `c1-three-gate`, `c4g-two-not-gates`, `family-for-many-not-gates`, `literature-c4`, `continuous-mapping`, `xor-extension-open-case`, `kannan-machine`, `qg-gaps`, `clay-model-equivalence`, `file-tree-merge`, `search-harness`, `telescope-l5-l6`, `lang-integration`.

## The boards

Each board serves numbered items of [`README.md`](README.md). Write on the board of the item you serve.

A few boards instead of one long one (owner, 2026-11-24: "its ok to have few boards now if its much better than readme strat"). Each board serves numbered items of [`README.md`](README.md), which is the proof. Write on the board of the item you serve; what everyone must see goes on the wall below.

| Board | Serves | Open now |
|---|---|---|
| [`boards/one-not.md`](boards/one-not.md) | the Theorem: D1 to D7, L1 to L4, T1 to T5, C1, C2 | C3 (priority): the k-point step, README §6. C1: a minimal counterexample that loses the certificate game |
| [`boards/ladder.md`](boards/ladder.md) | T6, T7 | L-gen-101 to 103; the XOR extension when C(f) = C(¬f); the Kannan machine |
| [`boards/physics.md`](boards/physics.md) | T8, T9, the premise | L-qg-115, 116, 119, 169 |
| [`boards/ops.md`](boards/ops.md) | no item: handoffs, compute, kill list, file tree | the README branch; second pass of the kill list |

## Reference (kept in full: targets, ladder, track pairs, literature)

The one board of this repository. A **row** is a checked statement; a **gap** is a statement written in Lean that still needs a proof (a `Prop` definition, never a `sorry`). Nothing on this board says that P versus NP is settled.

**How the pieces fit:** [`SYNTHESIS.md`](SYNTHESIS.md) (three layers: theorems, certificates and data, premises and maps; relativization against physical models; where L-meta-951 sits).
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
| L-gen-104 | `⌈log₂ (n + 1)⌉` NOT gates are as good as any number, up to a polynomial factor | CHECKED 2026-11-24: `PEqualNP.General.Fischer.L104 : Gap.L104` (`General/FischerMain.lean`), p = 30 (X + 1)^3; Markov 1958, Fischer 1975 |

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
| 1 | 1 | L-meta-951: one NOT gate saves nothing on Boolean sums; one open statement, `no_minCE`. Lives in `one-not/` (separate Lake project `one-not/lean`, imported 1:1 from pequalnp-work coord-951 ee11077; board history `one-not/board/`). Sharpest open form: `MergePrice` for a minimal counterexample. Coord: session_01GmnDhdShHMzucEAq9ottn6 |
| k | fixed `k`, then `k` growing | Amano, Maruoka 2005: clique with `(1/6) log log n` NOT gates |
| n | `n` (NOTs on inputs only) | CHECKED: `Fischer.stage1`: SIZE s ⊆ SIZENot (2s + n + 2) n (dual rail) |
| top | `⌈log₂ (n + 1)⌉` | equal to unrestricted circuits up to a polynomial factor: CHECKED (L-gen-104, `Fischer.L104`) |

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
| 3 | L-gen-104 (Fischer) as a row; Kannan's theorem as a row (needs the second level of the hierarchy) | tractability, helpers; L-gen-104 DONE by GeNeRALIZE (General/FischerBasic, FischerInverter, FischerMain; std axioms): a superpolynomial lower bound for circuits with ⌈log₂(n+1)⌉ NOT gates is now, in Lean, one for all circuits. Kannan's circuit half DONE (GeNeRALIZE): `SizeHierarchy.size_hierarchy`: ∀ k ∃ L ∈ P/poly, ∀ c, L ∉ SIZE(c n^k + c) (General/SizeHierarchy.lean, std axioms); uniform half REDUCED (GeNeRALIZE; General/Kannan{Defs,Lang,Sigma}.lean, std axioms): `KL k` = lex-first hard truth table; `KL_not_SIZE`; `mem_KL_iff` (exact ∃∀∀∃ form over a computable `Check`); `kannan_uniform_of_check : CheckLinTime k → ∃ L ∈ SigmaP 3, ∀ c, L ∉ SIZE(c n^k + c)`. ONE GAP: `CheckLinTime k` (a TM2 machine deciding `CheckW` in time linear in the total input: circuit evaluation at all 2^m points + lex compare; est. thousands of lines of machine code). Σ₂ ∩ Π₂ (Karp–Lipton) not started |
| 4 | What is out there for unrestricted circuits: verify and extend the list below | research, the Generalize sessions |
| 5 | Read the official Clay problem description | DONE (session_01GmnDhgAdyDijthBgZgJFWn, claymath.org added to its environment): Cook's official text read; P and NP in `Defs/Base.lean` match it up to standard model equivalences (one-tape TM vs `FinTM2`, alphabet, witness bound), not formalized; `notes/general/clay-official-statement.md` |

**Ideas in the literature (research verified 2026-11-24; exact statements, DOIs and what was read:
`notes/general/research-lit-unrestricted.md`).** Gate elimination: Li, Yang 2022 3.1n - o(n) over all binary gates; Iwama,
Morizumi 2002 5n - o(n) in the De Morgan basis (NOT gates not counted); limits: Golovnev, Hirsch, Knop, Kulikov. Fixed degree
above NP: Kannan 1982 (Σ2 ∩ Π2; one summary disagrees, flagged), Cai (S2P ⊆ ZPP^NP), Vinodchandran (PP), Santhanam (MA/1).
Near-maximum: Korten 2021; Chen, Hirahara, Ren 2024 (S2E/1, 2^n/n); Li 2024 (S2E, almost everywhere). Algorithms to lower
bounds: Williams (NEXP ⊄ ACC0); Murray, Williams (NQP). Hardness magnification: Oliveira, Santhanam 2018; McKay, Murray,
Williams 2019; locality barrier: Chen et al. 2020. Meta-complexity: Hirahara 2018; Liu, Pass 2020. NOT gates: Markov;
Fischer; Amano, Maruoka; Sung, Tanaka; Jukna; Jukna, Lingas. Slice functions (monotone bounds transfer to unrestricted
circuits): Berkowitz; Valiant 1986; Wegener; Hiltgen, Paterson 1995.

**Watch (2026-11-24, raised by tractability).** There are two different `PEqualNP.Kernel` circuit
kernels: `lean/PEqualNP/Kernel/Circuit.lean` (root project) and `one-not/lean/PEqualNP/Kernel/Circuit.lean`
(the 951 kernel, which the 951 modules depend on). Tractability proposed to coord: drop the root
one and merge `one-not/lean` into `lean/`. Until coord decides, do not build new work on the root
`Kernel`.

**Rules.** A row is "checked": no `sorry`, only `propext`, `Classical.choice`, `Quot.sound`.
Open statements are `Prop` definitions. Physics premises never enter a Lean statement. Old
repositories are frozen as they are; new work lands here. Models: avoid Fable runs, a few are
acceptable; Sonnet is fine. Never run `lake update`.

