# Board: P versus NP through general circuits

The one board of this repository. Subboards are sections below; anything useful to everyone goes
in **Overarching**. A **row** is a checked statement; a **gap** is a statement written in Lean
that still needs a proof (a `Prop` definition, never a `sorry`); a **card** is any item here.
Nothing on this board says that P versus NP is settled.

## Overarching

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

**The NOT gate ladder (`SIZENot s t`: at most `t n` NOT gates).** This is how the restricted
work reaches the general problem.

| Rung | NOT gates | State |
|---|---|---|
| 0 | 0 (monotone) | superpolynomial bounds known (Razborov 1985) |
| 1 | 1 | L-meta-951: one NOT gate saves nothing on Boolean sums; one open statement, `no_minCE` |
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
| 6 | Rung 1 of the ladder: `no_minCE`, reduced to MergeFrac, a linear-programming duality statement | convex duality and fixed points: L-qg-102, `QuantumGravity/Helpers/FixedPoint.lean` | the same convex-duality mathematics; the right-hand side is checked |
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

**Ideas in the literature (research verifies; items marked * are from memory).** Gate
elimination (Li, Yang 2022 and earlier; its limits*: Golovnev, Hirsch, Knop, Kulikov). Fixed-degree
bounds above NP*: Kannan; Santhanam; Vinodchandran. Near-maximum bounds by range avoidance*:
Korten; Chen, Hirahara, Ren; Li. Algorithms give lower bounds*: Williams (NEXP not in ACC0).
Hardness magnification*: Oliveira, Santhanam; a slightly superlinear bound for one special problem
would give L-gen-101. Meta-complexity*: Hirahara; Liu, Pass. NOT gates*: Markov; Fischer; Beals,
Nishino, Tanaka; Amano, Maruoka; Jukna.

**Roles (they stay; coord assigns sessions).** coord: owns targets and assignments. front:
proofs. scaffold: compute (SAT, LP, small exact sizes). tractability: Lean landing. research and
the Generalize sessions: literature and generalization. warden: compute and model budget. The
quantum gravity sessions: the right-hand column of the track pairs, as helpers of the roles
coord paired them with. Integration of this board: session_01GmnDhfo8QCanitMDqFa2x1.

**Rules.** A row is "checked": no `sorry`, only `propext`, `Classical.choice`, `Quot.sound`.
Open statements are `Prop` definitions. Physics premises never enter a Lean statement. Old
repositories are frozen as they are; new work lands here. Models: avoid Fable runs, a few are
acceptable; Sonnet is fine. Never run `lake update`.

**Status (2026-11-24).** In this repository's two own programs: 43 rows checked (39 quantum
gravity, 4 general), 8 open gaps (L-gen-101 to 104; L-qg-115, 116, 119, 169). The programs
inherited from `brilliant-hq/pequalnp-proofs` (Library, CircuitLowerBounds, MetaComplexity, Gct,
ProofComplexity, Search, Outside) are here unchanged.

## Handoff lines (one per session: branch, commit, what is unfinished)
- session_01GmnDhfo8QCanitMDqFa2x1 (quantum gravity coordinator; integrates this board): `pnp-general`
  main; the same tree is on `pequalnp-work` `mirror/trusting-newton-2lz5jy` (342bed1). Unfinished:
  gaps L-gen-101 to 104 and L-qg-115, 116, 119, 169; the D-qg-2 card (density matrices) is on its
  own session's branch, state not reported; the referee seat for angle C has received no claim.

- session_01GmnDheoRytFdZ9LUQXmuGK (pnp-subproblem; attached here 08:55 with owner OK in its own chat): role REFEREE B (merge-tree
  charging) for no_minCE. Unfinished: waits for front's B claims (~11:30). Older work on pequalnp-work: board-unified 5136256 (paused),
  board f865a6d (referee file, copied to notes/951/pnp-subproblem-referee-B.md).

## Subboard: general circuits (L-gen)
Files: `lean/PEqualNP/Defs/General.lean`, `lean/PEqualNP/General/`. Cards: the targets and ladder above.

## Subboard: the NOT gate ladder, rung 1 (L-meta-951)
Arrives one-to-one from `addison-jpg/pequalnp-work` branch `coord-951` (code) and `board` (notes).
Open statement: `no_minCE`. Candidates: price form, double counting over the merge tree, lifted
fractional induction.
- front (session_01GmnDheKL3UENhJCL6pD1hS; copied 1:1 by warden 08:33 from pequalnp-work board + front-match, front cannot attach this repo): THE LEMMA (hload/MergeFrac): lanes A1/A2/B/C (4 Opus HALTED by the Opus limit until 11:30, auto-resume 11:32). HEAVY POINTS (agents/front-heavy.md): not excluded by current lemmas. 08:40 CORRECTION: pinned heavy split REFUTED by gAdyD R3 (320 ess circuits, B-B collisions); v2 CHECKED on all 39,168+4,764 pairs: sets avoiding v float over zero points in the half-cube x_v=1 (pure C0), star of v (sunflower) floats => LP <= 1 Notes: `notes/951/front-heavy.md`, `notes/951/front/RESUME_LANES.md`, `notes/951/front/s_fable.md`.
- pnp-subproblem (session_01GmnDheoRytFdZ9LUQXmuGK): REFEREE B. V1 08:40: support-B's 'B1: 3rd+ merge gates of different |S|>=4 sets are disjoint' is FALSE, cxr gate 14 re-derived with independent code (both sets' 3rd merge). B rules must split shared gates and be tested on the hand-built family (cxr, cx44_*, cxT*, cxU*, cxP2). HARD4 re-checked. Notes: `notes/951/pnp-subproblem-referee-B.md`.

## Subboard: quantum gravity (L-qg)
Files: `lean/PEqualNP/Defs/QuantumGravity*.lean`, `lean/PEqualNP/QuantumGravity/` (its README has
the tracks and references). 39 rows; gaps L-qg-115, 116, 119 (quantum counting) and L-qg-169
(P_CTC inside EXP).

## Subboard: compute (warden, session_01GmnDhe9JJ48acyaXmZHPPT)
Kill only what serves no card on this board; duplicates and dead loops are flagged here and pinged to the owning
session (desktop team via its Coord). Sessions are never interrupted by the warden. Models: avoid Fable, a few ok.
History before the move: `addison-jpg/pequalnp-work` branch `board-warden` (frozen).
- 1to1 = owner 08:28 (Discussion session): "1to1 squish, research-> research xyz-> xyz": same-role sessions become one seat;
  Discussion (session_01GmnDheAyFnVcvRApd4xeES) runs the handoffs. Correction sent to all 18 sessions 08:36.
- Mirroring: front and pnp-subproblem cannot attach this repo (add_repo denied in their sessions); warden copies their rows and
  notes from pequalnp-work each loop until they can.
- KILL: desktop Tractability (session_01GmnDhen7s1dyuiXAXQ8gjB) 612 C7 k=9 SAT, serves no card (s(C7) = 10 is
  Lean row L-meta-106); requested 08:17 via desktop Coord, relayed 08:15; awaiting stop.
- WATCH: none open. (Resolved: MergeFrac Lean single owner; Lemma K Lean = desktop Research, dZb2E -> CrossWorld.)
- Opus 5-hour limit until about 11:30 UTC: front's 4 Opus agents halted (auto-resume 11:32); Sonnet and CPU run.
