# Board: P versus NP through general circuits

The one board of this repository. Subboards are sections below; anything useful to everyone goes
in **Overarching**. A **row** is a checked statement; a **gap** is a statement written in Lean
that still needs a proof (a `Prop` definition, never a `sorry`); a **card** is any item here.
Nothing on this board says that P versus NP is settled.

## Overarching

**Goal.** Lower bounds for circuits of AND, OR and NOT gates with any number of NOT gates
(`SIZE`, `PPoly` in `lean/PEqualNP/Defs/CircuitLowerBounds.lean`), with every method that fits:
circuit complexity, quantum gravity, pure mathematics. Owner, 2026-11-24: one place, everyone
merged, the merge is one-to-one, no refactoring of old material.

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

**The one-to-one table: each P versus NP track beside its counterpart.**

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
quantum gravity sessions: the right-hand column of the one-to-one table, as helpers of the roles
coord paired them with. Integration of this board: session_01GmnDhfo8QCanitMDqFa2x1.

**Rules.** A row is "checked": no `sorry`, only `propext`, `Classical.choice`, `Quot.sound`.
Open statements are `Prop` definitions. Physics premises never enter a Lean statement. Old
repositories are frozen as they are; new work lands here. Models: avoid Fable runs, a few are
acceptable; Sonnet is fine. Never run `lake update`.

**Status (2026-11-24).** In this repository's two own programs: 43 rows checked (39 quantum
gravity, 4 general), 8 open gaps (L-gen-101 to 104; L-qg-115, 116, 119, 169). The programs
inherited from `brilliant-hq/pequalnp-proofs` (Library, CircuitLowerBounds, MetaComplexity, Gct,
ProofComplexity, Search, Outside) are here unchanged.

## Subboard: general circuits (L-gen)
Files: `lean/PEqualNP/Defs/General.lean`, `lean/PEqualNP/General/`. Cards: the targets and ladder above.

## Subboard: the NOT gate ladder, rung 1 (L-meta-951)
Arrives one-to-one from `addison-jpg/pequalnp-work` branch `coord-951` (code) and `board` (notes).
Open statement: `no_minCE`. Candidates: price form, double counting over the merge tree, lifted
fractional induction.

## Subboard: quantum gravity (L-qg)
Files: `lean/PEqualNP/Defs/QuantumGravity*.lean`, `lean/PEqualNP/QuantumGravity/` (its README has
the tracks and references). 39 rows; gaps L-qg-115, 116, 119 (quantum counting) and L-qg-169
(P_CTC inside EXP).
