# A map, not progress on P vs NP

Seat W1, task [`worlds-map`](../boards/tasks/worlds-map.md), 2026-11-25. P vs NP is one binary cut inside a landscape with many axes. This note lists the axes and worlds from the task board, each with a statement, a source, a status and an honest read status. Nothing here says P vs NP is settled or near. This repository's results appear only as points on the circuit axes (last section), never as evidence about P vs NP.

**Status:** proved / open / known conditional. **Read status:** read in full / abstract / search result / from memory. Network note: en.wikipedia.org did not resolve in this session, so nothing was read there; arXiv, ECCC and publisher pages were not opened either. Most entries are therefore *from memory* or *search result*. Re-read before relying on any of them.

## The proved part of "infinitely many levels"

| Entry | Statement | Source | Status | Read |
|---|---|---|---|---|
| Time hierarchy | For time-constructible f, g with f(n) log f(n) = o(g(n)), DTIME(f) is strictly inside DTIME(g). So P contains infinitely many strictly nested levels (n, n², n³, ...), and so does EXP. | Hartmanis and Stearns, Trans. AMS 117 (1965) 285-306 (tight log factor: Hennie and Stearns 1966) | proved | from memory |
| Space hierarchy | For space-constructible f, g with f = o(g), DSPACE(f) is strictly inside DSPACE(g). | Stearns, Hartmanis, Lewis 1965 | proved | from memory |

Everything below about infinite structure is open or conditional. (Ladner 1975, "On the structure of polynomial time reducibility", JACM 22: if P ≠ NP then infinitely many degrees lie between P and NP-complete. Conditional. From memory.)

## Axes

| Axis / world | Statement | Source | Status | Read |
|---|---|---|---|---|
| Time exponent: galactic P = NP | P = NP is compatible with an algorithm of astronomically large degree or constant, useless in practice. Levin's universal search is optimal-up-to-constant if any polynomial algorithm for NP exists, with an impractical constant. | Levin 1973 (Problems of Information Transmission 9); Cook, Clay description | open (P vs NP) | from memory |
| Time exponent: quasi-polynomial | NP ⊆ DTIME(n^(polylog n)) is not known to be false, and not known true. It would not give P = NP. | folklore; see Cook, Clay description for the definitions | open | from memory |
| Average case: Algorithmica | P = NP, or NP ⊆ BPP: NP is easy even in the worst case. | Impagliazzo, "A personal view of average-case complexity", Proc. 10th IEEE Structure in Complexity Theory (1995) | open | search result (secondary summaries) |
| Average case: Heuristica | NP is hard in the worst case but easy on average for every efficiently samplable distribution. | same | open | search result |
| Average case: Pessiland | NP is hard on average, but one-way functions do not exist. | same | open | search result |
| Average case: Minicrypt | One-way functions exist, public-key cryptography does not. | same | open | search result |
| Average case: Cryptomania | Public-key cryptography exists. | same | open | search result |
| Non-uniformity | Karp-Lipton: NP ⊆ P/poly implies the polynomial hierarchy collapses to its second level (Σ₂ = Π₂). So NP ⊆ P/poly with P ≠ NP is not known false; it would be a collapse of PH. | Karp and Lipton, STOC 1980 (in L'Enseignement Math. 28, 1982) | known conditional (implication proved; the antecedent is open) | from memory |
| Provability | P vs NP being independent of ZFC or PA is not ruled out; Aaronson's survey discusses it and argues independence is no more likely than for other natural problems. | Aaronson, "Is P versus NP formally independent?", BEATCS 81 (Oct 2003) | open | search result (survey title, venue and summary) |
| Barrier: relativization | There are oracles A, B with P^A = NP^A and P^B ≠ NP^B, so relativizing proofs cannot decide P vs NP. | Baker, Gill, Solovay, SIAM J. Comput. 4 (1975) | proved | from memory (project rows L-lib-061/062 checked per LITERATURE.md §H) |
| Barrier: natural proofs | If strong one-way functions (pseudorandom generators) exist, no "natural" (constructive, large) proof technique shows super-polynomial circuit lower bounds. | Razborov and Rudich, JCSS 55 (1997) | known conditional (on the crypto assumption) | from memory |
| Barrier: algebrization | Algebrizing techniques cannot separate P from NP (also not resolve several other class relations). | Aaronson and Wigderson, STOC 2008; ACM TOCT 1(1) 2009 | proved (as a barrier) | abstract / search result |
| Fine-grained: ETH | k-SAT (k ≥ 3) has no 2^(o(n)) algorithm; formally s_k > 0. | Impagliazzo and Paturi, CCC 1999; JCSS 62 (2001) | known conditional hypothesis (open) | search result |
| Fine-grained: SETH | For every ε < 1 there is k such that k-SAT has no O(2^(εn)) algorithm. | Impagliazzo, Paturi, Zane; Impagliazzo and Paturi (above) | known conditional hypothesis (open) | search result |

## Circuit axes (size, depth, fan-out, NOT gates, monotone vs general)

| Entry | Statement | Source | Status | Read |
|---|---|---|---|---|
| NOT gates (Markov) | ⌈log₂(d(f)+1)⌉ NOT gates are necessary and sufficient for a circuit of f (d(f) = decrease count of a chain); about log n NOT gates suffice. | Markov, JACM 5 (1958) 331-334 | proved | from memory, TXT via Jukna Thm 10.5 per LITERATURE.md §C |
| NOT gates (Fischer) | ⌈log₂(n+1)⌉ NOT gates suffice with a polynomial size blow-up. | Fischer, LNCS 33 (1975) | proved | from memory, TXT via Jukna Thm 10.18 per LITERATURE.md §C |
| Monotone vs general | Exponential monotone lower bound for CLIQUE. | Razborov, Dokl. Akad. Nauk SSSR 281 (1985) | proved | from memory |
| Tardos's gap | A monotone function in P whose monotone circuit complexity is exponential, so monotone and general circuit size differ exponentially for it. | Tardos, Combinatorica 8 (1988) 141-142 | proved | from memory |

## This repository's points on the circuit axes

None of these bears on P vs NP. Each is a finite or restricted circuit statement.

- **One NOT gate.** Reduction of the one-NOT question for (1,1)-disjoint Boolean sums to the open lemma **BottomPay** (a Hall condition on bottom forests of DD sets). Files: `one-not/lean/PEqualNP/W951/Open/` (`LightAbsorb.lean`, `DDAbsorb.lean`, `MixedStepNegIff.lean`, `MixedCount.lean`; `no_minCE` and the general one-NOT theorem are NOT proved). Status: open. See BOARD.md CURRENT STATE.
- **Several NOT gates.** Proved for any number of NOT gates: OR of n inputs needs n−1 gates (`Or4ManyNot.lean`), OR systems need n − comp (`OrSystemManyNot.lean`), plus `FlipLemma.lean`, `FlipHall.lean`, `PointLemma.lean` (ingredients). Open: the point lemma for two sets. Same directory.
- **Markov-Fischer bound.** Fischer's ⌈log₂(n+1)⌉ NOT-gate construction with polynomial blow-up, checked in Lean: `lean/PEqualNP/General/FischerMain.lean` (also `Fischer.L104`, `Fischer.stage1`). It re-proves a known 1958/1975 result. Status: proved (known).
- **f_G row.** For the edge function f_G of a graph G, |E| + τ − 1 ≤ C(f_G) is checked on restricted classes (W6, W4 with maximum degree 3: `EdgeFnWindow.lean`, `EdgeFnWindow4.lean`) and equality for C4-free graphs is a conjecture the project says it cannot prove; it is likely false for dense C4-free graphs. Files: `workshop/notes/note-3-big-picture.md`, `workshop/notes/note-1-edge-function-exact-size.md`, `boards/ladder.md` (density barrier note).
- **L6 rows.** Two different things carry the name. (a) L6 time average: `lean/PEqualNP/QuantumGravity/Helpers/FixedPoint.lean` and `Telescope.lean` (a Cesàro identity, same telescoping sum as L5; a physics-side premise, not a circuit size bound). (b) L6 MONO lemma in `workshop/notes/general/generalize-open-case.md`, a hand proof marked UNVERIFIED. I did not find "depth and size rows" for L6 in the README or boards; if the board means other rows, point me to them. Status: (a) checked identity, (b) unverified.
