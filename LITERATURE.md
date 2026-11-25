# Literature: one index of everything the project has read

Owner, 2026-11-24: "preexisting lit is literally the most important thing here. dont drop, just
organize." This file organizes; it drops nothing. Every entry points to the note that holds the
full reading. Literature notes are never marked `OFF THE ROUTE` and never deleted.

**Read status** (kept from the source notes): **TXT** = statement read in the paper's text;
**ABS** = abstract only; **TLDR** = machine summary only; **MEM** = standard result from memory,
not re-read; **CITED** = seen only as a citation in another source. A status below TXT is a
reason to re-read before relying on the entry.

**Headline.** Problem 951 (one NOT gate saves nothing on (1,1)-disjoint Boolean sums) appears to
be new. A forward-citation crawl of 28 seed papers (255 citing works) finds no one-NOT bound for
Boolean sums; Jukna and Sergeev 2013 §7 and Blum 2024 (ECCC TR24-179) list the question as open.

## A. Boolean sums in monotone circuits (rung 0: the base value Σ(|S| − 1))

| Source | What it gives | Status | Note |
|---|---|---|---|
| Wegener, *The Complexity of Boolean Functions* (1987), §6.6: Def. 6.1, Lemma 6.1, Thm 6.2, Cor. 6.1, 6.2 | optimal monotone circuits for (1,1)-disjoint sums are OR-only, value exactly Σ(\|S\| − 1); proof replaces the LAST AND gate; "(6.7) essential that f_j is a Boolean sum" | TXT | `research-and-replacement`, `tractability-lit`, `research-hall-charging-lit` |
| Mehlhorn, "Some remarks on Boolean sums", Acta Inf. 12 (1979); Galil and Mehlhorn, Computing 16 (1976) | exact monotone base; replacement rules | CITED (not opened) | `research-lit`, `research-hall-charging-lit` |
| Nechiporuk (1969) | Boolean sums Ω(n^{3/2}); Thm 3.9 counts wires | CITED | `research-lit` |
| Pippenger, "On another Boolean matrix", TCS 11 (1980) 49-56, Lemma 1, Lemma 4 | charging of demands to eligible edges on a-to-b paths, load ≤ t²; AND-gate elimination. Best printed charging template (cone restriction + bounded load) | TXT (opened in full) | `research-hall-charging-lit`, `research-heredity-lit` |
| Jukna, *Boolean Function Complexity* (2012) §13.6, draft Thm 13.21, 13.27 | restates Pippenger; C_{∧,∨}(f_A) = Ω(\|A\|/k³) | partly read; printed numbering unverified | `research-hall-charging-lit` |
| Jukna and Sergeev, "Complexity of Linear Boolean Operators", FnTTCS 2013, Thm 3.9, §7 | 2-free A ⇒ OR(A) = \|A\| (wires); §7 ASKS whether AND/OR/NOT circuits help for Boolean sums. Its printed construction "y_i ∧ ¬h" is wrong as written: do not cite that gap | TXT | `tractability-lit` |
| Tarjan 1978 | AND helps for non-(1,1)-disjoint sums (17 < 18) | CITED | `research-lit` |
| Tsukiji, "On a small class of Boolean sums", TCS 163 (1996) 283-289 | a class of n-output sums with monotone complexity n² / 2^{O((log log n)²)} | TLDR | `research-crawl` |
| Weiß, Inf. Control 59 (1983), via Wegener §6.7 Thm 7.1 | bottleneck argument: first OR gates on paths from x_1 all die under x_1 := 0, size by pigeonhole | TXT (in Wegener) | `research-charging` |

## B. The weight ≤ 1 barrier (set circuits, slices)

A proof of 951 must use inputs of weight ≥ 2.

| Source | What it gives | Status | Note |
|---|---|---|---|
| Wegener 1987 pp. 207-214, §6.13-6.15 | set circuits / 1-slices; p. 213 open question SC(H_1..H_n) = Σ(\|H_i\| − 1)? | TXT | `research-lit`, `tractability-lit` |
| Hiltgen and Paterson, Comput. Complexity 5 (1995) 132-154 | the Nechiporuk 1-slice has a 3n + o(n) circuit; savings whenever SC ≥ 3n + 2m. Answers Wegener's question negatively; quantifies the barrier | TLDR / abstract (full text not reached) | `research-crawl`, `research-relax` |
| Tsukiji, RIMS Kokyuroku 906 (1995) 81-88, hdl:2433/59458 | set circuits with {∪, ∩, ¬} for 1-slices of Boolean sums: SC = C + Θ(n) | TXT | `research-lit` |
| Berkowitz 1982; Valiant, SIAM J. Comput. 15 (1986) | for slice functions, monotone ≤ c · general + O(n log² n) | ABS | `notes/general/research-lit-unrestricted` |
| project result (research Fable W) | weight ≤ k is not enough at scale for any fixed k (AG(2,25) construction, tested) | project | `research-fable-weight` |

## C. Circuits with few NOT gates (the ladder)

| Source | What it gives | Status | Note |
|---|---|---|---|
| Markov, JACM 5 (1958) 331-334 | ⌈log₂(d(f)+1)⌉ NOT gates are necessary and sufficient | TXT via Jukna BFC Thm 10.5 | `research-lit-unrestricted`; in Lean: L-gen-104 line |
| Fischer 1975 (LNCS 33) | ⌈log(n+1)⌉ NOT gates with polynomial overhead | TXT via Jukna Thm 10.18 | checked in Lean: `Fischer.L104`, `Fischer.stage1` |
| Amano and Maruoka, RIMS Kokyuroku 1041 (1998) 71-78, hdl:2433/62069 (= SICOMP 2005) | Thm 2: size_t(f) ≥ min over families of 2^{t+1} − 1 monotone functions covering the sensitivity graph; Fact 3 (h / C0 / C1 edge cover) = the project's two-world split | TXT (1998 version) | `research-lit` |
| Blais, Canonne, Oliveira, Servedio, Tan, arXiv 1410.8420 | t NOT gates ⇒ f = PARITY of O(2^t) monotone functions; influence O(2^t √n). Function-level: gives no gate count for 951 | TXT | `research-negation-influence` |
| Morizumi, Tarui, Iwama, RIMS Kokyuroku 1554 (2007) 131-138 | parity with few NOTs; white / black gates; accounting loses exactly 1 gate per NOT | TXT | `tractability-lit` |
| Jukna and Lingas, ECCC TR18-154 (JCSS 2022), Thm 1 | negation width w: size ≥ monotone size / K − 1 (multiplicative loss) | TXT | `tractability-lit` |
| Sung and Tanaka, RIMS 992 (1997); IPL 2002 | removing one NOT can cost exponentially (Fischer's question) | ABS | `research-lit` |
| Rossman, CCC 2015 | correlation bounds against monotone NC1, ~(1/2) log n NOTs; asymptotic | CITED | `research-lit` |
| Blum 2009; Blum arXiv 1708.03486; Blum 2024, ECCC TR24-179 | why monotone techniques do not extend to negations; TR24-179 proposes (1,1)-disjoint sums with negations as an OPEN target | TLDR / TXT (1708.03486) | `research-lit`, `tractability-lit` |
| Kochergin and Mikhailovich (2019, 2024, 2025) | exact complexity counting negations only (monotone gates free): not 951's measure | ABS | `research-crawl` |
| Korshunov, Russian Math. Surveys 58:5 (2003) | survey; possible place for a Russian one-negation result | NOT read | `research-crawl` |
| Kyoto RIMS repository | source for Japanese negation-limited work; DSpace API recipe | — | `research-lit` |

## D. Monotone circuits for partial functions, games

| Source | What it gives | Status | Note |
|---|---|---|---|
| Sokolov, "Dag-like communication and its applications", ECCC TR16-202, Def. 2.1, 2.3, Thm 3.2 | game size = monotone circuit size, valid for partial functions: exact form of the lifted 951 | TXT | `research-partial`, `research-fable-sokolov`, `coord-lateral`, `front-referee-lateral` |
| Razborov, fusion method (STOC 1989; Jukna BFC §20.3; Karchmer 1993) | extends to partial functions but counts AND gates: wrong measure for Boolean sums | TXT | `research-partial` |
| Wegener 1987 §6.4, §6.5, Exercise 12 | merging function (partial), replacement rules | TXT | `research-partial` |
| Karchmer, Kushilevitz, Nisan, SIAM J. Discrete Math. 8 (1995) | fractional covers; LP lower bounds by dual solutions | ABS | `research-charging` |
| Chistikov, Iván, Lubiw, Shallit, STACS 2017 | fractional rectangle coverings bound depth-2 OR circuits | ABS | `research-crawl` |

## E. Hall, matroids, transversals (the counting step)

| Source | What it gives | Status | Note |
|---|---|---|---|
| Halmos and Vaughan (1950); Ore (1955) | Hall by minimal counterexample; deficiency form | MEM | `research-heredity-lit` |
| Edmonds 1965, 1970; Nash-Williams 1966; Schrijver ch. 42 | matroid union / partition min-max; integrality. Caveat (tested): merge-set families are NOT matroid basis families (exchange fails on 18 of 26) | MEM | `research-nominCE-lit`, `research-charging` |
| Lorea 1975; Frank, Király, Kriesell, Discrete Appl. Math. 131 (2003) | hypergraphic matroid | MEM | `research-nominCE-lit` |
| Aharoni and Haxell, J. Graph Theory 35 (2000); Haxell 1995, 2001 | Hall for hypergraphs; independent transversals when classes have ≥ 2Δ vertices; alternating-tree argument. Numeric conditions fail on 25 of 26 instances | MEM | `research-hypergraph-hall` |
| Aharoni's topological Hall; Meshulam; Aharoni, Berger, Meshulam | η(H\|Q) ≥ \|Q\| ⇒ independent transversal: the right strength, needs structure-specific bounds | TXT via Boehmer-Huang | `research-hypergraph-hall` |
| Boehmer and Huang, arXiv 2611.15392; Haxell and Szabó, Combinatorica 45 (2025); Asadpour, Feige, Saberi | Santa Claus = MergeSDR's setting; MergeFrac is their configuration LP; constant-factor gap, no exact statement | TXT (§1-2) | `research-hypergraph-hall` |
| Aspvall, Plass, Tarjan 1979 | 2-SAT cycle certificate for the world choice | MEM | `research-hypergraph-hall` |
| In Lean already | Mathlib Hall; `rado_aux` (Rado for linear matroids, `Gct/Helpers/RadoLinear.lean`); Hall b-matching + LP duality (tractability). Not in Mathlib: König-Egerváry, Menger, matroid union, finite Farkas | read in the repo | `research-nominCE-lit`, `research-lit` |

## F. Gate elimination and explicit bounds for general circuits

| Source | What it gives | Status | Note |
|---|---|---|---|
| Li and Yang, STOC 2022 (ECCC TR21-023) | 3.1n − o(n) for affine dispersers, all binary gates | TXT | `research-lit-unrestricted`, `one-not/tools/research951/charging/gate_elim_extract.md` |
| Find, Golovnev, Hirsch, Kulikov, FOCS 2016 | (3 + 1/86)n − o(n) | TXT | `research-lit-unrestricted` |
| Iwama and Morizumi, MFCS 2002; Lachish and Raz, STOC 2001; Zwick 1991 | 5n − o(n), 4.5n, 4n in the De Morgan basis (NOT gates free) | TLDR / MEM | `research-lit-unrestricted`, `research-charging` |
| Schnorr 1974; Red'kin 1973; Kombarov 2011 | XOR_n: 3(n − 1) with NOT free; 4(n − 1) with NOT counted; optimal circuits are trees of XOR_2 blocks | secondhand; primary sources unverified | `notes/general/generalize-ladder-survey` |
| Carmosino, Dang, Jackman, arXiv 2511.16903 and 2602.17942 | simple extensions, Red'kin measure, convergent gate elimination (Thm 18, Thm 37): closest to the XOR extension open case | partly read | `generalize-ladder-survey`, `research-hall-charging-lit`, board wall "XOR extension" |
| Golovnev, Hirsch, Knop, Kulikov, ECCC TR16-119 | limits of gate elimination | TXT | `research-lit-unrestricted` |
| Kulikov, Pechenev, Slezkin, MFCS 2022 | SAT-based local improvement; exact synthesis feasible for small sizes | ABS | `generalize-ladder-survey` |

## G. Fixed-degree bounds, range avoidance, magnification, meta-complexity

All in `notes/general/research-lit-unrestricted.md`.

- Kannan 1982 (Σ2P ∩ Π2P ⊄ SIZE(n^k); MEM, full text not reached; circuit half checked in Lean:
  `SizeHierarchy.size_hierarchy`); Cai 2007; Vinodchandran 2005; Santhanam 2007.
- Korten FOCS 2021; Chen, Hirahara, Ren STOC 2024; Li STOC 2024 (near-maximum bounds).
- Williams JACM 2014; Murray and Williams STOC 2018 (algorithms imply lower bounds).
- Oliveira and Santhanam FOCS 2018; McKay, Murray, Williams STOC 2019; Chen et al. ITCS 2020
  (hardness magnification and the locality barrier).
- Hirahara FOCS 2018; Liu and Pass FOCS 2020 (meta-complexity).

## H. The problem statement and the barriers

| Source | What it gives | Status | Note |
|---|---|---|---|
| Cook, "The P versus NP Problem" (Clay official description) | the official statement; compared line by line with `Defs/Base.lean`; Propositions 2, 3 | TXT (verbatim quotes) | `notes/general/clay-official-statement.md`, `research-pnp-defs` |
| Baker, Gill, Solovay 1975 | relativization | checked rows L-lib-061 / 062 | `notes/checker/note-2-physics-models-and-the-three-barriers.md` |
| Aaronson and Wigderson 2009 | algebrization | checked rows L-lib-065 / 076 | same |
| Razborov and Rudich 1997 | natural proofs | checked row L-lib-086 | same |
| Razborov 1987; Smolensky 1987 | polynomial method: depth-restricted only, no exact gate counts | MEM | `research-negation-influence` |

## I. Quantum gravity and complexity

The full reference list of the quantum gravity program, kept here so that no cut of a README can drop it. The map from physics models to the three barriers is in
`notes/checker/note-2-physics-models-and-the-three-barriers.md`.

- J. D. Bekenstein, Universal upper bound on the entropy-to-energy ratio for bounded systems,
  Phys. Rev. D 23 (1981) 287.
- K. Kraus, States, Effects, and Operations, Lecture Notes in Physics 190, Springer (1983).
- D. Deutsch, Quantum mechanics near closed timelike lines, Phys. Rev. D 44 (1991) 3197.
- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator,
  J. A. Smolin, H. Weinfurter, Elementary gates for quantum computation, Phys. Rev. A 52 (1995)
  3457, arXiv:quant-ph/9503016.
- E. Knill, Approximation by quantum circuits, LANL report LAUR-95-2225 (1995),
  arXiv:quant-ph/9508006. (L-qg-115, 116, 119: Lemma 4.3, Theorem 4.1 / Corollary 4.2, Theorem 3.4.)
- E. Bernstein, U. Vazirani, Quantum complexity theory, SIAM J. Comput. 26 (1997) 1411.
- S. J. Szarek, Metric entropy of homogeneous spaces, Banach Center Publ. 43 (1998),
  arXiv:math/9701213. (L-qg-115: Theorem 7.)
- N. Margolus, L. B. Levitin, The maximum speed of dynamical evolution, Physica D 120 (1998) 188.
- S. Lloyd, Ultimate physical limits to computation, Nature 406 (2000) 1047.
- M. A. Nielsen, I. L. Chuang, Quantum computation and quantum information, Cambridge University
  Press (2000), Section 4.5.
- R. Bousso, The holographic principle, Rev. Mod. Phys. 74 (2002) 825, arXiv:hep-th/0203101.
- T. A. Brun, Computers with closed timelike curves can solve hard problems efficiently, Found.
  Phys. Lett. 16 (2003) 245, arXiv:gr-qc/0209061.
- S. Aaronson, NP-complete problems and physical reality, SIGACT News 36 (2005),
  arXiv:quant-ph/0502072.
- C. M. Dawson, M. A. Nielsen, The Solovay-Kitaev algorithm, Quantum Inf. Comput. 6 (2006) 81,
  arXiv:quant-ph/0505030.
- M. A. Nielsen, A geometric approach to quantum circuit lower bounds, Quantum Inf. Comput. 6
  (2006) 213, arXiv:quant-ph/0502070.
- S. Aaronson, J. Watrous, Closed timelike curves make quantum and classical computing
  equivalent, Proc. R. Soc. A 465 (2009) 631, arXiv:0808.2669.
- D. Harlow, P. Hayden, Quantum computation vs. firewalls, JHEP 06 (2013) 085, arXiv:1301.4504.
- D. Stanford, L. Susskind, Complexity and shock wave geometries, Phys. Rev. D 90 (2014) 126007,
  arXiv:1406.2678.
- L. Susskind, Computational complexity and black hole horizons, Fortsch. Phys. 64 (2016) 24,
  arXiv:1402.5674.
- F. Pastawski, B. Yoshida, D. Harlow, J. Preskill, Holographic quantum error-correcting codes:
  toy models for the bulk/boundary correspondence, JHEP 06 (2015) 149, arXiv:1503.06237.
- A. R. Brown, D. A. Roberts, L. Susskind, B. Swingle, Y. Zhao, Holographic complexity equals
  bulk action?, Phys. Rev. Lett. 116 (2016) 191301, arXiv:1509.07876.
- S. Aaronson, The complexity of quantum states and transformations: from quantum money to black
  holes, lecture notes (2016), arXiv:1607.05256.
- A. R. Brown, L. Susskind, Second law of quantum complexity, Phys. Rev. D 97 (2018) 086015,
  arXiv:1701.01107.
- Z. Ji, Y.-K. Liu, F. Song, Pseudorandom quantum states, CRYPTO 2018, arXiv:1711.00385.
- A. R. Brown, H. Gharibyan, G. Penington, L. Susskind, The Python's lunch: geometric obstructions
  to decoding Hawking radiation, JHEP 08 (2020) 121, arXiv:1912.00228.
- A. Bouland, B. Fefferman, U. Vazirani, Computational pseudorandomness, the wormhole growth
  paradox, and constraints on the AdS/CFT duality, ITCS 2020, arXiv:1910.14646.
- W. Kretschmer, Quantum pseudorandomness and classical complexity, TQC 2021, arXiv:2103.09320.
- J. Haferkamp, P. Faist, N. B. T. Kothakonda, J. Eisert, N. Yunger Halpern, Linear growth of
  quantum circuit complexity, Nature Physics 18 (2022) 528, arXiv:2106.05305.
- Z. Brakerski, Black-hole radiation decoding is quantum cryptography, CRYPTO 2023,
  arXiv:2211.05491.

### Frontier survey (task qg-frontier, seat Q1, 2026-11-25)

Ranking of the next formal targets: `lean/PEqualNP/QuantumGravity/FRONTIER.md`. Status as above; "search result" = seen only as a search hit.

| Source | What it gives | Status | Note |
|---|---|---|---|
| Susskind 2014 (arXiv:1402.5674); Stanford and Susskind 2014 (arXiv:1406.2678) | complexity = volume: the volume of the Einstein-Rosen bridge tracks the circuit complexity of the boundary state, growing linearly for exponential time | MEM | physics premise only; no Lean statement in the repo mentions volume (README, track A) |
| Brown, Roberts, Susskind, Swingle, Zhao 2016 (arXiv:1509.07876, PRL 116 191301) | complexity = action: complexity is the action of the Wheeler-DeWitt patch; late-time growth 2M/πħ, compared with the Lloyd bound | MEM | physics premise; the Lloyd bound side is track E (L-qg-010) |
| Belin, Myers, Ruan, Sárosi, Speranza, "Does complexity equal anything?" (2022, arXiv:2111.02429) | an infinite family of gravitational observables with the same late-time linear growth, so "volume" and "action" are not singled out | MEM (not opened) | weakens any claim that one bulk quantity *is* circuit complexity |
| Brown and Susskind, "Second law of quantum complexity" (arXiv:1701.01107, PRD 97 086015) | complexity of K qubits ~ positional entropy of a classical system with 2^K degrees of freedom; expected complexity grows like entropy; "uncomplexity" is a resource; conjecture of linear growth until exponential saturation | ABS (abstract opened 2026-11-25) | the counting side (most unitaries have exponential complexity) is checked: L-qg-115/116/118 and `L119_weak` |
| Haferkamp, Faist, Kothakonda, Eisert, Yunger Halpern, Nature Physics 18 (2022) 528 (arXiv:2106.05305) | Thm 1: for T blocks of ≤ L Haar-random 2-qubit gates each containing a backwards light cone, exact complexity C_u(U) ≥ R/(9L) − n/3 with probability 1 until T ≥ 4^n − 1. Upper bound d_A ≤ 9R + 3n by parameter counting (eq. 3); Prop. 1 d_{A_T} ≥ T via a Clifford point of high Jacobian rank; Lemma 1: the low-rank locus of the contraction map is algebraic of measure 0 (Tarski-Seidenberg, real algebraic dimension theory); then constant-rank theorem + compactness. Their complexity does NOT lower-bound Nielsen's | TXT (main text: Thm 1, Prop. 1, Lemma 1, proof sketch; supplementary appendices A-B not read) | the upper half (9R + 3n) is exactly `KnillParametrization` / `L119_weak` (16k); the lower half needs real algebraic geometry and the constant-rank theorem, neither in Mathlib |
| Haferkamp, "On the moments of random quantum circuits and robust quantum complexity" (arXiv:2303.16944) | approximate complexity: linear growth Ω(d/poly n) for d ≤ 2^{n/2} at error Θ(2^{-n}); only Ω(√d/poly n) at constant error | search result, NOT read | the robust (approximate) linear growth is still open at constant error |
| Chen, Haah, Haferkamp, Liu, Metger, Tan, "Incompressibility and spectral gaps of random circuits" (arXiv:2406.07478) | spectral gap Ω(n^{-3}) of random reversible circuits for all t, and random quantum circuits for t ≤ Θ(2^{n/2}); O(n⁴t)-gate reversible circuits are t-wise independent | search result, NOT read | design-based route to robust complexity growth |
| Schuster, Haferkamp, Huang, "Random unitaries in extremely low depth" (arXiv:2407.07754, Science 2025 per Caltech record) | approximate unitary designs in depth log n on any geometry; PRUs in poly log n depth in 1D | search result, NOT read | |
| Ma and Huang, "How to construct random unitaries" (arXiv:2410.10116, STOC 2025) | pseudorandom unitaries exist if quantum-secure one-way functions exist (also against inverse queries) | ABS (abstract opened 2026-11-25) | bears on Bouland-Fefferman-Vazirani's wormhole-growth paradox (track C) |
| Liu, Tian, Wu, "Structure-fair quantum circuit complexity" (arXiv:2509.18205) | claims a linear-plus-log lower bound for a modified complexity notion | search result, NOT read; not peer reviewed | do not rely on it |
| Pastawski, Yoshida, Harlow, Preskill 2015 (HaPPY, arXiv:1503.06237) | perfect tensors (6-qubit, from the [[5,1,3]] code) tiled on a hyperbolic lattice give isometric bulk-to-boundary codes; Ryu-Takayanagi for these states | MEM | the stabilizer core is CHECKED: L-qg-140 to 149 (five-qubit code distance 3, six-qubit perfect state, every 3-set determines the stabilizer); README track F row "none yet" is stale |
| Aaronson and Watrous 2009 (arXiv:0808.2669) | P_CTC = BQP_CTC = PSPACE: a fixed point of any (non-unitary) quantum circuit can be implicitly computed in polynomial space | ABS (abstract opened 2026-11-25) | repo has P_CTC ⊆ EXP (L-qg-169, `Open/L169.lean`); PSPACE is not defined in the repo |
| Nielsen 2006 (arXiv:quant-ph/0502070); Nielsen, Dowling, Gu, Doherty, Science 311 (2006) 1133 | geometric complexity: gate count is bounded by a polynomial in the geodesic distance for a right-invariant Finsler/Riemannian penalty metric on SU(2^n) | MEM | needs Riemannian geometry on Lie groups; not reachable in current Mathlib (track G) |
| Search, 2026-11-25 (one web search) | no 2025-2026 proof found of linear growth of APPROXIMATE complexity at constant error for random circuits | absence of a hit is not evidence of absence | |

### The generalization question (README C4): do AND and NOT gates help for Boolean sums?

| Source | What it gives | Status |
|---|---|---|
| Nechiporuk 1969; Wegener 1987 Thm 6.2; Mehlhorn 1979; Pippenger 1980 | AND gates do not help for (1,1)-disjoint sums in MONOTONE circuits; at most a factor max{h−1, k−1} for (h,k)-disjoint | TXT (Wegener, Pippenger), CITED (others) |
| Jukna and Sergeev 2013 §7 | ASKS whether general circuits help for Boolean sums (OR against GEN): an open question, not a stated conjecture | TXT |
| Blum, ECCC TR24-179 | proposes (1,1)-disjoint Boolean sums with negations as an open target | TXT (outlook) |
| Find, Göös, Järvisalo, Kaski, Koivisto, Korhonen, "Separating OR, SUM, and XOR circuits", arXiv 1304.0513v2 (Thm 1: Gap_{+/∨} = Ω(n^{1/2}/log²n); Cor 3: Gap_{∨/⊕}, Gap_{+/⊕} = Ω(n/log²n); Thm 5 Mehlhorn-Pippenger: (s,t)-free ⇒ C∨ ≥ \|A\|/(st)) | OR / SUM / XOR circuits only (no AND, no NOT). Thm 1: Gap_{+/∨}(n) = Ω(n^{1/2}/log² n); Cor 3: Gap_{∨/⊕} = Ω(n/log² n) (k-uniform matrices, XOR beats OR); §1: C_∨(A) ≤ C_+(A) for every A; Thm 5 (Mehlhorn-Pippenger): (s,t)-free A gives C_∨(A) ≥ \|A\|/(st). §1.1 conjecture: every non-trivial gap between the three models is n^{1−o(1)}. NOTHING on rectangle-free ((1,1)-disjoint) matrices against cancelling or general circuits; not a C4 statement ADDED (research-desktop): linear circuits only (OR / SUM / XOR, wires, no AND, no NOT, no depth restriction). XOR circuits (non-monotone, cancellation) beat OR by n/log²n on dense k-uniform matrices (not on sparse (1,1)-free ones). States conjectures only about gaps between the three linear models (all non-trivial gaps n^{1-o(1)}); no conjecture or refutation of C4. Weaker model than AND/OR/NOT | TXT (§1 to §3.3 via arXiv HTML; §4, §5 not read); TXT (`research-literature-c4`) |
| Boyar and Find, "Cancellation-free circuits in unbounded and bounded depth", arXiv 1305.3041v2 (Lemma 1 = Nechiporuk-Mehlhorn-Pippenger-Wegener: k-free A ⇒ C∨ ∈ Ω(\|A\|/k²); Thm 4: λ(n)=max C∨/C⊕ ∈ Ω(n/log²n), also constant depth ≥ 2; Sect. 6-7: Sierpinski matrix, OR and cancellation-free ≥ ½ n log n) | Prop 1: C_∨(A) ≤ C_CF(A); Thm 4: max_A C_∨(A)/C_⊕(A) = Ω(n/log² n), so cancellation (XOR) can help by almost a factor n; Lemma 1 (Nechiporuk, Mehlhorn, Pippenger, Wegener): k-free A gives C_∨(A) = Ω(\|A\|/k²); Sierpinski matrix exactly (1/2) n log n. The separating matrices come from Ramsey-type random graphs, not shown rectangle-free; no statement on whether cancellation or AND / NOT helps for rectangle-free matrices; not a C4 statement ADDED (research-desktop): linear XOR / cancellation-free / OR circuits only; no AND, no NOT. XOR cancellation beats OR on a dense random-product matrix (A = BC). Open problem in Sect. 7 is whether cancellation helps for the Sierpinski matrix, not C4. No conjecture or refutation of C4 | TXT (§1 to §3 via arXiv HTML; §4 to §7 not read); TXT (`research-literature-c4`) |
| Cavalar, Fabris, Mukhopadhyay, Srinivasan, Yehudayoff, "Negations are powerful even in small depth", arXiv 2512.19515v1 (Thm 1.1: ΣΠΣ size O(n³) polynomial, monotone arithmetic ≥ 2^{Ω(n)}; Thm 1.2 constant degree; Thm 1.5: monotone Boolean f in uniform NC², monotone size 2^{n^{1/3-o(1)}}, only the abstract, Sect. 1 and 1.3 read; proofs of Sect. 2-5 not read) | Thm 1.1: an expander polynomial with a ΣΠΣ circuit of size O(n³) (one subtraction of two monotone depth-3 circuits) needs monotone arithmetic size 2^{Ω(n)}; Thm 1.5: a monotone Boolean f in uniform NC² needing monotone size 2^{n^{1/3−o(1)}}. Separating functions are NOT Boolean sums; no theorem for Boolean circuits with exactly one NOT gate; nothing on Boolean sums. Caution for C4 stays: one negation (subtraction) helps hugely for other functions ADDED (research-desktop): functions: spanning-tree-like polynomial from expander graph, unique/different-from-1 disjointness, matroid / rank functions; NOT Boolean sums. Negation or subtraction, depth 3 arithmetic, depth O(log² n) Boolean. Its open problems (Sect. 1.3) are about monotone rank programs, planar matching, constant-depth separations: nothing on Boolean sums or C4. A caution only: negations can be exponentially powerful for other functions; the paper says nothing about sums | TXT (§1, §2, part of §3 via arXiv HTML; §4, §5 not read); PART (`research-literature-c4`) |
| Tsukiji, "Circuit Complexity of An Explicitly Defined First Slice Function", RIMS Kokyuroku 906 (1995) 81-88, file 0906-11.pdf, hdl:2433/59458 = SAME paper as row 38 (confirmed from repository metadata). Introduction, p. 81: constant-slice functions have C_{∨,∧}(f) = Θ(C_{∨,∧,¬}(f)), but "this relation, generally, does not hold for a Boolean sum" (the example after "e.g." is garbled in the text extraction; not read) | = Tsukiji, RIMS Kokyuroku 906 (1995) 81-88, hdl:2433/59458, row above (set circuits for 1-slices of Boolean sums: SC = C + Θ(n)); the 'does not hold for a Boolean sum' remark is about slices, not a C4 conjecture ADDED (research-desktop): an unsupported remark, no proof, no citation for it: a Boolean sum can have nonlinear monotone lower bounds ([6], [5,7] = (s,t)-disjointness), and the remark suggests nothing about a non-monotone upper bound. It is not a statement of C4 and not a refutation of it. Adds nothing to row 38 except this quote | TXT (read earlier, `research-lit`); TXT (intro re-read; same paper as row 38) (`research-literature-c4`) |
| Two web searches, 2026-11-24 | no paper found that states C4 as a conjecture or proves or refutes it | absence of a hit is not evidence of absence |
| Result of task literature-c4 (research, 2026-11-24) | none of the three arXiv papers nor the Kyoto paper states C4 as a conjecture or proves or refutes it; the nearest printed items stay Jukna and Sergeev 2013 §7 (open question) and Blum TR24-179 (open target). The XOR/OR and SUM/OR separations are in other bases (no AND / NOT) and for non-rectangle-free matrices | TXT |
| Jukna, "On the minimum number of negations leading to super-polynomial savings", Inform. Process. Lett. 89 (2004) 71-74 (preprint ECCC TR01-058) | explicit monotone multi-output functions in P need superpolynomial size with at most log n − O(log log n) NOT gates: strong bounds are provable almost up to the Markov rung, by monotone methods, for SOME functions (not Boolean sums). Used in `notes/beyond-one-not.md` (S4, Barriers) | ABS (abstract on the author's page, seen through one web search result; paper NOT read) (`beyond-one-not`) |
| Beals, Nishino, Tanaka, "On the complexity of negation-limited Boolean networks", SIAM J. Comput. 27 (1998) 1334-1347; Morizumi and Suzuki (IEICE Trans. E93-D, 2010) | inverter of size O(n log n), depth O(log n), with ⌈log(n+1)⌉ NOT gates; later a linear-size inverter with log^{1+o(1)} n NOT gates. Gives: rung ⌈log₂(n+1)⌉ equals all circuits up to a factor 2 and an additive O(n log n), so on dense designs (`base` ≈ n^{3/2}) that rung is a superlinear statement about all circuits (S4) | search result NOT read (one web search; the formula 2·size + O(n log n) is the standard reading of the inverter, not confirmed from the paper) (`beyond-one-not`) |
| Result of task beyond-one-not (research agent of main, 2026-11-24; three web searches) | no printed statement of `BoolSumNot t` for t = 2, of an additive savings bound f(t) for Boolean sums, or of a t-world certificate game. The printed accountings for t NOT gates lose 1 gate per NOT (Morizumi, Tarui, Iwama: parity) or a factor about 2^t (Amano and Maruoka; Blais et al.; Jukna and Lingas); a factor 2^t is superlinear on designs only for t < ½ log₂ n | absence of a hit is not evidence of absence |

### Sums over paths (for README §6)

| Source | What it gives | Status |
|---|---|---|
| Adleman, DeMarrais, Huang, "Quantum computability", SIAM J. Comput. 26 (1997) | the acceptance probability of a quantum computation is a sum over computation paths; BQP ⊆ PP | MEM |
| Feynman 1948; Feynman and Hibbs 1965 | the path integral as a limit of sums over discretized histories | MEM |
| Markov-Kakutani fixed point theorem | fixed points of commuting affine maps by averaging; the Cesàro proof in `Helpers/FixedPoint.lean` is the one-map case | MEM; the one-map case is checked |
| Lutz, resource-bounded measure (1992) | martingales on Cantor space; "NP is not p-measure zero" is a hypothesis stronger than P ≠ NP | MEM |

### Mapping the continuous form to the discrete count (task continuous-mapping)

Notation: slack(Q) as in `one-not/tools/search/core.py`; F = multilinear extension (F(x) = E[slack(Q)], point v in Q with probability x_v), Φ(p) = F(p,...,p). Status vocabulary as above; "search result, NOT read" = seen only as a search hit. Note: `one-not/board/agents/sonnet-continuous-lit.md` ranks the ideas; the one-line data tests quoted below were run by the author of this section on the 15 witness circuits with n <= 9 in `one-not/data/witnesses/` (the two twin-tree files and the larger ones are excluded).

| Source | What it gives | Status | Use here |
|---|---|---|---|
| Rossignol, "Threshold for monotone symmetric properties through a logarithmic Sobolev inequality", arXiv math/0511607 (Ann. Probab. 2006), Lemma 2.2 | For ANY real f on {0,1}^n (monotone not needed): d/dp ∫ f dμ_p = Σ_i ∫ ∇_i f dμ_p, ∇_i f = f(x with x_i=1) − f(x with x_i=0). Russo's lemma is the case f = 1_A, A monotone | TXT | USE: this is exactly Φ'(p) = Σ_v E[slack(Q+v) − slack(Q)], no monotonicity needed. It gives the derivative only; it does not by itself give a sign at p = 0 (slack is not monotone) |
| Margulis 1974; Russo, Z. Wahrsch. 61 (1982); Talagrand, Ann. Probab. 22 (1994) "On Russo's approximate zero-one law" | the origin of the formula and its sharp-threshold use | CITED (in Rossignol) | NO USE: sharp-threshold results bound the width of the transition of a monotone event; our Φ is a signed integer-valued function with a zero at p = 1, not an event probability |
| Friedgut and Kalai, "Every monotone graph property has a sharp threshold", Proc. AMS 124 (1996); Kalai and Safra, "Threshold phenomena and influences" | Russo + KKL (BKKKL): for symmetric monotone A the total influence is large, so μ_p(A) rises steeply | search result, NOT read | NO USE: needs a monotone Boolean event and symmetry; slack is neither |
| Dughmi, "Submodular functions: extensions, distributions, and algorithms. A survey", arXiv 0912.0322 (v4), §3: derivative formula; Prop. 3.17; "up-concave" | ∂F/∂x_i = E[f(S+i) − f(S)]; ∂²F/∂x_i∂x_j = E[f(S+i+j) − f(S+i) − f(S+j) + f(S)], which is <= 0 for all x iff f is submodular, hence F concave along every direction u >= 0 (up-concave); and cross-convex along e_i − e_j (Prop. 3.17, credited to a reference [1]) | TXT | USE as a test criterion: if slack were SUPERmodular then F would be up-CONVEX (mirror image), and convexity of Φ with the tangent at p = 1 would give the corner. Data: slack is supermodular on 2 of 12 tested circuits, neither sub- nor supermodular on 9, modular on 1: so this exact route fails in general. The mixed second derivative is still a computable certificate (idea 2 in the note) |
| Dughmi survey §3, pipage rounding paragraph | Cross-convexity of F lets one move along e_i − e_j without decreasing F, so a fractional point rounds to a vertex with no loss, for matroid polytopes | TXT | USE ONLY IF slack is submodular on the relevant face: then min_x F(x) over a polytope is attained at a vertex; for the plain cube no rounding is needed (F is multilinear, its min over [0,1]^n is already at a vertex), so the content must be a constraint such as |Q| = k |
| Ageev and Sviridenko (2004) pipage rounding; Calinescu, Chekuri, Pál, Vondrák, "Maximizing a monotone submodular function subject to a matroid constraint", SICOMP 40 (2011) 1740-1766 (continuous greedy) | continuous greedy: move x along the best direction; guarantee 1 − 1/e through the up-concavity of F | MEM (not re-opened) | NO USE: a maximization guarantee for a monotone submodular objective; slack is a difference and we need a minimum |
| Chekuri, Vondrák, Zenklusen, "Submodular function maximization via the multilinear relaxation and contention resolution schemes", arXiv 1105.4593 (SICOMP 2014) | rounding a point of the multilinear relaxation with a contention resolution scheme, also for non-monotone f; ties to the correlation gap | ABS | NO USE: loses a constant factor; we need an exact corner, not an approximation |
| Iyer and Bilmes, "Algorithms for approximate minimization of the difference between submodular functions", arXiv 1207.0560 (UAI 2012) | F = G − H with G, H submodular: monotone-decreasing majorise-minimise algorithms; hardness result that no multiplicative approximation exists, additive bounds only | ABS | NO USE for a proof (it is an algorithm, hardness says certifying min >= 0 is a genuine difficulty); USE as the vocabulary: slack = W − base is a DS function (W and base are both decreasing, base is supermodular) |
| Narasimhan and Bilmes, "A submodular-supermodular procedure", arXiv 1207.1404 (UAI 2005) | concave-convex procedure for G − H using modular upper/lower bounds | search result, NOT read | NO USE (algorithm) |
| El Halabi, Orfanides, Hoheisel, "Difference of submodular minimization via DC programming", ICML 2023 (PMLR 202), arXiv 2305.11046, Prop. 2.3 | for a normalized F (F(∅) = 0; submodularity not needed): min_X F(X) = min over [0,1]^d of the Lovász extension f_L; a minimiser x* rounds to a discrete minimiser by thresholding. For F = G − H, f_L = g_L − h_L is a difference of convex functions | TXT (§2, from the fetched HTML, first half only) | USE: it is a clean theorem saying "slack >= 0 at every Q" IFF "Lovász extension >= 0 on the whole cube". The Lovász extension at x is the chain sum Σ_i (x_(i) − x_(i+1)) slack(top-i set), which is exactly the project's L5 chain sum averaged along one chain: a continuous statement on chains. It adds nothing by itself (the equivalence is free), but a SUFFICIENT certificate g_L ≥ h_L (convex ≥ convex) can be searched by LP |
| Bilmes and coauthors, "Discrete and continuous difference of submodular minimization", arXiv 2506.07952 | any normalized F on a finite product domain has a DS decomposition G − H; decompositions are not unique | search result, NOT read | USE (existence only): there is freedom to pick the decomposition, e.g. G = W, H = base, or a decomposition chosen to make G ≥ H easy |
| Murota, *Discrete Convex Analysis* (SIAM 2003); Murota and Shioura; arXiv 1707.09091 "On equivalence of M♮-concavity of a set function and submodularity of its conjugate" | M♮-concave set functions: maximisers are tractable (local = global), exchange axiom; M♮-concave iff conjugate submodular; L♮-convex have Lovász-extension convex closure | search result, NOT read | USE as a testable shape: "slack is M♮-convex, so every local minimum of slack over the cube is global" would give: a descent from ∅ along single-point exchanges reaches the minimum, and slack(N) = 0 is a local minimum. M♮-convexity of slack fails if the one-point step fails (slack is not even monotone), so test the two-point exchange instead |
| Hart and Mas-Colell, "Potential, value, and consistency", Econometrica 57 (1989) 589-614 | a unique function P on games whose marginal contributions P(N) − P(N∖i) are efficient; they give the Shapley value | search result, NOT read | USE: the potential P(S) = Σ_{T ⊆ S} dividend(T)/|T| is a candidate "potential" for slack: efficiency Σ_i (P(N) − P(N∖i)) = slack(N) = 0 is the project's chain sum over uniform random orders (qg-d2 `sum_shapley`). A sign statement needs a game-theoretic property (convexity = supermodular), which slack lacks |
| Harsanyi (1963) dividends = Möbius transform m(T) with slack(Q) = Σ_{T ⊆ Q} m(T); positive games (all dividends >= 0) are convex games; for supermodular v the Lovász extension is concave on the nonnegative orthant (secondary: arXiv 1410.8395, search result NOT read) | In the monomial basis F(x) = Σ_T m(T) Π_{v ∈ T} x_v, so Φ(p) = Σ_T m(T) p^{|T|}, Φ(0) = m(∅) = slack(∅), Φ(1) = Σ_T m(T) = 0 | derivation (the supporting statements are search results, NOT read) | USE as the exact dual picture: the corner Φ(0) = m(∅) is the CONSTANT term; slack(∅) >= 0 means Σ_{T ≠ ∅} m(T) <= 0. Compute m by Möbius inversion and look at the signs of m(T) by |T| |
| Faigle and Grabisch, "A discrete Choquet integral for ordered systems", arXiv 1102.1340 | the Lovász extension equals the Choquet integral of the set function | search result, NOT read | NO NEW USE (same object as above) |
| Harris, "Improved nonnegativity testing in the Bernstein basis via geometric means", arXiv 2309.10675 (2023), §1 | all Bernstein coefficients >= 0 is a sufficient but conservative test for p >= 0 on [0,1] (Bernstein 1915); the paper gives a weaker explicit condition on each coefficient in terms of the geometric mean of its neighbours (cubic case and matrix-valued) | TXT (abstract and intro) | USE: this is the checkable certificate for the Bernstein form of Φ whose coefficients are the level means m_i. Data: on the 15 circuits tested all m_i >= 0 and in fact m_0 >= m_1 >= ... >= m_n = 0 (monotone level means), so the plain test passes and nothing finer is needed there. Test it on the twin trees |
| Bernstein coefficient facts: subdivision / degree elevation (arXiv 2304.11781, 1710.05735, via search snippets) | a polynomial positive on [0,1] has all-positive Bernstein coefficients after enough degree elevation or subdivision; in the simplicial basis some nonnegative polynomials have NO certificate (arXiv 1710.05735) | search result, NOT read | USE (weakly): since Φ is already in Bernstein form of degree n and has all m_i >= 0 on the data, the certificate is not the obstacle; the obstacle is proving m_i >= 0, i.e. the discrete count again |
| Variation diminishing property of the Bernstein basis (standard: sign changes of Σ m_i B_i(p) are at most the sign changes of the sequence (m_i)) | if the level means (m_i) are monotone nonincreasing, Φ' = n Σ (m_{i+1} − m_i) B_{i,n−1} <= 0, so Φ is nonincreasing and Φ(0) >= Φ(1) = 0 | MEM (not re-opened) | USE: the most direct mapping. The property "level means m_0 >= m_1 >= ... >= m_n" is a discrete inequality averaged over levels, weaker than the one-point step, and it held on all 15 circuits tested. The twin-tree files (n > 9) were not tested here: check there first (the board says the one-point step fails on them, which does not contradict monotone level means) |
| Guerra, "Broken replica symmetry bounds in the mean field spin glass model", arXiv cond-mat/0205123, CMP 233 (2003) 1-12; Guerra and Toninelli, CMP 230 (2002) | interpolation: build a one-parameter family Z(t) between a hard system and a solvable one, show d/dt has a sign (after an integration by parts) so the endpoint inequality follows | search result, NOT read | USE as a template, not a theorem: the corner Φ(0) is the hard end, a modular or product surrogate the easy end; the derivative would have to be a sum of squares or a convex-covariance term. The needed ingredient is an explicit "remainder = positive" identity for d/dt of an interpolation of the circuit (e.g. gate by gate), which is unknown |
| Lindeberg replacement; Mossel, O'Donnell, Oleszkiewicz (Ann. Math. 2010); O'Donnell, *Analysis of Boolean Functions*, arXiv 1205.0314 | swap coordinates one at a time: the difference is a telescoping sum of n single-coordinate terms, each controlled by a Taylor expansion | search result, NOT read | USE as the discrete form of idea "L5 chain sum": the project's chain sum IS the Lindeberg telescoping sum over a chain of cubes; the Taylor remainder has no analogue for integer-valued slack, so NO new inequality |
| Bonami 1970, Beckner 1975; Talagrand 1994; Cordero-Erausquin and Ledoux, "Hypercontractive measures, Talagrand's inequality, and influences", arXiv 1105.4533 | semigroup / hypercontractive proofs of KKL and Talagrand's isoperimetric inequality by differentiating along the noise (heat) flow | search result, NOT read | NO USE as stated: they bound L^p norms of a Boolean function from derivatives along a flow; our slack has no norm to bound; the heat flow on the cube IS the p-path (T_ρ f at x = (1−2ρ.. ) is F), so only the framework transfers |
| Pudlák, "Lower bounds for resolution and cutting plane proofs and monotone computations", J. Symbolic Logic 62 (1997) | extends Razborov's approximation method to monotone REAL circuits (gates arbitrary nondecreasing real functions), giving cutting-plane lower bounds via interpolation | search result, NOT read (abstract-level in the hit) | USE as the precedent for relaxing gates to reals; but the relaxation there is monotone, and the project's circuits have NOT gates, so it is the opposite regime (Blum 2024 TR24-179 in section C) |
| Jukna, "Combinatorics of monotone computations", Combinatorica 19 (1999) 65-85, §2 and Thm 2.1 | criterion for circuits whose gates are arbitrary nondecreasing real functions of at most d inputs: if f has a d-local monotone (Boolean OR real) circuit of size l, then for all s, r there are K <= l(dr)^s + 1 s-sets S_0..S_K and L <= l(ds)^r r-sets R_1..R_L such that either every negative input of size >= s contains some S_i, or every positive input of size >= r meets S_0 or contains some R_j. "The arithmetic structure of the reals is not used: any totally ordered domain works" | TXT | NO USE for 951 directly (monotone only, no NOT); USE as evidence that relaxing gate values to an ordered real domain gives no new lower-bound power for monotone circuits |
| Razborov (1985) approximation method; Alon and Boppana (1987); Jukna ch. 9 | the approximation method replaces each gate by an approximator and bounds the error added per gate; sunflower plucking | search result, NOT read | USE as the model of a gate-by-gate potential: "error added per gate" is the discrete derivative along the circuit order, and the final inequality is a sum of per-gate terms, as in L5 |
| Karchmer, Kushilevitz, Nisan, "Fractional covers and communication complexity", SIAM J. Discrete Math. 8 (1995) 76-92 | LP relaxation (fractional cover) characterises amortised nondeterministic communication complexity exactly | search result, NOT read (abstract-level) | NO USE: relaxing a counting measure to a fractional cover is exactly a continuous relaxation, but no theorem transfers; the analogue here is a fractional transversal of the sets S_w, and the base value Σ(|S_w| − 1) is not a covering LP value |
| Golovnev, Hirsch, Knop, Kulikov, "On the limits of gate elimination", MFCS 2016 / JCSS 96 (2018), ECCC TR16-119 | gate elimination with any subadditive measure cannot prove cn above a constant c that depends on the number of substitutions per step | search result, NOT read (abstract-level) | USE as a caution: a potential function built by local substitutions has a built-in ceiling; our measure (witness gates minus base) is a different, global potential |
| Aaronson and Wigderson, "Algebrization: a new barrier in complexity theory", ACM TOCT 1 (2009) / STOC 2008 | arithmetization-based non-relativizing techniques still algebrize, so they cannot separate classes that have algebrizing oracle counterexamples | search result, NOT read | NO USE: our multilinear extension is a finite combinatorial relaxation of one fixed circuit, not an arithmetization of a language; the barrier is not triggered but the technique is not the same either |
| Forman, "Morse theory for cell complexes", Adv. Math. 134 (1998); Chari (2000) acyclic matchings | discrete gradient vector field = acyclic matching on the face poset; paths follow matched pairs, critical cells remain | search result, NOT read | USE as the substitute for a monotone path: slack(Q ∪ v) vs slack(Q) on matched pairs (Q, Q ∪ v) of an acyclic matching of the Boolean lattice; the one-point step fails at SOME pairs, but a matching could choose the pairs where it holds and leave the rest as critical cells. Test: does an acyclic matching with step <= 0 on every matched pair exist, with all critical cells at nonnegative slack? (a small ILP) |
| de Bruijn, Tengbergen, Kruyswijk (1951) symmetric chain decomposition; Tomon, "Decompositions of the Boolean lattice into rank-symmetric chains", arXiv 1509.07346 | 2^[n] partitions into C(n, ⌊n/2⌋) symmetric chains; many such partitions exist | search result, NOT read | USE: Σ_Q slack(Q) = Σ over chains of the chain sums, and every chain has the project's L5 telescoping sum; a chain decomposition turns the average of slack over all of 2^[n] into a sum of chain integrals. It bounds the AVERAGE, not the corner |

## K. Circuit file formats

Serves the asteroid language (task asteroid-bench). The format in use is ISCAS `.bench`
(`asteroid/BENCH.md`); AIGER is an export only (`notes/aiger.md`). Status **SR** = seen in a web
search result only, the source itself was not opened (the hosts were not reachable from the
container on 2026-11-24).

| Source | What it gives | Status | Note |
|---|---|---|---|
| F. Brglez, H. Fujiwara, "A neutral netlist of 10 combinational benchmark circuits and a target translator in Fortran", Proc. IEEE ISCAS, 1985 | the ISCAS-85 circuits; distributed as a numeric node list with a Fortran translator; no formal grammar | CITED; SR (title, authors, year, "never formally documented" from a search summary of ddd.fit.cvut.cz/www/prj/Benchmarks/iscas85.pdf and s2.smu.edu iscas85_format.pdf); page numbers not confirmed | `asteroid/BENCH.md` |
| F. Brglez, D. Bryan, K. Kozminski, "Combinational profiles of sequential benchmark circuits", Proc. IEEE ISCAS, May 1989, pp. 1929-1934, doi:10.1109/ISCAS.1989.100747 | the ISCAS-89 circuits | CITED; SR (pages and DOI from a search summary of ddd.fit.cvut.cz ISCAS89.bib and scilit.com) | `asteroid/BENCH.md` |
| `.bench` syntax in practice: ABC `read_bench` / `write_bench` (`src/base/io/ioReadBench.c`, `ioWriteBench.c`); the parser library lorina ("BENCH parser", lorina.readthedocs.io); a description page with the c17 example (sportlab.usc.edu, benchmark-project/bench.html); Atalanta | `INPUT(x)`, `OUTPUT(x)`, `name = GATE(a, b)`, `#` comments; no grammar in the sources cited | SR for ABC, lorina and the description page (none opened); Atalanta: cited, not opened | the grammar in `asteroid/BENCH.md` is asteroid's own statement of the format |
| A. Biere, "The AIGER And-Inverter Graph (AIG) Format Version 20071012", FMV Reports 07/1, Johannes Kepler University Linz, 2007; specification text fmv.jku.at/aiger/FORMAT.aiger | header `aag M I L O A`, literals 2v / 2v+1, binary `aig` | SR (title and report number); cited, not opened (fmv.jku.at unreachable) | `notes/aiger.md` |
| A. Biere, K. Heljanko, S. Wieringa, "AIGER 1.9 And Beyond", FMV Reports 11/2, Johannes Kepler University Linz, 2011 | bad-state, constraint, justice and fairness sections | SR (title and report number); cited, not opened | `notes/aiger.md` |
| AIGER in competitions: the hardware model checking competition (HWMCC, from 2007); SYNTCOMP: S. Jacobs et al., "The First Reactive Synthesis Competition (SYNTCOMP 2014)", arXiv:1506.08726; S. Jacobs, "Extended AIGER Format for Synthesis", arXiv:1405.5793 | AIGER is the input format of both | SR (titles and arXiv numbers); not opened | `notes/aiger.md` |
| Lean's verified AIG: `Std.Sat.AIG` (Lean core, from LeanSAT; used by `bv_decide`) | AND nodes with an inversion flag on each input: the AIGER data model, with proofs | cited, not opened; the module was not opened in this session | `notes/aiger.md`; target of a future proof that `toAag` keeps the function |
| University of California, Berkeley, "Berkeley Logic Interchange Format (BLIF)", 1992 (distributed with SIS) | gates are `.names` truth-table covers | cited, not opened | `asteroid/BENCH.md`, Differences |

## L. Limits, flag algebras and stability (the top level of BOARD.md "THREE LEVELS")

Added by seat L2, 2026-11-25. Every row below is **search result only** (title, venue and a
search-engine summary; no paper opened in full, full texts not fetched). Re-read before relying on
any entry. The last column says how it could apply to "one-NOT circuits on OR systems need
>= base gates"; none of these sources mentions circuits with NOT gates.

| Source | What it gives | Status | How it could apply to 951 |
|---|---|---|---|
| Razborov, "Flag algebras", J. Symbolic Logic 72(4) (2007) 1239-1282, doi:10.2178/jsl/1203350785 | calculus on limits of finite structures; density inequalities proved by semidefinite programs (sums of squares over small labelled patterns); first use: minimum triangle density | search result only (paywalled; summaries from Wikipedia, Matschke notes, Jeong-Park-Yang survey arXiv 2601.12741) | the tool for the top level: write slack >= 0 as a linear inequality in densities of small patterns (sets, wires, the NOT wire h) and look for an SOS certificate; needs the pattern theory to be a universal first-order theory (see seat limits_density_form) |
| Lovász and Szegedy, "Limits of dense graph sequences", J. Combin. Theory B 96 (2006); MSR TR-2004-79; arXiv math/0408173 | graphons as limits of dense graph sequences; every limit is determined by subgraph densities | search result only (abstract-level) | model for a limit object of a growing family of set systems with their circuits; dense only, so a circuit family with sparse wires may have a trivial limit (a real risk: base is about n, gates are sparse) |
| Elek and Szegedy, "Limits of hypergraphs, removal and regularity lemmas. A non-standard approach", arXiv 0705.2179; and "A measure-theoretic approach to the theory of dense hypergraphs", arXiv 0810.4062 (Adv. Math. 2012) | limit objects for k-uniform hypergraphs via ultraproducts; new proofs of hypergraph removal and regularity | search result only (abstract-level) | the OR system is a hypergraph (sets S_w over inputs), so this is the right limit space for the set-system side; the circuit side (wires, gates) is a further structure on top, not covered |
| Zhao, "Hypergraph limits: a regularity approach", arXiv 1302.1634 (Random Struct. Algorithms 2015); Aroskar and Cummings, "Limits, regularity and removal for finite structures", arXiv 1412.8084 | hypergraph limits from a weak regularity lemma; extension of the Elek-Szegedy framework to finite relational structures | search result only (titles and abstracts) | Aroskar-Cummings is the closest fit: a circuit plus its set system is a finite relational structure (relations: input-to-gate, gate-to-gate, NOT-wire); check whether their limit theory accepts it |
| Pikhurko, EJC 2011 (opikhurko.warwick.ac.uk/E/Pikhurko11ejc.pdf), exact Turán result for 3-graphs with two forbidden induced subgraphs | the template: flag algebras for the asymptotic bound, then a stability theorem, then an exact result for all n >= n0 with the unique extremal object T_n | search result only (snippets of the paper) | the exact step for 951: gates >= base for all large n needs stability of near-tight circuits; the Fano corpus with 245 non-up-set tight cubes is the test of whether tight circuits look unique |
| Pikhurko, Sliačan, Tyros, "Strong forms of stability from flag algebra calculations", J. Combin. Theory B 135 (2019), arXiv 1706.02612 | general conditions under which a flag-algebra certificate yields stability and "perfect stability" | search result only (abstract-level) | tells which properties of the certificate (tight constraints, rank of the SDP solution) give stability, so the Opus certificate seat should record them |
| Mubayi and Pikhurko, JCTB 97 (2007); Pikhurko, "An exact Turán result for the generalized triangle", Combinatorica 28 (2008) | same four-step method (stability, then exact) on hypergraph Turán problems, no flag algebras in the older ones | search result only (snippets) | evidence that the stability-then-exact step is routine once the extremal object is unique; here it is not known to be |
| Balogh, Clemen, Lidický: hypergraph Turán problems in the l2-norm (survey and "Solving Turán's tetrahedron problem for the l2-norm"); Balogh, Clemen, Lidický on almost similar triangles | flag algebras plus stability for asymptotically tight (or exact) hypergraph results; Turán density of K_4^3 still open | search result only; whether exactness holds in each case NOT confirmed | shows flag algebras settle some hypergraph problems and not others; a sample of how often the method gives exactness |
| An Oxford thesis (author and title not captured) (ora.ox.ac.uk uuid fb9060d3-...) with chapters on circuits computing CLIQUE and depth-3 threshold circuits, and a Flag Algebra Calculus chapter | the one hit that joins flag algebras and Boolean circuits | search result only (table of contents and introduction; specific results NOT confirmed) | the only lead for a limit theory of circuits; must be opened first. It is about monotone or bounded-depth circuits, not NOT gates |
| Any limit or density theory for Boolean circuits, set systems with OR, hypergraph covers | the search found none; the nearest are hypergraph limits (above) and the Jukna approximation criteria in section F/G | NOT found (two searches, 2026-11-25) | to be recorded in section J if a third search also fails: the circuit-side limit object would have to be built, not cited |
| Hatami and Norine, "Undecidability of linear inequalities in graph homomorphism densities", J. AMS 24 (2011) 547-565, arXiv 1005.2382; Blekherman, Raymond, Wei, Forum Math. Sigma (2024), polynomial inequalities for weighted graphs; Li, arXiv 2505.07378, subset densities | no algorithm decides all (linear, polynomial) density inequalities for graph limits; answers a question of Razborov and of Lovász | search result only (abstract-level) | a hard limit of the method: the density form of 951 might lie in an undecidable class, so a certificate must be found for this specific inequality, not by a general procedure |
| Hatami, Hladký, Král', Norine, Razborov, "Non-three-colorable common graphs exist", Combin. Probab. Comput. 21 (2012), arXiv 1105.0307 | flag-algebra and limit arguments show the 5-wheel is common | search result only | a sample of a limit inequality settled with a computer-aided certificate (a positive example for the method); no direct bearing |
| Limit-theory caveats seen in one slide deck and one search: dense setting only (sparse sequences give a trivial limit); a graphon whose typical-vertex space is not compact disproves a conjecture of Lovász and Szegedy (Hladký slides www.cs.cas.cz/~hladky/slides/FEL.pdf, a PhD thesis not identified) | limits of the method: density only, non-compactness, no general exactness | search result only | exactness and integrality: a flag-algebra bound is real-valued and asymptotic; the project's statement is integer and exact; exactness needs stability, and uniqueness of tight circuits is the open part |

## M. Formal philosophy, and mathematical readings of Deleuze (task philosophy-formal)

Added by seat P1, 2026-11-25. Read status here is stricter than elsewhere: **ABS** = abstract fetched
and read; **search result only** = title, venue and a search-engine summary, nothing opened; **not
reached** = fetch failed (philarchive.org and ddll.inf.tu-dresden.de are outside the session's
allowed network domains, so the Smith, Duffy and Hladik full texts could not be opened). No row is
read in full. Re-read before relying on any entry. Everything in `philosophy/` models a *cited reading*
and claims nothing about what Deleuze meant.

### M1. Existing logical and computational formalisations of philosophy

| Source | What it gives | Status | How it could apply here |
|---|---|---|---|
| Fitelson and Zalta, "Steps Toward a Computational Metaphysics", J. Philosophical Logic 36 (2007), doi:10.1007/s10992-006-9038-7; Oppenheimer and Zalta (Anselm, with Prover9) | Zalta's theory of abstract objects (encoding vs exemplifying) run in Prover9 and Mace4; found an error in an earlier treatment of Plato's Forms; one of three premises of a reconstructed Anselm argument already suffices | search result only (summaries of mally.stanford.edu/cm) | proof that a whole metaphysical system can be mechanised; the encoding relation is the nearest thing to "virtual objects have properties without exemplifying them" |
| Kirchner, Benzmüller, Zalta, "Computer Science and Metaphysics: A Cross-Fertilization", Open Philosophy 2 (2019), arXiv 1905.00787 | Principia Logico-Metaphysica as a shallow semantic embedding in Isabelle/HOL (Kirchner, Archive of Formal Proofs), with artifactual theorems filtered out; new modal-metaphysics results | ABS (abstract fetched) | the method to copy: embed in the host logic, then remove artefacts of the embedding. P2 must say which of its lemmas are artefacts of the Lean encoding |
| Benzmüller and Woltzenlogel Paleo, "Formalization, Mechanization and Automation of Gödel's Proof of God's Existence", arXiv 1308.4526 (ECAI 2014, FAIA 263) | Scott's variant of Gödel's argument in quantified modal logic: natural deduction, TPTP THF, LEO-II and Satallax, Nitpick (consistency), Coq (step by step), Isabelle (Sledgehammer, Metis) | ABS (abstract fetched) | the template for a checked philosophical argument; shows consistency checking next to proof (a model, not only a derivation) |
| Benzmüller and Scott, "Notes on Gödel's and Scott's variants of the ontological argument", Monatsh. Math. (2025); a 2026 arXiv paper "Gödel's and Scott's Variants of the Ontological Argument in Lean 4 and TPTP THF" (arXiv 2609.26806) | later work, including a Lean 4 version | search result only | the one Lean 4 precedent in this family; check its modal-logic embedding before writing a new one |
| Jarrett, "The Logical Structure of Spinoza's Ethics, Part I", Synthese 37 (1978) | the root reference for formalising E1: definitions, axioms and propositions as a deductive system | CITED (via search summaries) | the Spinoza rung: substance, attribute, mode, "in" and "conceived through" as primitives |
| Hladík, tableau reconstruction of Spinoza (WSPI 2004, ddll.inf.tu-dresden.de); Prover9 on E1 p1-11 (2017, reusing Blum and Malinovich); UvA master's thesis (2017, E1 p1-23, consistency proved); Coq "De Deo" (bimodal logic, after Jarrett); Agda project (github OlivierNicole/spino); Lean 4 preprint by Y. Nakamura on Bennett's objection to E1p5 (arXiv 2605.02331, kernel-checked countermodel) | most of E1 reconstructs in formal logic but needs extra axioms Spinoza assumes implicitly; a counter-model to a step | search result only (Hladík full text not reached; Nakamura is a recent unreviewed preprint) | a formal Spinoza exists in several provers; the honest finding is "needs implicit axioms", which P2 should record rather than hide |
| Leibniz: SEP "Leibniz's Modal Metaphysics" (compossibility, complete individual concepts); IEP; a 2014 Queen's University dissertation (compossibility via networks of mutual intelligibility) | working definition: substances are compossible iff no contradiction among predicates deducible from their complete concepts; a world is a maximal compossible set | search result only (SEP and IEP read as snippets) | the Leibniz rung. **No worked-out machine formalisation of the Monadology was found** (one search); a compossibility relation with maximal cliques is the cheap model |
| Leśniewski, Foundations of the General Theory of Sets (1916), On the Foundations of Mathematics (1927-31); Leonard and Goodman, Calculus of Individuals (1940); SEP "Mereology" | parthood as a partial order; sums; the classical extensional theory | search result only (SEP snippets) | the bottom rung; maps to Mathlib `PartialOrder` / `CompleteLattice` / `CompleteBooleanAlgebra` |
| Clarke, "A calculus of individuals based on connection", Notre Dame J. Formal Logic 22(3) (1981); Whitehead, *Process and Reality* (extensive connection); a 1991 analysis (Clarke's axioms characterise complete atomless Boolean algebras) | mereotopology: regions with a primitive connection C; models are Boolean algebras (minus the zero) | search result only | the topological layer, if needed; Casati and Varzi, *Parts and Places* (1999), and RCC8 NOT confirmed by the search |
| Priest's LP as a model of Hegelian dialectic; formal model of dialectical progression (Hegel, Marx) in paraconsistent logic; Günther's trans-classical logic (Pluder); a Jaśkowski-based study (stoa.uv.mx) that doubts Hegel was paraconsistent | contested logics of Hegelian contradiction; the 2023 History and Philosophy of Logic papers (doi 10.1080/01445340.2023.2182584 and .2182598) are among the hits | search result only | Hegel is the foil for Duffy and Deleuze; **no proof-assistant formalisation of Hegel found** (one search: Lean and Isabelle named, nothing) |

### M2. Mathematical readings of Deleuze

| Source | What it gives | Status | How it could apply here |
|---|---|---|---|
| DeLanda, *Intensive Science and Virtual Philosophy* (Continuum, 2002), ch. 1 "The Mathematics of Virtual Philosophy: Manifolds, Vector Fields and Transformation Groups" | multiplicity = manifold (dimensions are properties of a process); singularities of a vector field (Poincaré) as attractors with basins; the virtual as a science of intensities; reviewers dispute his "flat ontology of individuals" | search result only (Protevi outline and reviews; full text not fetched) | the main source for the first definitions: manifold, vector field, singularity, basin |
| Duffy, *The Logic of Expression: Quality, Quantity and Intensity in Spinoza, Hegel and Deleuze* (Ashgate, 2006) | reads Deleuze on Spinoza through the differential calculus: Spinoza's Letter XII diagram as an integral sum of differentials; Leibniz recovers the differential as the genetic force of the calculus; expression as an alternative to Hegelian dialectic; chapter on "the differential point of view of the infinitesimal calculus" | search result only (publisher chapter list, reviews; not reached) | the ladder itself: Spinoza to Leibniz to Deleuze through the differential; the closest published version of what PLAN.md proposes |
| Duffy (ed.), *Virtual Mathematics: The Logic of Difference* (Clinamen, 2006): chapters by Plotnitsky, Badiou, Châtelet, Salanskis, D. W. Smith, DeLanda; Duffy, *Deleuze and the History of Mathematics* | the standard collection of mathematical readings (contents from search) | search result only | where to look for the Riemann and Salanskis readings |
| D. W. Smith, "Axiomatics and Problematics as Two Modes of Formalisation: Deleuze's Epistemology of Mathematics", in *Virtual Mathematics* (2006) 145-168 | two modes of formalisation, axiomatics vs problematics; Deleuze's model for dialectical Ideas is problematics and the history of the calculus | search result only (abstract-level; PhilArchive SMIAAP-8 not reached) | justifies reading "virtual = problem" and "actual = solution" as a model choice |
| D. W. Smith, "Mathematics and the Theory of Multiplicities: Badiou and Deleuze Revisited", Southern J. Philosophy 41 (2003); "Deleuze on Leibniz: Difference, continuity, and the calculus" (2005) | Deleuze and Badiou take opposing routes through mathematics: problematics vs axiomatics, differential vs extensive multiplicities, calculus vs set theory | search result only (PhilArchive SMIMAT-6 not reached) | marks the fork: Deleuze's multiplicity (Riemann, differential) is not Badiou's (ZF set); P2 follows the first and must say so |
| Plotnitsky, "Manifolds: on the concept of space in Riemann and Deleuze", in *Virtual Mathematics* (2006) | Riemann's concept of manifold as Deleuze's source for multiplicity | search result only (title and place in volume; content not seen) | the Riemann reading of multiplicity |
| Lautman, *Essai sur les notions de structure et d'existence en mathématiques* (1938); Salanskis, *L'herméneutique formelle* (1991) and chapter in *Virtual Mathematics* | Lautman's dialectic of problems and their mathematical solutions is the source Deleuze uses for the virtual; Salanskis ties Lautman to Hegelian dialectic | search result only (secondary summaries; the Essai itself and which parts Deleuze draws on NOT confirmed) | the origin of the problem / solution pair; a note only, not a definition |
| Badiou, *Deleuze: The Clamor of Being* (1997); Cambridge chapter "The virtual" in *Badiou's Deleuze* (Roffe) | the critique: if the virtual is an image it is a simulacrum; the actual cannot be grounded by the virtual without becoming a blur or tearing away from it (which breaks univocity); Badiou grounds multiplicity in the empty set | search result only (secondary summaries; the book not opened) | the objection a formal model must face: the actual must be definable from the virtual without a second ground |
| Matti, "Deleuze, axiomatized", Tabula Rasa (2025) | Badiou axiomatises Deleuze, a mathematical framing of The Logic of Sense | search result only | the only "formalisation of Deleuze" lead found; not a Lean-style one |

### M3. Mathlib side (what the readings can map to)

| Source | What it gives | Status | How it could apply here |
|---|---|---|---|
| Yin and Kudryashov, "Integral Curves and Flows on Banach Manifolds in Lean", arXiv 2602.13247 (2026); Mathlib `Mathlib/Geometry/Manifold/IntegralCurve/{Basic,ExistUnique}.lean` and `Riemannian/Basic.lean` (`IsMIntegralCurve`, `IsRiemannianManifold`), present in the project's checkout | existence and uniqueness of integral curves of vector fields on Banach manifolds; names verified present locally (`IsMIntegralCurve` at IntegralCurve/Basic.lean:76) | ABS for the paper; the Mathlib names confirmed by grep in the local checkout | the actual = integral curve; the virtual = vector field |
| Kripke frames and modal logic in Lean: Zulip thread (not in Mathlib; in FormalizedFormalLogic), a Kripke-frames blueprint (matejjazbec.github.io), CSLib Hennessy-Milner logic | no branching-time (CTL) library in Mathlib found | search result only | for Fisher: a branching-time structure is two lines of plain Lean (a preorder-free tree of states), no library needed |

### M4. Mark Fisher

| Source | What it gives | Status | How it could apply here |
|---|---|---|---|
| Fisher, *Capitalist Realism* (2009); *Ghosts of My Life* (2014); Derrida's hauntology; Berardi's "slow cancellation of the future" | hauntology = futures that were cancelled rather than realised, still exerting pressure; capitalist realism = the inability to imagine an alternative | search result only (descriptions, one Wikipedia-level summary, essays) | **No formal or modal-logic treatment of Fisher was found** (one search, "formal logic OR modal logic OR formalization"). Footing is ours to build: see philosophy/PLAN.md |

### M5. Unification: Beauvoir, Hegel, Camus, Lawvere (philosophy-unification seat, 2026-11-25)

Read status as in M: nothing here was read in full in this session. "memory" = cited from the seat's
memory of the text, not re-read. In-copyright works are cited, not copied. Frame and results:
`philosophy/UNIFY.md`.

| Source | What it gives | Status | How it applies here |
|---|---|---|---|
| Beauvoir, *Diary of a Philosophy Student, Volume 1, 1926-27*, ed. Klaw, Le Bon de Beauvoir, Simons (Univ. of Illinois Press, 2006); French: *Cahiers de jeunesse* (2008) | reads Barrès, *Sous l'œil des barbares* (entry of 5 Oct 1926, per the editors' notes); "barbarians" = those who are not the self; 10 July 1927: "this opposition of self and other"; writers read or quoted per reviews: Kant, Bergson, Nietzsche, Schopenhauer, Barrès, Claudel, Cocteau, Gide, Alain-Fournier, Rivière, Mauriac, Goethe | search result only (publisher and Project MUSE listings, a Bookforum review as summarised, French Studies review as summarised); diary not opened; bookforum.com not reachable. NOT confirmed: Alain (the philosopher), Lagneau, a source named "Claudia" | `Beauvoir.Barbarian`, `barbarian_iff_lost` |
| "The Barbarians" as a title by Beauvoir | **no such text found** (one search). The word is Barrès's, taken over in the 1926 diary | searched, not found | nobody need search again |
| Barrès, *Sous l'œil des barbares* (1888), vol. 1 of *Le Culte du moi* | the barbarians are the non-self | search result only (public domain; not opened) | source of the word |
| Simons, "Beauvoir's Early Philosophy: 1926-27" (in the volume above, 29-50) | the self / other problem predates Sartre; Bergson quoted at length | search result only | supports the dating |
| Beauvoir, *L'Invitée* (1943; *She Came to Stay*) | epigraph from Hegel, "Chaque conscience poursuit la mort de l'autre"; ends with Françoise killing Xavière; SEP "Simone de Beauvoir": the murder destroys a particular other, not the other as such | search result only (SEP and two theses as summarised); novel not opened | `Beauvoir.each_seeks_the_death_of_the_other`, `not_every_other_dies` |
| Beauvoir, *Pour une morale de l'ambiguïté* (1947; *The Ethics of Ambiguity*, tr. Frechtman) | facticity / transcendence; the serious man; willing others free | memory | `Beauvoir.ambiguity`, `serious_iff_not_free`; "willing others free" has no theorem (UNIFY.md, what failed) |
| Beauvoir, *Wartime Diary* (Univ. of Illinois Press) | not verified in this session | not confirmed | not used |
| Hegel, *Phänomenologie des Geistes* (1807), Introduction (determinate negation) and "Lordship and Bondage"; Baillie translation (1910) is public domain | a refutation has a content; the struggle to the death defeats recognition | memory | `Hegel.determinate_negation`, `Beauvoir.no_recognition_between_barbarians` |
| Lawvere, "Unity and Identity of Opposites in Calculus and Physics", Appl. Categ. Structures 4 (1996) 167-174; nLab "adjoint modality" | adjoint cylinder: an adjoint triple whose two outer functors are full and faithful | search result only (nLab as summarised; paper not opened) | `Hegel.unity_and_identity_of_opposites` (even ⊣ half ⊣ odd on ℕ, our form) |
| Lawvere, "Adjointness in Foundations", Dialectica 23 (1969); "Diagonal arguments and cartesian closed categories" (1969) | quantifiers as adjoints; the fixed point theorem | memory | `Unify.level_adjoints`, `Camus.lawvere_fixed_point` |
| Camus, *Le Mythe de Sisyphe* (1942) | the absurd as the confrontation of a demand for unity with a world that does not answer; revolt | memory | `Camus.no_total_answer`, `Camus.revolt` |
| Priest, "The Logic of Paradox", J. Philosophical Logic 8 (1979) | three-valued LP: contradictions without explosion | memory | `Hegel.lp_no_explosion` (a textbook check, not joined to the frame) |

### M6. Beauvoir routed at quantum gravity's discrete structures (seat BQG, 2026-11-25)

Read status: **memory** throughout. No row was opened or fetched in this session, so titles, venues
and numbers are from the seat's memory and should be checked before being relied on. Results:
`philosophy/BEAUVOIR_QG.md`, `lean/PEqualNP/Philosophy/BeauvoirQG.lean`.

| Source | What it gives | Status | How it applies here |
|---|---|---|---|
| Beauvoir, *L'Invitée* (1943; *She Came to Stay*) | the triad Françoise / Pierre / Xavière; Hegel epigraph | memory of secondary accounts; novel not opened; in copyright | reading only: `pure_pair_decouples`, `ghz_pair_separable` |
| Beauvoir, *Pour une morale de l'ambiguïté* (1947) | ambiguity; one's own freedom and that of others | memory; not re-read; in copyright | reading only: `pure_iff_product`, `entropy_symm` |
| Nielsen and Chuang, *Quantum Computation and Quantum Information* (2000), §2.5 | Schmidt decomposition; reduced states of a pure state share nonzero eigenvalues | memory | `entropy_symm`, `moments_symm`, `schmidt_rank_symm` (proved without Schmidt, by `charpoly_mul_comm'`) |
| Wootters, "Entanglement of formation of an arbitrary state of two qubits", Phys. Rev. Lett. 80 (1998) 2245 | concurrence; for a pure two-qubit state it is `2 |det M|` | memory | `minor`, `sum_minor_sq` |
| Rungta, Bužek, Caves, Hillery and Milburn, "Universal state inversion and concurrence in arbitrary dimensions", Phys. Rev. A 64 (2001) 042315 | I-concurrence `√(2(1 − tr ρ²))` | memory | `sum_minor_sq`, `pure_iff_product` |
| Coffman, Kundu and Wootters, "Distributed entanglement", Phys. Rev. A 61 (2000) 052306 | monogamy inequality for three qubits | memory | **not proved**; only the extreme case `pure_pair_decouples` |
| Greenberger, Horne and Zeilinger (1989) | the GHZ state | memory | `ghz_pair_separable`, `ghz_couple_mixed` |
| Ryu and Takayanagi, "Holographic derivation of entanglement entropy from AdS/CFT", Phys. Rev. Lett. 96 (2006) 181602 | entropy of a boundary region = area of a minimal surface | memory | premise in prose for `rt`; not proved |
| Pastawski, Yoshida, Harlow and Preskill, "Holographic quantum error-correcting codes", JHEP 06 (2015) 149 | tensor networks in which the entropy of a connected boundary region is a minimal cut | memory (also §I) | premise in prose; `schmidt_rank_le_bond_pow` is the upper-bound half under an assumed factorisation |
| Headrick and Takayanagi, "A holographic proof of the strong subadditivity of entanglement entropy", Phys. Rev. D 76 (2007) 106013 | strong subadditivity from minimal surfaces | memory | `rt_submodular` (graph form) |
| Hayden, Headrick and Maloney, "Holographic mutual information is monogamous", Phys. Rev. D 87 (2013) 046003 | monogamy of mutual information; GHZ violates it | memory | `rt_mmi`, `no_network_has_ghz_entropies` |
| Bao, Nezami, Ooguri, Stoica, Sully and Walter, "The holographic entropy cone", JHEP 09 (2015) 130 | graph models: entropies as minimal cuts of weighted graphs; proofs by contraction maps | memory | the definitions `cut`, `Anchored`, `rt`; `edge_monogamy` is a contraction check |
| Van Raamsdonk, "Building up spacetime with quantum entanglement", Gen. Rel. Grav. 42 (2010) 2323 | connectivity of space from entanglement | memory | reading only ("entanglement is the edge"): `bell_bond_saturates` |
| Bombelli, Lee, Meyer and Sorkin, "Space-time as a causal set", Phys. Rev. Lett. 59 (1987) 521 | spacetime as a locally finite partial order | memory | `Spacelike`, `Beyond`, `causal_order_from_links` |

## J. Searched and not found (so nobody searches again)

- A one-NOT or few-NOT lower bound for Boolean sums: none in 255 citing works (`research-crawl`).
- A fractional Hall / transportation lemma with unit gate capacity in gate elimination or monotone
  lower bounds: two searches, no hit (`research-hall-charging-lit`).
- A Nechiporuk / Mehlhorn-type bound for Boolean sums with don't-care sets (`research-partial`).
- A statement, conjecture or refutation of C(x ⊕ f) = min(C f, C ¬f) + c (board wall "XOR
  extension").
- Mapping the continuous form to the discrete corner (task continuous-mapping): no source found that proves an inequality for a DIFFERENCE of two decreasing set functions from a continuous extension; no source linking M-natural / L-natural convexity to the multilinear extension (only to the Lovász extension); Laplante-Lee-Szegedy (adversary / formula size) was not searched; Wikipedia and the Hart homepage are blocked in this session (search result only).
- Unreachable full texts: Springer, SIAM, ScienceDirect (Amano-Maruoka(-Tarui), Pippenger TCS 1980
  from the publisher), Hiltgen-Paterson, Korshunov, Kannan 1982.

## Where the notes are

`one-not/board/agents/`: research-lit, research-crawl (+ `research-crawl-citers.tsv` if present),
research-nominCE-lit, research-hall-charging-lit, research-charging, research-hypergraph-hall,
research-heredity-lit, research-and-replacement, research-negation-influence, research-partial,
research-relax, research-fable-weight, research-fable-sokolov, research-pnp-defs, tractability-lit,
coord-lateral, front-referee-lateral. `notes/general/`: research-lit-unrestricted,
clay-official-statement, generalize-ladder-survey. `notes/checker/`: note-2.
