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

### The generalization question (README C4): do AND and NOT gates help for Boolean sums?

| Source | What it gives | Status |
|---|---|---|
| Nechiporuk 1969; Wegener 1987 Thm 6.2; Mehlhorn 1979; Pippenger 1980 | AND gates do not help for (1,1)-disjoint sums in MONOTONE circuits; at most a factor max{h−1, k−1} for (h,k)-disjoint | TXT (Wegener, Pippenger), CITED (others) |
| Jukna and Sergeev 2013 §7 | ASKS whether general circuits help for Boolean sums (OR against GEN): an open question, not a stated conjecture | TXT |
| Blum, ECCC TR24-179 | proposes (1,1)-disjoint Boolean sums with negations as an open target | TXT (outlook) |
| Find, Göös, Järvisalo, Kaski, Koivisto, Korhonen, "Separating OR, SUM, and XOR circuits", arXiv 1304.0513v2 (Thm 1: Gap_{+/∨} = Ω(n^{1/2}/log²n); Cor 3: Gap_{∨/⊕}, Gap_{+/⊕} = Ω(n/log²n); Thm 5 Mehlhorn-Pippenger: (s,t)-free ⇒ C∨ ≥ \|A\|/(st)) | linear circuits only (OR / SUM / XOR, wires, no AND, no NOT, no depth restriction). XOR circuits (non-monotone, cancellation) beat OR by n/log²n on dense k-uniform matrices (not on sparse (1,1)-free ones). States conjectures only about gaps between the three linear models (all non-trivial gaps n^{1-o(1)}); no conjecture or refutation of C4. Weaker model than AND/OR/NOT | TXT (`research-literature-c4`) |
| Boyar and Find, "Cancellation-free circuits in unbounded and bounded depth", arXiv 1305.3041v2 (Lemma 1 = Nechiporuk-Mehlhorn-Pippenger-Wegener: k-free A ⇒ C∨ ∈ Ω(\|A\|/k²); Thm 4: λ(n)=max C∨/C⊕ ∈ Ω(n/log²n), also constant depth ≥ 2; Sect. 6-7: Sierpinski matrix, OR and cancellation-free ≥ ½ n log n) | linear XOR / cancellation-free / OR circuits only; no AND, no NOT. XOR cancellation beats OR on a dense random-product matrix (A = BC). Open problem in Sect. 7 is whether cancellation helps for the Sierpinski matrix, not C4. No conjecture or refutation of C4 | TXT (`research-literature-c4`) |
| Cavalar, Fabris, Mukhopadhyay, Srinivasan, Yehudayoff, "Negations are powerful even in small depth", arXiv 2512.19515v1 (Thm 1.1: ΣΠΣ size O(n³) polynomial, monotone arithmetic ≥ 2^{Ω(n)}; Thm 1.2 constant degree; Thm 1.5: monotone Boolean f in uniform NC², monotone size 2^{n^{1/3-o(1)}}, only the abstract, Sect. 1 and 1.3 read; proofs of Sect. 2-5 not read) | functions: spanning-tree-like polynomial from expander graph, unique/different-from-1 disjointness, matroid / rank functions; NOT Boolean sums. Negation or subtraction, depth 3 arithmetic, depth O(log² n) Boolean. Its open problems (Sect. 1.3) are about monotone rank programs, planar matching, constant-depth separations: nothing on Boolean sums or C4. A caution only: negations can be exponentially powerful for other functions; the paper says nothing about sums | PART (`research-literature-c4`) |
| Tsukiji, "Circuit Complexity of An Explicitly Defined First Slice Function", RIMS Kokyuroku 906 (1995) 81-88, file 0906-11.pdf, hdl:2433/59458 = SAME paper as row 38 (confirmed from repository metadata). Introduction, p. 81: constant-slice functions have C_{∨,∧}(f) = Θ(C_{∨,∧,¬}(f)), but "this relation, generally, does not hold for a Boolean sum" (the example after "e.g." is garbled in the text extraction; not read) | an unsupported remark, no proof, no citation for it: a Boolean sum can have nonlinear monotone lower bounds ([6], [5,7] = (s,t)-disjointness), and the remark suggests nothing about a non-monotone upper bound. It is not a statement of C4 and not a refutation of it. Adds nothing to row 38 except this quote | TXT (intro re-read; same paper as row 38) (`research-literature-c4`) |
| Two web searches, 2026-11-24 | no paper found that states C4 as a conjecture or proves or refutes it | absence of a hit is not evidence of absence |

### Sums over paths (for README §6)

| Source | What it gives | Status |
|---|---|---|
| Adleman, DeMarrais, Huang, "Quantum computability", SIAM J. Comput. 26 (1997) | the acceptance probability of a quantum computation is a sum over computation paths; BQP ⊆ PP | MEM |
| Feynman 1948; Feynman and Hibbs 1965 | the path integral as a limit of sums over discretized histories | MEM |
| Markov-Kakutani fixed point theorem | fixed points of commuting affine maps by averaging; the Cesàro proof in `Helpers/FixedPoint.lean` is the one-map case | MEM; the one-map case is checked |
| Lutz, resource-bounded measure (1992) | martingales on Cantor space; "NP is not p-measure zero" is a hypothesis stronger than P ≠ NP | MEM |

## J. Searched and not found (so nobody searches again)

- A one-NOT or few-NOT lower bound for Boolean sums: none in 255 citing works (`research-crawl`).
- A fractional Hall / transportation lemma with unit gate capacity in gate elimination or monotone
  lower bounds: two searches, no hit (`research-hall-charging-lit`).
- A Nechiporuk / Mehlhorn-type bound for Boolean sums with don't-care sets (`research-partial`).
- A statement, conjecture or refutation of C(x ⊕ f) = min(C f, C ¬f) + c (board wall "XOR
  extension").
- Unreachable full texts: Springer, SIAM, ScienceDirect (Amano-Maruoka(-Tarui), Pippenger TCS 1980
  from the publisher), Hiltgen-Paterson, Korshunov, Kannan 1982.

## Where the notes are

`one-not/board/agents/`: research-lit, research-crawl (+ `research-crawl-citers.tsv` if present),
research-nominCE-lit, research-hall-charging-lit, research-charging, research-hypergraph-hall,
research-heredity-lit, research-and-replacement, research-negation-influence, research-partial,
research-relax, research-fable-weight, research-fable-sokolov, research-pnp-defs, tractability-lit,
coord-lateral, front-referee-lateral. `notes/general/`: research-lit-unrestricted,
clay-official-statement, generalize-ladder-survey. `notes/checker/`: note-2.
