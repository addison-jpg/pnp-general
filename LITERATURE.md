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
