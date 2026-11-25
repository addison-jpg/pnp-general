# research: what is out there for unrestricted circuits (board card 4) — verified list

Legend: ABS = claim read in the paper's abstract (OpenAlex / Semantic Scholar / publisher); TXT = read in full text;
TLDR = only Semantic Scholar's machine summary seen; MEM = standard result, not re-read here. Retrieved 2026-11-24.

## 1. Explicit lower bounds for general circuits (gate elimination)
- Li, Yang, '3.1n - o(n) circuit lower bounds for explicit functions', STOC 2022, doi 10.1145/3519935.3519976 (ABS, TXT ECCC
  TR21-023): affine dispersers need 3.1n - o(n) gates over all binary gates (B2); measure µ(C,P,R) with a packing P of troubled
  pairs (details: pequalnp-work research/tools/research951/charging/gate_elim_extract.md).
- Find, Golovnev, Hirsch, Kulikov, FOCS 2016 (TXT ECCC TR15-166): (3 + 1/86)n - o(n); Blum 1984 3n - o(n) before (ABS of Li-Yang).
- Iwama, Morizumi, 'An explicit lower bound of 5n - o(n) for Boolean circuits', MFCS 2002, doi 10.1007/3-540-45687-2_29 (TLDR):
  improves Lachish-Raz 4.5n - o(n) to 5n - o(n) 'using the same family of Boolean functions'. NOTE: this is the De Morgan / U2
  basis (AND, OR; negations not counted), so the board's 'about 5n gates for AND, OR, NOT' should read 'NOT gates free'.
- Limits: Golovnev, Hirsch, Knop, Kulikov, 'On the limits of gate elimination', ECCC TR16-119 (TXT): subadditive measures that do
  not use properties of the function cannot give strong bounds (drops <= m·µ(g) per m-substitution).
## 2. Fixed-degree bounds (L-gen-102) one level up
- Kannan, 'Circuit-size lower bounds and non-reducibility to sparse sets', Inf. Control 55 (1982), doi 10.1016/s0019-9958(82)90382-5
  (MEM: Σ2P ∩ Π2P ⊄ SIZE(n^k) for every k). CAUTION: S2's TLDR says 'a language L_k in NP without O(n^k)-size UNIFORM circuits';
  not reconciled, full text not reached.
- Cai, 'S2P ⊆ ZPP^NP', JCSS 2007, doi 10.1016/j.jcss.2003.07.015 (TLDR); with S2P ⊄ SIZE(n^k) (MEM) this gives ZPP^NP ⊄ SIZE(n^k).
- Vinodchandran, 'A note on the circuit complexity of PP', TCS 2005, doi 10.1016/j.tcs.2005.07.032 (TLDR): for every k, PP has
  languages without circuits of size n^k.
- Santhanam, 'Circuit lower bounds for Merlin-Arthur classes', STOC 2007, doi 10.1145/1250790.1250832 (TLDR + MEM): MA/1 and
  promise-MA are not in SIZE(n^k).
## 3. Near-maximum bounds by range avoidance
- Korten, 'The hardest explicit construction', FOCS 2021, doi 10.1109/focs52979.2021.00051 (ABS): constructing a truth table of high
  circuit complexity is complete for APEPP under NP-oracle reductions.
- Chen, Hirahara, Ren, STOC 2024, doi 10.1145/3618260.3649624 (ABS): a language in S2E/1 with circuit complexity >= 2^n/n; also Σ2E,
  (Σ2E ∩ Π2E)/1, ZPE^NP/1. Li, STOC 2024, doi 10.1145/3618260.3649615 (ABS): S2E ⊄ i.o.-SIZE[2^n/n] (almost everywhere).
## 4. Algorithms imply lower bounds
- Williams, 'Nonuniform ACC circuit lower bounds', JACM 2014, doi 10.1145/2559903 (ABS): NEXP has no polynomial-size ACC circuits;
  E^NP has no 2^{n^{o(1)}}-size ACC circuits. Murray, Williams, STOC 2018, doi 10.1145/3188745.3188910 (ABS): easy witness lemma
  for NP and NQP; nontrivial circuit-analysis algorithms give lower bounds for NQP (NQP ⊄ ACC0, MEM).
## 5. Hardness magnification (a slightly superlinear bound for a special problem gives L-gen-101-type separations)
- Oliveira, Santhanam, FOCS 2018, doi 10.1109/focs.2018.00016 (ABS): if MCSP[2^{√n}] is not solvable on average with zero error by
  formulas of linear (or sublinear) size then NP has no polynomial-size formulas.
- McKay, Murray, Williams, STOC 2019, doi 10.1145/3313276.3316396 (ABS): weak lower bounds on resource-bounded compression
  (search MCSP generalizations) imply strong separations.
- Chen, Hirahara, Oliveira, Pich, Rajgopal, Santhanam, ITCS 2020, doi 10.4230/lipics.itcs.2020.70 (ABS): 'locality barrier': the
  known weak lower bounds also hold for oracle/local variants, so they cannot be magnified as is.
## 6. Meta-complexity
- Hirahara, FOCS 2018, doi 10.1109/focs.2018.00032 (ABS): first non-black-box worst-case to average-case reduction within NP (MINKT).
- Liu, Pass, FOCS 2020, doi 10.1109/focs46700.2020.00118 (ABS): one-way functions exist <=> K^t is mildly hard on average.
## 7. Barriers (board rows L-lib-061/062/065/076/086)
- Baker, Gill, Solovay, SIAM J. Comput. 4 (1975), doi 10.1137/0204037 (TLDR). Razborov, Rudich, 'Natural proofs', JCSS 55 (1997),
  doi 10.1006/jcss.1997.1494 (MEM). Aaronson, Wigderson, 'Algebrization', ACM TOCT 2009, doi 10.1145/1490270.1490272 (ABS).
## 8. NOT gates (the ladder) — ADDED with checked content from the L-meta-951 work
- Markov, JACM 5 (1958) 331-334, doi 10.1145/320941.320945: ⌈log2(d(f)+1)⌉ NOT gates necessary and sufficient (TXT via Jukna BFC
  Thm 10.5). Fischer 1975 (LNCS 33), doi 10.1007/3-540-07407-4_9: ⌈log(n+1)⌉ NOTs with polynomial overhead (Jukna BFC Thm 10.18).
- Amano, Maruoka, SICOMP 2005 (TXT of the 1998 RIMS version, Thm 2): size_t(f) >= min over families of 2^{t+1}-1 monotone functions
  covering the sensitivity graph of f of the max monotone size; superpolynomial for CLIQUE with (1/6) log log n NOTs (ABS).
- Sung, Tanaka, IPL 2002: removing one NOT can cost exponentially (ABS). Jukna, IPL 2004: minimum number of negations leading to
  super-polynomial savings. Jukna, Lingas, JCSS 129 (2022) (TXT ECCC TR18-154): negation width w: size >= monotone size / K - 1.
- SLICE FUNCTIONS (the route from monotone to unrestricted circuits): Berkowitz 1982; Valiant, 'Negation is powerless for Boolean
  slice functions', SIAM J. Comput. 15 (1986), doi 10.1137/0215037 (ABS): for slice functions monotone complexity <= c·general +
  O(n (log n)^2). Wegener, CoBF §6.13-6.15 (TXT): set circuits; any ω(n log^2 n) monotone bound for a slice gives a general bound.
  Hiltgen, Paterson, Comput. Complexity 5 (1995) (TLDR): the Nečiporuk 1-slice has a 3n + o(n) circuit (known slice instances easy).
- One NOT on Boolean sums (rung 1, L-meta-951): no prior result (citation crawl of 28 seeds, 255 citers: pequalnp-work board
  agents/research-crawl.md); correctness on inputs of weight <= k is not enough at scale for any fixed k (research Fable W, AG(2,25)
  construction checked).
