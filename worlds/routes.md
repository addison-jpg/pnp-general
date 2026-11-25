# A map, not progress on P vs NP

Seat W3, 2026-11-25. Task: [`boards/tasks/worlds-map.md`](../boards/tasks/worlds-map.md). Nothing here says P versus NP is proved, near, or helped by this repository. A route is a theorem that carries a result on one axis to the P vs NP cut. For each route: statement, source, threshold (what bound, on what problem), barrier, read status, and the distance from this repository.

Read status as in [`LITERATURE.md`](../LITERATURE.md): TXT, ABS, TLDR, MEM, CITED. Here "ABS (fetched)" means a page summary of the abstract was fetched by a tool in this seat; no paper was read in full. New rows are in LITERATURE.md section G; see the end of this file.

## What this repository has (the point to measure from)

- Explicit functions in P with linear lower bounds in a restricted model: circuits with monotone gates (AND, OR) plus at most one NOT gate.
  - Boolean sums with (1,1)-disjoint sets: exact value Σ(|S| − 1) AND/OR gates, one NOT gate saves nothing. Proved only in three cases (the NOT reads an input; every set has at most three points; the certificate test). The general one-NOT case is NOT proved (`no_minCE`, `BottomPay` open). Several NOT gates: only OR of n inputs and OR systems (n − comp).
  - Edge function f_G(x) = OR over edges uv of (x_u AND x_v), one input per vertex: exactly |E| + τ(G) − 1 gates, NOT gates allowed, on forests and on graphs with long threads (cycles of length at least 7, high-degree vertices far apart). With |E| ≤ 3n/2 on those classes, this is at most about 2.5n for n inputs. Source: `notes/note-1-edge-function-exact-size.md`.
  - The general-circuit side is only Markov: about log n NOT gates suffice for any circuit (checked).
- All bounds are linear in the number of input variables, for a restricted class of functions (specific graph families, disjoint-set sums), in a restricted model, and only for one NOT gate (or the monotone case).

## Summary table

| Route | Needs, on which problem | Barrier | Our distance |
|---|---|---|---|
| Hardness magnification (OS18, MMW19, CJW19) | slightly superlinear n^{1+ε} (or n^{3+ε} for formulas) against MCSP-type or sparse NP problems, in general circuits or a named weak class | locality barrier (CHOPRS20) | not comparable: below the threshold by a polynomial factor n^ε, and wrong problem, wrong model |
| Algorithms to lower bounds (Williams 2011; MW18) | a faster-than-brute-force circuit-SAT or approximate-counting algorithm for the class | relativization and algebrization avoided; natural proofs avoided only by being non-constructive-in-the-needed-way; stops at ACC and similar | no overlap: we have no algorithm and no class of this kind |
| Karp–Lipton | an NP problem with small general circuits | none stated; a conditional collapse, not a separation route | none: needs an upper bound on SAT, we only have lower bounds on P functions |
| Meta-complexity (Liu–Pass 2020; Hirahara; Ilango) | average-case hardness of time-bounded Kolmogorov complexity, or NP-hardness of MCSP variants | MCSP NP-hardness itself open | none: no bound on a meta-complexity problem |

## 1. Hardness magnification

**Statement.** A barely non-trivial lower bound for a specific problem in a weak model implies a super-polynomial or exponential lower bound in a strong model.

**Sources and exact thresholds (as fetched).**
- Oliveira and Santhanam, "Hardness Magnification for Natural Problems", FOCS 2018, ECCC TR18-139. ABS (fetched). If MCSP[2^√n] cannot be solved on average with zero error by formulas of linear (or sub-linear) size, then NP has no polynomial-size formulas. A depth-d AC0 version for vertex cover of size (log n)^c needs size m^{1+ε}, m = Θ(n²). MKtP[N^ε, N^ε + 5 log N] needing circuits of size N^{1+δ} gives EXP not in SIZE(poly). Approximate MCSP not in sublinear-time randomized algorithms gives NP not in BPP.
- McKay, Murray, Williams, "Weak lower bounds on resource-bounded compression imply strong separations of complexity classes", STOC 2019. CITED (LITERATURE.md section G lists it by seat; not opened here). Statement from memory of the abstract: a weak lower bound for compression-type problems (MCSP-style) implies NP not in P/poly or similar. Treat as MEM, re-read before relying on it.
- Chen, Jin, Williams, "Hardness Magnification for all Sparse NP Languages", FOCS 2019, ECCC TR19-118. ABS (fetched). If some 2^{n^{o(1)}}-sparse language in NP is not in Circuit[n^{1+ε}] for some ε > 0, then NP does not have n^k-size circuits for any fixed k. Analogues for De Morgan formulas, B_2-formulas, branching programs, AC0[6], TC0. Search versions: search-MCSP[2^{βm}] without De Morgan formulas of size n^{3+ε} (all constant β > 0) gives Parity-P not in NC1.
- Oliveira, Pich, Santhanam, "Hardness magnification near state-of-the-art lower bounds", Theory of Computing 2021. TLDR (search result): thresholds sit near known bounds in several models; Gap-MKtP for U2-formulas with parity leaves lies below known bounds.

**Threshold, stated plainly.** For input length N (a truth table, or a sparse language's inputs): a lower bound of the form N^{1+ε} for a general circuit, or N^{3+ε} for De Morgan formulas, on one of: MCSP with a 2^{o(m)}-type size parameter, MKtP, search-MCSP, approximate (gap) MCSP, vertex cover of polylog size, or any 2^{n^{o(1)}}-sparse NP language. The problem must be one whose YES set is sparse or whose approximate or search version is the hard part, and it must be in NP (or a stated version). A bound on an arbitrary function in P does not count.

**Barrier.** The locality barrier (route 2). The papers also claim magnification avoids natural proofs; that claim is the subject of CHOPRS20.

**Read status.** ABS (fetched) for OS18 and CJW19; CITED / MEM for MMW19; TLDR for OPS21.

**Our distance.** Three gaps, all open and unrelated to each other.
1. Size: the best bound here is about 2.5N (linear in the number of inputs) for f_G; magnification needs N^{1+ε}. The factor missing is a polynomial N^ε, not a constant.
2. Problem: f_G with a fixed graph per n is a single explicit function in P, not MCSP, MKtP, search/gap MCSP, or a sparse NP language. Boolean sums are n-output functions in P. The thresholds are about specific hard-looking problems.
3. Model: our bounds hold for monotone plus at most one NOT gate (and for f_G, all circuits, but only on special graph classes and only linearly). The magnification statements need either general circuits or a named class where the target bound is the best known frontier (for formulas, around n^{3−o(1)} or n^2 depending on the model).
Unless a route that applies is found, this repository sits below every known magnification threshold.

## 2. The locality barrier

**Statement.** Known magnification theorems show that the relevant problems have efficient circuits with small fan-in oracle gates; lower-bound techniques against weak models often extend to circuits with such oracle gates. Therefore direct adaptation of those techniques to reach the magnification thresholds is unlikely to work.

**Source.** Chen, Hirahara, Oliveira, Pich, Rajgopal, Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", ITCS 2020; JACM 2022; ECCC TR19-168; arXiv 1911.08297. ABS (fetched, plus a search summary): they also show that slightly superlinear circuit lower bounds for certain MCSP versions would imply that natural proofs do not exist.

**Threshold.** Not a route but a constraint on routes: a proof of the magnification-threshold bound must use a technique that does not survive adding small fan-in oracle gates.

**Barrier it is.** Locality barrier.

**Read status.** ABS (fetched).

**Our distance.** Our technique counts gates by exchange and Hall-type charging on AND/OR structure; whether it survives small fan-in oracle gates is unchecked. Gate elimination on explicit functions is the standard example of a technique that is "local" in this sense (stated here from memory, MEM, not checked against the paper). We have not tested it. No gap size is defined, only an open question.

## 3. Algorithms to lower bounds

**Statement.** A slightly faster than exhaustive-search algorithm for circuit satisfiability (or approximate counting) for a circuit class C yields a lower bound against C for a nondeterministic class.

**Sources.**
- Williams, "Non-uniform ACC circuit lower bounds", CCC 2011; JACM 61(1), 2014. MEM. Result: NEXP is not in ACC0. Route used: a faster algorithm for ACC0 circuit-SAT plus the nondeterministic time hierarchy.
- Murray and Williams, "Circuit lower bounds for nondeterministic quasi-polytime: an easy witness lemma for NP and NQP", STOC 2018, ECCC TR17-188. ABS (fetched). If every NP problem has n^k-size circuits then every yes-instance of an NP verifier has a witness encoded by a circuit of size n^{O(k³)}; the same for NQP. Consequence with the known ACC∘THR SAT algorithms: for every fixed k, NQP does not have ACC∘THR circuits of size n^{log^k n}.

**Threshold.** A circuit-analysis algorithm (SAT or approximate counting) faster than 2^n/poly-type brute force for the target class. For a separation of NP from P/poly: such an algorithm for general polynomial-size circuits, which is not known; the known successes are for ACC0 and ACC∘THR, whose lower bounds are for NEXP and NQP, not NP.

**Barrier.** Relativization and natural proofs are avoided in the sense stated in the sources; Williams's own survey notes this route stops at ACC and fails to extend to general circuits. Algebrization: stated as avoided in Williams's papers (MEM, not re-read here).

**Read status.** MEM (Williams 2011), ABS (fetched, MW18).

**Our distance.** None. This repository has lower bounds on gate counts and no SAT or counting algorithm for a circuit class. It is not on this axis.

## 4. Karp–Lipton

**Statement.** If NP ⊆ P/poly then the polynomial hierarchy collapses to its second level (Σ2 = Π2 = PH).

**Source.** Karp and Lipton, STOC 1980. MEM (also listed in LITERATURE.md section N).

**Threshold.** Not a lower-bound route. It states: an upper bound (SAT has polynomial-size circuits) would cause a collapse. Its contrapositive says: if PH is infinite (or NP is not in Σ2 ∩ Π2 type classes), then NP is not in P/poly. So it carries a hypothesis about PH, not a circuit lower bound, to a circuit lower bound.

**Barrier.** None applies to the implication itself; it relativizes.

**Read status.** MEM.

**Our distance.** None. The implication needs a bound on SAT, an NP problem. Our bounds are for functions in P, which Karp–Lipton cannot use.

## 5. Meta-complexity

**Statements.**
- Liu and Pass, "On one-way functions and Kolmogorov complexity", FOCS 2020. TLDR (search result): one-way functions exist if and only if polynomial-time-bounded Kolmogorov complexity K^t is mildly hard on average. Ilango, Ren and Santhanam extended the equivalence to hardness over arbitrary polynomial-time samplable distributions (stated in a 2026 arXiv paper that the search returned).
- Hirahara, FOCS 2018 and later. Search result and an ECCC report: one-way functions exist if and only if it is NP-hard to approximate distributional Kolmogorov complexity under randomized polynomial-time reductions and NP is hard in the worst case.
- Hirahara, FOCS 2022. TLDR (search result): NP-hardness, under randomized reductions, of the partial-function version of MCSP and of MKTP*, MINKT* on partial strings.
- Ilango, "Constant depth formula and partial function versions of MCSP are hard", FOCS 2020. TLDR (search result): hardness for the partial-truth-table version (inputs 0, 1, *) and for the constant-depth formula version. The board says this is "already in LITERATURE.md"; it is not (grep for "Ilango" found nothing at the start of this seat). It is added now.
- Whether MCSP itself is NP-hard remains open (search result).

**Threshold.** Average-case hardness of K^t, or NP-hardness of MCSP-type problems under suitable reductions. These carry results between the average-case axis (worlds: Pessiland, Minicrypt) and the worst-case cut. No bound on gate counts of an explicit function is involved.

**Barrier.** Hirahara's reductions are randomized; a deterministic NP-hardness proof of full MCSP is open, and some results are known to face relativization-type obstacles for black-box reductions (MEM, not checked).

**Read status.** TLDR for Liu–Pass, Hirahara and Ilango (search results only; no abstract opened).

**Our distance.** None. No problem here is a meta-complexity problem. MCSP asks for the circuit size of a given truth table; the exact sizes proved here (Σ(|S|−1), |E| + τ − 1) are sizes for a fixed family of functions, not a decision procedure on arbitrary truth tables. One could ask whether f_G-type truth tables are instances where an MCSP algorithm is easy; that is not a route, only an observation, and it is unchecked.

## 6. Closing the gap: the plain statement

- Our theorem class: linear lower bounds (about |E| + τ − 1 and Σ(|S|−1)) on explicit functions in P, restricted model (monotone plus one NOT gate, three proved cases) or special graph classes.
- Nearest route: hardness magnification (route 1). Its threshold is N^{1+ε} for general circuits on an MCSP-type or sparse NP problem, N^{3+ε} for De Morgan formulas on search-MCSP. Our distance: a polynomial factor N^ε in size, plus a different problem (we bound functions in P, not MCSP-type or sparse NP problems), plus a restricted model. No finite number of NOT gates or increase in the constant 2.5 closes this.
- No route applies. Even a full proof of the general one-NOT theorem would still be a linear bound in a restricted model on functions in P.
- Barriers, in addition to the above: relativization (Baker–Gill–Solovay 1975), natural proofs (Razborov–Rudich 1997), algebrization (Aaronson–Wigderson 2009); see LITERATURE.md section H.

## LITERATURE.md rows added by this seat

Section G gains rows (appended at the end of the section) for: Chen–Jin–Williams FOCS 2019 (ABS fetched), Murray–Williams STOC 2018 (ABS fetched), Oliveira–Santhanam 2018 (ABS fetched), CHOPRS 2020 (ABS fetched), Oliveira–Pich–Santhanam 2021 (TLDR), Hirahara FOCS 2022 and Ilango FOCS 2020 (TLDR). Section J gains lines for what was not opened (McKay–Murray–Williams, Williams 2011 full text, Karp–Lipton, and the Liu–Pass paper).
