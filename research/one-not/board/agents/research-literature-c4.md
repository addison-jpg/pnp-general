# research-literature-c4 (research-desktop, 2026-11-24)

Question: is there a STATED conjecture, or a refutation, of "general AND/OR/NOT circuits do not beat base = sum(|S_i|-1) on (1,1)-disjoint Boolean sums"?
VERDICT: neither. None of the four sources states C4 or refutes it. Public sources only. PDFs fetched and run through pdftotext.

## 1. arXiv 1304.0513 (Find et al.) - TXT (whole text)
- Model: wire-counted linear circuits over OR, SUM (integer +), XOR. No AND gates, no NOT, any depth.
- Thm 1: Gap_{+/OR}(n) = Omega(n^{1/2}/log^2 n). Cor 3: Gap_{OR/XOR}, Gap_{+/XOR} = Omega(n/log^2 n), via k-uniform dense matrices (Thm 2, C_XOR = O(n)).
- Thm 4: no O(|C|^{2-eps}) rewrite OR->SUM or OR->XOR unless SETH fails.
- Thm 5 (Mehlhorn-Pippenger): (s,t)-free A gives C_OR(A) >= |A|/(st). Cited, not re-proved.
- Conjecture (Sect 1.1): all non-trivial gaps among OR, SUM, XOR are n^{1-o(1)}. Only about those three linear models.
- Relevance: XOR cancellation beats OR, but only on dense matrices, not on (1,1)-free ones. Not C4.

## 2. arXiv 1305.3041 (Boyar, Find) - TXT (whole text)
- Model: XOR, cancellation-free XOR (= OR-like), OR circuits; size = gates.
- Lemma 1 (Nechiporuk, Mehlhorn, Pippenger, Wegener): k-free A gives C_OR(A) in Omega(|A|/k^2).
- Thm 4: lambda(n) = max C_OR/C_XOR in Omega(n/log^2 n), also for constant depth >= 2 (Sect 5). Thm 1, 2, 3 (Morgenstern), Prop 2: supporting.
- Sect 7 open problem: does cancellation help for the Sierpinski matrix (OR / cancellation-free need >= n log n / 2)? Not C4.

## 3. arXiv 2512.19515 (Cavalar et al.) - PART (abstract, Sect 1, 1.3, Sect 2-4 skimmed by grep; proofs not read)
- Thm 1.1: polynomial P_n (expander graph) with a SigmaPiSigma circuit of size O(n^3), monotone arithmetic size 2^{Omega(n)}. Thm 1.2: constant-degree k version, (n/k)^{Omega(k)}.
- Thm 1.4 (mixed separation, as stated in Sect 1.3 only); Thm 1.5: monotone Boolean f in uniform NC^2 with monotone size 2^{n^{1/3-o(1)}}.
- Boolean functions are span-program / matroid / code-based, NOT sums. Negation = one subtraction gate in the arithmetic setting.
- Open problems (Sect 1.3): monotone rank programs, planar matching, constant-depth separations. Nothing on Boolean sums.
- Use for C4: only as a caution that negation can help a lot on other functions. Nothing on (1,1)-disjoint sums.

## 4. Kyoto kokyuroku 0906-11 - TXT, SAME PAPER as LITERATURE row 38
- Repository metadata (hdl 2433/59458): Tsukiji, "Circuit Complexity of An Explicitly Defined First Slice Function", RIMS Kokyuroku 906 (1995) pp 81-88, file 0906-11.pdf. Row 38 is the same paper.
- Added vs row 38: the intro (p 81) says constant-slice functions have C_{OR,AND}(f) = Theta(C_{OR,AND,NOT}(f)) and "this relation, generally, does not hold for a Boolean sum". No proof or example given in the readable text (the example after "e.g." is garbled in extraction).
- Intro also notes explicit Boolean sums have nonlinear MONOTONE lower bounds via (s,t)-disjointness. This is not a non-monotone upper bound and not a refutation of C4.

## Conclusion
- No source states C4 as a conjecture or proves or refutes it. Closest prior statement remains Jukna-Sergeev 2013 sect 7 (a question).
- Gap: nobody here treats AND/OR/NOT circuits for (1,1)-disjoint sums. Only Wegener 1987 Sect 6.6 (monotone) is relevant.
- Files edited: research/LITERATURE.md rows 179-182 (replaced), boards/tasks/literature-c4.md Lines. No commit.
