# LIT1: is "k NOTs need Sum(|S_w|-1) gates on (1,1)-disjoint Boolean sums" known, open or false?

Seat LIT1 (Sonnet), 2026-11-25. Target: Boolean sums f_w = OR of S_w with |S_a ∩ S_b| ≤ 1; every
circuit over AND/OR/NOT with at most k NOT gates has at least Σ(|S_w| − 1) gates. No P vs NP
implication is claimed.

## Verdict: OPEN (not known; no counterexample found)

**Superseded in part by the LIT2 section at the end of this file:** OPEN stands for k = 1 only; "every k"
is false for large instances, and reason (2) below misreads Jukna–Sergeev §7 (exact quote in LIT2 s2).

Reasons. (1) No source read or found proves any gate lower bound for Boolean sums with even one NOT
gate beyond the trivial n−comp for a single OR; the project's earlier 255-paper citation crawl
(`research-crawl`, LITERATURE.md §J) found none. (2) Jukna and Sergeev 2013 §7 ask the
AND/OR/NOT question for Boolean sums as a problem (read, TXT, per LITERATURE.md §A); Jukna's errata
page lists Problems 7.4 and 7.7 as solved but gives no statements, so whether the negation problem
is among them is UNCHECKED (the page fetched today names no negation result). (3) Nothing found
contradicts the target for k = 1 or general k: no known example where a NOT saves gates on a
(1,1)-disjoint sum.

Strongest source for "open": Jukna and Sergeev, FnTTCS 9(1) 2013, §7 (asks it). Strongest
source for "not known": absence in the 255-work crawl. Neither is a proof of absence.

## Source by source

| Source | What it proves | Read | Effect on target (k = 1 / general k) |
|---|---|---|---|
| Markov 1958 | ⌈log2(d(f)+1)⌉ NOTs suffice and are needed for a function; says nothing about size | TXT via Jukna Thm 10.5 | none / none; it counts NOTs, not gates |
| Fischer 1975 | log-many NOTs cost only polynomial overhead | TXT via Jukna 10.18 | none; shows few NOTs are not size-free in general, no lower bound |
| Amano-Maruoka (RIMS 1998 = SICOMP 2005) | size_t(f) ≥ min over t-NOT covers of the sensitivity graph by 2^{t+1}−1 monotone functions; function-level, asymptotic | TXT (1998) | leaves open: gives no exact gate count for sums |
| Amano-Maruoka-Tarui, DAM 126 (2003) 3-8 | merging with r NOTs: size Θ(n log n / 2^r), tight | ABS via search snippet | not Boolean sums; shows NOTs can save a factor on non-sum functions, consistent with open |
| Morizumi-Tarui-Iwama 2007; Morizumi (parity, inverters) | parity with few NOTs; accounting loses 1 gate per NOT | TXT (RIMS 1554) | no Boolean-sum statement; leaves open |
| Sung-Tanaka 1997/2002 | NOT removal can cost exponentially; inverter depth | ABS | leaves open |
| Blais-Canonne-Oliveira-Servedio-Tan 1410.8420 | t NOTs ⇒ PARITY of O(2^t) monotone fns; influence bound | TXT | function level; no gate count |
| Jukna-Lingas 2022 (negation width) | size ≥ monotone size / K − 1, multiplicative loss | TXT | gives only a constant-factor-lossy bound, NOT Σ(|S|−1) exactly; leaves open |
| Rossman CCC 2015 | correlation bounds, ~½ log n NOTs vs monotone NC1; asymptotic | CITED | no exact sum bound; open |
| Guo-Malkin-Oliveira-Rosen (negation-limited and pseudorandomness) | pseudorandom functions with few NOTs; not about sums | NOT read (named only) | does not apply |
| Jukna, BFC 2012, ch. 10 (negation-limited) | Markov, Fischer, Tardos-Razborov context | partly read (MEM) | no Boolean-sum k-NOT bound recalled; unverified |
| Wegener 1987 §6.6; Mehlhorn 1979; Pippenger 1980 | monotone case: OR-only optimal, Σ(|S|−1) exact | TXT (Wegener, Pippenger); Mehlhorn CITED | covers k = 0 only; the target is exactly its extension |
| Jukna-Sergeev 2013 §7 | asks if AND/OR/NOT helps for Boolean sums | TXT | OPEN for all k |
| Blum 2024 TR24-179 | ECCC abstract (fetched today) does not mention Boolean sums with negations; the earlier LITERATURE row claim rests on TLDR | ABS | the "lists it as open" claim is UNVERIFIED; downgrade |
| Tardos 1988; Razborov 1985; Alon-Boppana | monotone functions in P (Tardos, matching-type) needing exponential monotone size, so unlimited NOTs save exponentially | search snippets only | exponential separations use many NOTs and non-sum functions; they do not give a 1-NOT saving on a (1,1)-disjoint sum and do not contradict the target |
| Cavalar-Goos-Sofronova-Sokolov 2025 (arXiv 2507.16105) | matching: exponential monotone vs general gap | ABS | same: asymptotic, many NOTs |

## Does a known example show one NOT saves gates on monotone functions?

Yes in general: merging with r NOTs beats monotone by factor 2^r (Amano-Maruoka-Tarui), and
Tardos/Razborov-type gaps are exponential. None is a Boolean sum with |S_a ∩ S_b| ≤ 1; for such
sums the monotone optimum is OR-only and equals the target value. Tarjan 1978's 17 < 18 saving is
for non-(1,1)-disjoint sums with AND, still monotone. So no source gives a counterexample.
Razborov's matching gap does not apply (it needs unbounded NOTs and non-sum functions).

## Caveats and next reads

Not opened: Mehlhorn 1979, Amano-Maruoka full text on sums, Jukna ch. 10 text, Guo et al.,
Rossman full text, Jukna errata items 7.4/7.7 statements (to be sure the negation question was
not solved in 2017). Search is US-only web; publisher full texts were unreachable. Verdict is
"open to the best of this search", enough to forbid "known" but not enough to assert novelty
without those reads.

---

# LIT2 (Fable, 2026-11-25): errata, the exact Jukna–Sergeev question, and two redirects

Read status words as in LITERATURE.md. "Not opened" means the text was not reached; nothing is
inferred about it. No P vs NP implication is claimed anywhere below.

## LIT2 verdict (replaces the single word OPEN above)

| Statement | Verdict | Basis |
|---|---|---|
| k = 1 (`no_minCE`, `BoolSumNot 1`) | **OPEN**: not found in print, no counterexample | this search; LIT1 |
| "for every k" (`L105`, `∀ k, BoolSumNot k`; the card's "general k") | **FALSE for large instances** | two printed results put together by LIT2 (s3); paper, not in Lean, asymptotic |
| the point lemma for every family W (B6 s2) | **FALSE** | explicit program on AG(2,8), script-checked (s4) |
| Jukna–Sergeev §7 question | **not an open problem**: the authors answer it in the same paragraph | TXT, quote in s2 |

So the line "the flagship target answers a problem posed in print" is NOT added: the printed
question is about unrestricted gates, and print answers it against us.

## 1. Jukna's errata: Problems 7.4 and 7.7 (TXT, fetched today)

The "solved" list is not for *Boolean Function Complexity*. It is on the page of Jukna and Sergeev,
*Complexity of Linear Boolean Operators* (web.vu.lt/mif/s.jukna/Knizka/index.html). The BFC errata
(boolean/misprints-BFC.html) has no solved-problem entries; for ch. 10 it has two corrections
(Thm 10.5 should read I(f) = ⌈log(d(f)+1)⌉; Remark 10.20, Beals 1995).

- **Problem 7.4** (page problem-7.4.html, posted 15.04.2017): "Does L_d(m,n) ∼ mn/log(mn) hold for
  all log n ≪ m ≤ n and a constant d?" (SUM-circuits of bounded depth, Shannon function). Solved by
  I. S. Sergeev, "Rectifier circuits of bounded depth", J. Appl. Ind. Math. 12(1) (2018) 153–166:
  L_3(m,n) ≤ (1+τ) mn/log₂(mn). The paper itself was not opened (Springer); the page states the theorem.
- **Problem 7.7** (page problem-7.7.html, added 04.06.2017): solved affirmatively by Sergeev, on the
  page itself, with proof: XOR₂(A ⊞ B) ≥ XOR₂(A) + XOR₂(B) in depth 2, and N×N matrices with
  XOR₂(A)/XOR(A) ≽ N^{0.3}/log N (direct sums plus fast matrix multiplication; the argument is from
  Paul, TCS 2 (1976)). It is about depth-2 XOR circuits against unbounded depth.
- **Neither is the negation question for Boolean sums.** No AND, no NOT, no (1,1)-disjoint sums in
  either. The other comments on that page (comment1–4, 2014–2025) are about OR/XOR/SUM circuits;
  comment4 was opened (Problems 7.3, 7.5), the rest by title only.

## 2. Jukna–Sergeev 2013, §7: the exact text (TXT, authors' PDF Knizka/linear.pdf, pages as printed)

FnTTCS 9(1) (2013) 1–123, chapter 7 "Conclusion and Open Problems", **pp. 115–116**, right after
Problem 7.19. It is not a numbered problem. Verbatim (the PDF-to-text step drops overlines; the
complement bars are restored in brackets):

> "Note that Problem 7.18 concerns the power of non-linear gates when computing linear operators
> y = Ax over the XOR group. One can also ask a similar question for the OR semigroup: Do
> non-linear gates can help to simultaneously compute boolean sums? That is, if GENOR(A) denotes
> the smallest size of a general (not just OR) circuit simultaneously computing all the n ORs
> y_i = ∨_{a_ij = 1} x_j, how large can the gap OR(A)/GENOR(A) be?
> Results above imply that this gap can be almost maximally possible, can be as large as
> Ω(n/log³ n). This follows from the gaps (5.11) between the OR complexities of matrices and their
> complements, together with a simple observation that GENOR([Ā]) ≤ GENOR(A) + 2n. To see this
> upper bound, take a circuit for A (computing all ORs given by A). To obtain a circuit for [Ā],
> just add one gate computing the OR h of all n variables, and replace each output gate y_i by
> y_i ∧ ¬h. Important in this construction was that we allow NOT gates: Nechiporuk [74],
> Mehlhorn [64], and Pippenger [84] have shown that every circuit with only OR and AND gates for a
> (k + 1)-free matrix A must gave at least |A|/k³ wires."

What this is: (i) "general" = arbitrary Boolean functions as gates, size = wires, any matrix A;
nothing about few NOT gates, nothing restricted to 2-free A. (ii) The authors state the answer
(the gap is almost maximal). (iii) The construction "y_i ∧ ¬h" is wrong as printed (y_i ≤ h, so it
is the constant 0), as LITERATURE.md already says; the errata list has no entry for pp. 115–116.
(iv) The claim itself is true by another route, s3. The nearest numbered problem is 7.18 ("Do
non-linear gates help to compute F₂-linear operators?"), which is about XOR and is still listed
unsolved; it is not our target.

## 3. Redirect A: with many NOT gates the bound is false on large planes (print + two lines)

Printed ingredients, all TXT today:

1. Wegener 1987, §6.7, p. 168 (author's copy on Jukna's site, boolean/blaues_book.pdf): "Negations
   are powerful for the Boolean convolution. By the results of Ch. 3 we compute the Boolean
   convolution if we multiply the binary numbers x = Σ x_i 2^{ki} and y = Σ y_i 2^{ki} where
   k = ⌈log n⌉ + 1 [brackets restored; ...] can be multiplied by the method of Schönhage and Strassen with
   O(n log² n log log n) gates."
2. Jukna–Sergeev pp. 15–16: the point-line matrix P of PG(2,q), n = q² + q + 1, is 2-free with
   (q+1)n ones and (Singer) circulant: P[x,y] = 1 iff y = x + a mod n for some a ∈ S, |S| = q + 1.
3. Grinchuk–Sergeev, arXiv 1701.08557, §5: the cyclic Boolean convolution with the y-inputs fixed
   to constants is a system of Boolean sums with an arbitrary circulant matrix.

Consequence (LIT2, paper; not found stated in print, not in Lean): fix y to the indicator of the
Singer set in the circuit of item 1 and add n OR gates for the cyclic wrap. The n sums of PG(2,q)
(pairwise intersections exactly 1) have an AND/OR/NOT circuit with O(n log² n log log n) gates,
against base = n·q ≈ n^{3/2}. Hence:

- with no limit on NOT gates the bound Σ(|S_w| − 1) fails for all large q;
- pushing the NOT gates to the inputs (double rail, 2s + n gates, n NOT gates; the step is
  already in `workshop/notes/beyond-one-not.md` S4) gives failure of `BoolSumNot k` for k ≥ n, so
  **`L105 = ∀ k, BoolSumNot k` is false**;
- with the Beals–Nishino–Tanaka inverter (O(n log n) gates, ⌈log₂(n+1)⌉ NOT gates; DIMACS TR 95-31
  abstract seen through a search summary only, paper not opened) failure already at
  k = ⌈log₂(n+1)⌉.

Limits of this: asymptotic (the constant of Schönhage–Strassen is large; no instance at n ≤ 10⁴
is claimed); it says nothing for k = 1 or any fixed k. The same route with the O(log n)-free
circulant matrices of Grinchuk–Sergeev (weight Ω(N² log⁻³ N), OR-size Ω(N² log⁻⁵ N)) gives
OR(A)/GENOR(A) ≥ N/polylog N, i.e. the Jukna–Sergeev claim of s2 by a correct construction.
`beyond-one-not.md` S4 wrote "the statement may be false ... nobody knows whether it helps on
rectangle-free ones": for the top of the ladder this settles it (it helps, by ≈ √n/polylog).

Through the project's own implications (B5 Remark 2: classes ≤ AND/OR gates; B5: thin-basis ⟹
S3(b) for every circuit) this also makes **S3(b) "for every family, any number of NOT gates"
and the thin-basis lemma for every family false** on large Singer planes. Small systems are not
touched.

## 4. Redirect B: the point lemma is false for general families (explicit, checked)

`LIT2_point_counterexample.py`. Family: the q² non-vertical lines y = ax + b of AG(2,q), q = 2^m
(q² points, |S| = q, pairwise ≤ 1, base = q²(q − 1)). Leaves: vertical lines and single points
(checked to be partial transversals). Lines ∪, ∩, ∖ only. The program decodes the coordinates:
Y_t = points with bit t of y; unions of verticals for the F₂-linear forms of x;
D_{a,t} = Y_t ⊕ (bit t of a·x); S_(a,b) = the atom of the D_{a,·} with pattern b.

| q | points | sets | base | lines | |
|---|---:|---:|---:|---:|---|
| 4 | 16 | 16 | 48 | 56 | not below |
| 8 | 64 | 64 | 448 | **261** | every S_w among the lines |
| 16 | 256 | 256 | 3840 | **988** | every S_w among the lines |
| 32 | 1024 | 1024 | 31744 | **3671** | every S_w among the lines |

Each program is evaluated twice (bitmasks; frozensets recomputed from the recorded program; the two
agree and all q² targets appear as distinct lines). Lines grow like 2q² against base q³. This is
the weight ≤ 1 barrier of LITERATURE.md §B (Wegener's set circuits; Hiltgen–Paterson; Tsukiji) hit
by the point lemma, which reads a circuit only at 0 and the unit vectors. It is not a circuit
below base: ∩ and ∖ of point sets do not lift to inputs of weight ≥ 2.

By Lemma D as F1 states it (J = ∅, singleton classes: base ≤ number of lines), PHC@0 fails on
this program.

## 5. Mehlhorn 1979, Guo et al., Jukna ch. 10

| Source | Reached? | What can be said |
|---|---|---|
| Mehlhorn, Acta Inf. 12 (1979) 371–375 | **not opened** (Springer and MPI hosts blocked) | only through Wegener §6.6 (TXT): "The following results are based on Mehlhorn (79) who generalized the results of Nechiporuk (71) and Wegener (80)"; Lemma 6.1 / Thm 6.2 are monotone ({∨} and {∨,∧}). Nothing about NOT gates can be attributed to it from here |
| Guo, Malkin, Oliveira, Rosen, "The power of negations in cryptography" (TCC 2015) | **not opened** (eprint.iacr.org and iacr.org blocked) | nothing; the LIT1 row "not about Boolean sums" stays unverified |
| Jukna BFC ch. 10 | **table of contents only** (boolean/TOC.pdf): "10 The Mystery of Negations": 10.1 When are NOT Gates Useless? (10.1.1 Slice Functions, 10.1.2 Negated Inputs as New Variables), 10.2 Markov's Theorem, 10.3 Formulas Require Exponentially More NOT Gates, 10.4 Fischer's Theorem, 10.5 How Many Negations are Enough to Prove P ≠ NP? | no section title on Boolean sums; the text was not opened, so no statement is attributed |
| Grinchuk–Sergeev, arXiv 1701.08557 | TXT (intro, §5) | monotone lower bounds for circulant Boolean sums; used in s3 item 3 |
| Wegener 1987 §6.7 p. 168 | TXT | negations are powerful for Boolean convolution; s3 item 1 |

## 6. Who is affected

- **Flagship target statement.** Restrict it to k = 1 (or a fixed k, or k below a bound to be
  found); "general k" as "every k" is false (s3). The true threshold lies between k = 1 and
  ⌈log₂(n+1)⌉ and is unknown. The 2^k-lossy bounds (Amano–Maruoka, Jukna–Lingas) stay consistent.
- **The point lemma (B6, B9, B10; open-many-not).** False for general families (s4). The two-set
  forms (B9, F1's class point lemma for two sets) are not refuted; but no proof of them may extend
  to all families, so a proof must use "two sets" (or an acyclicity / sparsity hypothesis that
  AG(2,8) violates). As a route to S3(b) for all circuits it is closed.
- **F1 / PHC.** PHC@0 "for all point programs" is false (s4, via Lemma D at J = ∅). PHC can only be
  a theorem for a class of programs that excludes the AG(2,8) program: e.g. programs coming from
  circuits with at most one NOT gate, read at more than the point 0. Any PHC statement that is
  blind to the number of NOT gates is false on large planes by s3.
- **REF1.** A ready targeted instance: run Lemma D's inequality on the program printed by
  `LIT2_point_counterexample.py 3` (64 points, 261 lines). Random small instances cannot see s3
  (asymptotic) and need not see s4 (first failure found at q = 8; q = 4 gives 56 > 48 with this
  construction, smaller families not searched).
- **BottomPay / the k = 1 chain.** Not refuted by anything here. Constraint: the proof must use the
  one-NOT hypothesis and inputs of weight ≥ 2; an argument that would also run with n NOT gates,
  or only at 0 and unit vectors, proves a false statement.
- **`lean/PEqualNP/General/Gaps.lean` `L105`** (a `def`, nothing asserted): its docstring should
  say the statement is false for large k (not edited by this seat).
