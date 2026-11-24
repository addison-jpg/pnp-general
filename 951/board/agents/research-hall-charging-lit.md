# Literature search: Hall / charging templates for the D-shape

Date: 2026-11-24. Public sources only. Status labels: OPENED-IN-FULL, PARTLY READ, SNIPPET-ONLY, NOT OPENED.

## Summary (5 lines)
1. Best printed template: Pippenger 1980, Lemma 1 (opened in full): edges of a target graph F are charged to "eligible" edges of the circuit G lying on a-to-b paths, at most t^2 per edge; each F-edge needs at least one.
2. Second: Wegener 1987, Lemma 6.1 / Theorem 6.2 (Ch. 6.6, opened in the sections quoted): count gates with more than k summands; each gate is "useful for" at most h outputs (integral, shared-gate multiplicity h).
3. Jukna draft (bool-V7, sec. 13.6, Thm 13.21 and 13.27) restates Pippenger's charging; its numbering is draft numbering and was not checked against the printed 2012 edition.
4. None of these source texts contains a fractional Hall / transportation lemma with unit gate capacity and a first-two-merges exclusion. The D-shape is a new combination; these supply only the cone-restricted, capacity-bounded charging pattern.
5. Nechiporuk 1969, Mehlhorn 1979, Galil/Mehlhorn 1976 were not opened; they are only cited via Wegener and Jukna.

## Source table

| # | Source and exact statement | Status | Charging shape | Difference from D-shape |
|---|---|---|---|---|
| 1 | Pippenger, "On another Boolean matrix", TCS 11 (1980) 49-56, Lemma 1: if F has no K_{t+1,t+1} then L(F) >= #(F)/t^2. Lemma 4 (AND-gate elimination, L*(F) >= L(F)/max{t-1,1}); Thm 1-4 apply it. PDF at web.vu.lt/mif/s.jukna/boolean/Pippenger.pdf | OPENED-IN-FULL (extracted text, pp. 50-56; construction and Thm 1-2 proofs only skimmed) | Accounting scheme: an F-edge (a,b) is charged to ALL eligible G-edges on a-to-b paths. Eligible = at most t inputs reach the tail and at most t outputs reachable from the head. (I) each G-edge receives <= t^2 charges; (II) each F-edge is charged somewhere (proof by the initial/final segment argument). | Integral and many-to-many (one demand charged to every eligible gate, no unit split). Capacity t^2, not 1. Cone restriction is present (path a to b = the cone) and is the closest match. No "skip first two merges" rule; eligibility is by fan-in/fan-out counts. Existence (II) is proved by a monotone-segment argument, not by Hall. |
| 2 | Wegener, The Complexity of Boolean Functions (1987), Ch. 6.6: Def. 6.1 ((h,k)-disjoint), Lemma 6.1 (bound sum ceil((s_i-1)/(k-1)) - 1 over i, divided by h-1... as printed: (1/h) times sum of (ceil((s_i-1)/(k-1))-1) <= C_{OR}(f)), Theorem 6.2 (same bound for C_m with h' = max{1,h-1}), Cor. 6.1, Cor. 6.2. Free PDF web.vu.lt/mif/s.jukna/boolean/blaues_book.pdf | OPENED-IN-FULL for sec. 6.6 text (pp. 163-167 extracted); rest of book not read. Exact printed fraction in (6.1) was garbled by text extraction, so quote it from the PDF before citing. | Output f_i needs >= ceil((s_i-1)/(k-1)) OR-gates computing sums of more than k variables, minus the first ones; each such gate serves at most h outputs, so total count is divided by h. Pure double counting. Thm 6.2's AND-gate replacement uses the "given for nothing" sums of <= k variables (similar in spirit to excluding early merges). | Integral, shared-gate multiplicity bounded by a combinatorial design parameter (h), not by capacity 1. No flow/Hall step; the count is a single inequality. The "first merges are free" idea appears only as the (k-1) discount. Cone restriction is implicit (gate serves an output only if it is below it). |
| 3 | Jukna, Boolean Function Complexity (Springer 2012), sec. 13.6 "Circuits with OR gates: rectifier networks"; in the draft bool-V7: Thm 13.21 (k-free A needs >= |A|/k^2 wires, proof credited to Pippenger 1980), Claim 13.22, Thm 13.27 (C_{and,or}(f_A) = Omega(|A|/k^3)). TOC.pdf lists sec. 13.6 on printed p. 386. | PARTLY READ: sec. 13.6 read from the public early draft bool-V7.pdf; printed edition theorem numbers NOT verified; 2nd-edition draft is password-protected and was not opened. | Same eligible-wire charging as Pippenger, restated with s_w, t_w (inputs reaching w, outputs reachable from w); proof that every 1-entry has an eligible wire on its path. | Same differences as row 1. Useful as a modern citable restatement; cite as "Jukna 2012, sec. 13.6" only after checking the printed numbering. |
| 4 | Nechiporuk (1969) rectifier-network / Boolean-sum bound Omega(n^{3/2}); Mehlhorn, "Some remarks on Boolean sums", Acta Inf. 12 (1979); Galil-Mehlhorn, Computing 16 (1976) | NOT OPENED. Only seen as citations inside sources 1-3 (Wegener p. 163: Mehlhorn generalizes Nechiporuk and Wegener 1980; Jukna 13.6) and one search result listing. Do not cite for content. | Unknown beyond what sources 2-3 attribute. | Unknown. |
| 5 | Jukna Boolean sums / fractional-Hall material in the 2nd-edition draft | NOT OPENED (password protected). A web search found no public statement. | n/a | n/a |
| 6 | Gate-elimination / negation-limited literature: arXiv 2602.17942 (Carmosino, Dang, Jackman, convergent gate elimination); Kyoto negation-limited circuit papers; arXiv 1506.04485 (inversion complexity) | arXiv 2602.17942: PARTLY READ (first 100k chars, abstract and Thm 18/19 region via summary); others SNIPPET-ONLY (search result titles) | Substitution-based gate elimination (at least 3 gates removed per step); no charging, Hall or flow lemma was found in what was read. | Not a template for the D-shape. |
| 7 | Search for "fractional Hall" / "transportation lemma" in gate elimination or monotone lower bounds | Two web searches, no relevant hit | none | No citable source found; absence of a hit is not evidence of absence. |

## Best template candidate

Pippenger 1980, Lemma 1 (proof, pp. 50-52), with Jukna sec. 13.6 / Thm 13.21 as a textbook restatement.

Why: it is the only opened source that (a) assigns each demand to gates inside the demand's own source-to-target path set (a cone-like restriction), (b) bounds the load per gate by a fixed constant, and (c) proves coverage by a separating-vertex contradiction. Mapping to the D-shape: demand = merge-tree gates of a set S beyond its first two; admissible gates = output cone of S minus every set's first two merges; load cap = 1. To get from Pippenger's scheme to the D-shape one needs two changes that the source does NOT supply: replacing "charged to all eligible gates, load <= t^2" by "routed fractionally or integrally with load <= 1" (a Hall or max-flow statement), and proving the Hall condition from the circuit structure. Treat Pippenger Lemma 1 as a template for the accounting format only, and prove the Hall/flow condition directly.

Fallback: Wegener Lemma 6.1 if the argument can be made a pure double count (each gate useful to at most h sets).

## Caveats
- Printed theorem numbers for Jukna are unverified; Pippenger and Wegener (free PDF) numbers were read from the text.
- Text extraction garbled some formulas in Wegener Lemma 6.1; check the displayed (6.1) in the PDF itself.
- Mehlhorn, Nechiporuk, Galil papers were not read.
