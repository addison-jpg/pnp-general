# Which restricted exact-size rows generalize up the NOT gate ladder

Written by a Sonnet helper of Generalize (card rank 4), 2026-11-24; spot-read by Generalize, not verified row by row. Read-only survey: no Lean was run or edited. Everything about the
repository comes from reading statements (final `theorem` of each file, extracted by script) and, for a few rows, proofs.
Everything marked UNVERIFIED was not checked.

## 0. The key observation about the ladder

`HasCircuitSize n f s` (Defs/MetaComplexity.lean) counts every gate and puts NO bound on NOT gates. So a row stated with
`HasCircuitSize` is already on the top rung (`SIZENot s s`, any number of NOTs). Only rows with an explicit hypothesis are
lower rungs: `Monotone2 C`, `IsMonotoneCircuit C`, "no gate with op = not", or `Set.ncard {NOT gates} <= t`. Roughly 130 of the ~350
rows mention `HasCircuitSize`; the rest are monotone / structural / finite-computation rows. `SIZENot` itself is used only in
`General/` (L003, L004, Gaps) and in the few-NOT rows of section 2.F; no exact-size row is stated with `SIZENot`.

Consequence: the "restricted" exact-size work here is mostly NOT restricted in the ladder sense. It is restricted in the
FUNCTION class (edge functions of sparse graphs, AND/OR gadgets, parity, small named functions).

## 1. Table of rows

Rung: TOP = NOT counted, any number (statement over `HasCircuitSize`); MONO = monotone circuits only; FEW = at most t NOTs
(each applied to a monotone wire); "any #NOT: yes" means the printed statement already quantifies over all circuits.

| Rows | One-line statement | Rung | Holds for any #NOT? |
|---|---|---|---|
| L011, L012, L098 | function depending on n inputs needs >= n-1 gates; OR_n has size exactly n-1 | TOP | yes |
| L014, L018, L174 (gate_elim) | fixing a dependent input saves 1 gate (L014/L174: needs nonconstant restriction); L018: fixing k inputs costs <= +1 | TOP | yes |
| L020, L025, L031, L026 | parity_n: >= 2(n-1), 3(n-1), 4(n-1); upper 4(n-1). L031 is Red'kin's bound with NOT counted | TOP | yes |
| L174 | C(x AND f) = C(f)+1 for fresh x, f nonconstant | TOP | yes |
| L175, L176 | substituting AND/OR of two fresh vars for the last variable of g (g depends on it): +1 exactly | TOP | yes |
| L153 | C((a AND b) OR g(fresh)) = C(g)+2, g nonconstant | TOP | yes |
| L542-L547, L544/545, L653/654, L571-576 | C(g OR (v AND x_new)) between C(g)+1 and +2; with two fresh vars (v AND (w OR u)): exact +3 under side conditions; path gadgets +d, +2h | TOP | yes (exactness needs side conditions) |
| L567 | C(MAJ(X,a,b)) = C(X)+4 for nonconstant X, fresh a,b | TOP | yes |
| L-gen-005/006 (General/) | C(x XOR f) >= max(C f, C not f)+3; = min+4 when C f != C not f | TOP | yes, by construction |
| L716 | C(x XOR g) <= C(g)+4 and <= C(not g)+4 | TOP | yes (upper) |
| L195, L199, L200, General/NegLiteral | C(not x OR g) <= C(g)+2 (L195); L199: if g ignores p, size(not x_p OR g) = s+1 gives size(g) = s; NegLiteral: C f+1 <= C(not x AND f) <= C f+2 | TOP | yes |
| L589, L590, L591, L592, L627 | Shannon-type upper bounds: two wires F\|x_i=0, F\|x_i=1 of s gates give F with s+4 (L627: s+8); L591 identification costs 0, L592 negated identification +1 | TOP | yes (upper bounds) |
| L102, L106 | edge function of path P_n: n + floor(n/2) - 2 exactly; cycle C_n (n>=5): n + ceil(n/2) - 1 exactly | TOP | yes |
| L104, L105 | forests: every circuit >= \|E\|+tau-1; every graph with an edge has circuit \|E\|+tau-1 (tau = vertex cover) | TOP | yes (so forests are exact) |
| L204, L532, L376, L388, L468, L522, L553, L558, L559 | girth>=7 and hub distance >=7 (L532: "peelable"): edge function OR extra vars OR g needs >= \|A\|+\|E\|+tau-1 (+C(g)+1); L558 exact additivity | TOP | yes |
| L113 | on girth>=9, hub distance>=9 graphs every circuit for the edge function has a NOT-free circuit no larger | TOP -> MONO | yes; it says rung 0 = top on this class |
| L115, L154, L201, Helpers/NotFreeCor | monotone circuits: girth>=9, hubs >=7: size >= \|E\|+tau-1; L154 monotone upper bound; L201 structure of monotone circuits | MONO | no (hypothesis: no NOT) |
| L100, L112, L138, L139, L140, L746-L763, L902/903/917, L514-L528, L550, L517, L722, L609, L611, L671, L1003, L1004, L657 | exact sizes of single small functions (3-11 inputs), mostly "<= s iff k <= s" proved by finite computation; L140 (x0x1 OR not x2 = 3) and L671 (11) are non-monotone targets | TOP | yes |
| L_meta_168-171, L568, L588, L596, L658, L194, L534 | structure of MINIMAL circuits: if fixing x_n saves at most 1, then x_n has one reader, an OR (x=0 side) or AND (x=1 side); chains for x OR H. L588/596/658 assume the "free-input chain" statement as a hypothesis | TOP | yes, but L588/596/658 conditional |
| L_meta_150, 152, 265, 267, 282, 598-601, 603, 610, 724, 597; L402, L629, L649, L663 | counts of AND gates or of OR gates, line-degree, low merges, in MONOTONE circuits for edge functions / incidence functions | MONO | no, and the AND/OR-type counts are false with NOTs (section 2) |
| L_meta_270, 669, (708, 709, 713 as hypotheses) | monotone: sum of c_i <= size for a family of OR-of-sets with pairwise overlap <= 1; constant restriction preserves monotone circuits | MONO | no |
| L745, L_meta_885, 890, 894, 899, 900 | few-NOT conditionals: with <= t NOT gates, each applied to a MONOTONE wire, a family of 91 ORs over a projective-plane-like set system (t=3) needs >= 108 gates; assume 270/669-type statements | FEW | rung k, restricted form |
| L_meta_951 (not in this repo's rows) | rung 1: one NOT saves nothing on Boolean sums | FEW (t=1) | open (`no_minCE`) |

## 2. Natural generalizations and classification

Tools: `se` (semantic elimination), `block`, `count_main`, `restrict_one` (fixing a dependent input saves 1, either constant),
`restrict_three` (F flips with last input: C(F) >= max(C F|0, C F|1)+3), `neg_and_lower/upper`. Classes: (a) follows directly,
(b) plausible, needs a new argument, (c) false or blocked.

**A. Rows already on TOP (most of the table).** Nothing to generalize up the ladder. What is left is generalization in the
function class:

| Row | Generalization | Class | Why |
|---|---|---|---|
| L174 (x AND f) | x OR f: C = C(f)+1 | (a) | `restrict_one` with c=false on F = x OR f: restriction is f (nonconstant, F depends on x), so C(F)-1 >= C(f). Upper bound: one OR gate. Not found as a row (grep of statements; not exhaustive). |
| L174 | not x OR f in [C f+1, C f+2] | (a) | `restrict_one` with c=true gives g restricted = f, so >= C f+1; upper = L195. |
| NegLiteral (not x AND f) | exact value | (b) | Conjecture C(not x AND f) = min(C f, C not f)+2. Upper bound: not x AND f = not(x OR not f), so C(not f)+2; lower bound only max(C f+1, C(not f)) is available. Checked by hand on f = y, not y, y AND z, not(y AND z): consistent. Not a proof. Testable with the SAT tools in `tools/xor-extension/`. |
| L175/L176 + L-gen-006 | C(X XOR (a AND b)) = min(C X, C not X)+5 when C X != C not X (same for OR) | (a) | Compose: g(y,z) = X(y) XOR z depends on z, L-gen-006 gives C(g) = min+4, L175/176 add exactly 1. |
| L175/L176 | read-once AND/OR formula phi over k fresh variables: C(g[z := phi]) = C(g)+k-1 when g depends on z | (a), induction | Iterate L175/176 on leaves; needs variable-permutation invariance of C (L_meta_591-style lemma). |
| L-gen-005/006 | f XOR (x_1 XOR ... XOR x_k) >= max(C f, C not f)+3k | (a) | `restrict_three` on the last input; each branch is (x_1..x_{k-1} XOR f or not f), both have the induction bound. Upper bound min+4k (L716 iterated). Exact only for f a parity (L031). |
| L-gen-006 | C(x XOR f) = min+4 when C f = C not f | (b) | OPEN, finite evidence in `generalize-xor-extension.md`. |
| L567 (MAJ(X,a,b)) | other 3-variable gadgets G(X,a,b): full table of C(G(X,a,b)) - C(X) | (a) for those built from AND/OR/XOR with fresh pairs via 174/175/176/006; (b) for the rest | A table with 2 fresh variables has few classes (10 non-degenerate functions of (X,a,b) up to symmetry); not checked class by class. |
| f XOR g, disjoint variables, both nonconstant | C(f XOR g) = min(C f, C not f)+min(C g, C not g)+4 | (b) | Consistent with XOR_n = 4(n-1) and with L-gen-006 (g = a variable). Not tested. Additivity C(f AND g) = C f + C g + 1 for disjoint variables is the same kind of direct-sum statement; L558 proves it only on the edge-function class. For general f, g I do not know whether it is true: UNVERIFIED. |
| L204 etc. | drop girth/distance 7 | (c) | FALSE for the 4-cycle: (x0 OR x2) AND (x1 OR x3) has 3 gates, |E|+tau-1 = 5 (note-1). Girth 5 and 6 with hubs: untreated; the proof's graph lemma (good leaf or run) is where 7 enters. |
| L113 | class 9/9 -> 7/7 | (a) | Reading the proof: lower bound is `L204` (needs only 7/7, the `le_trans (by norm_num)` steps weaken 9 to 7), upper bound is `nfc_edge_upper_mono` (needs only an edge). So the same proof gives the NOT-free normal form under 7/7. Not compiled. |

**B. Monotone-only rows (rung 0).**

| Row group | Natural generalization | Class | Why |
|---|---|---|---|
| AND-count / OR-count rows (150, 152, 265, 267, 282, 598-601, 603) | same counts for circuits with NOTs | (c) | As stated they are false with NOT: x OR y = NOT(AND(NOT x, NOT y)) has zero OR gates, so "at least k OR gates" cannot survive. Only total size (or size with a type-invariant weighting) can generalize; L204/L104 are the total-size versions. L_meta_192 is a checked pair of 7-gate circuits with NOTs placed differently, same function. |
| Structure of monotone circuits (L610, L629, L649, L663, L402, L201, L724) | NOT-free normal form | (a) where L113 applies, (c) / (b) elsewhere | L113 turns a TOP circuit into a MONO one of no larger size, so any MONO lower bound on size transfers to TOP for the 9/9 (and, per the entry above, 7/7) class. For classes without a TOP lower bound (incidence functions of L649/L663, the 8-vertex graph of L724) this is the real open step, i.e. the ladder problem itself. |
| L115 (MONO lower bound for girth>=9, hubs >=7) | TOP | (a) | Already: L204 is the TOP version for 7/7, so L115 is a corollary class-wise. |

**C. FEW-NOT rows (L745, 885, 890, 894, 899, 900).** They assume each NOT gate reads a monotone wire and are conditional on 270/669/708/709/713.
Generalizing to NOT on arbitrary wires is (b): the repository's own note (research-lit-unrestricted.md section 8) says Amano-Maruoka (SICOMP 2005,
theorem read in the 1998 RIMS version) reduce t NOTs to a cover by 2^{t+1}-1 monotone functions, which is a different mechanism from the one used
here. Not read here in detail. `se`/`block`/`restrict_*` do not help: they handle gate-level elimination, not the monotone-wire restriction.

**D. Rung 1 (L-meta-951).** Nothing from `se`/`block`/`restrict_*` applies directly: "one NOT saves nothing on Boolean sums" is not a gate-elimination statement.

## 3. Literature (what I actually read)

| Source | Claim | What I read |
|---|---|---|
| Carmosino, Dang, Jackman, "Simple Circuit Extensions for XOR in PTIME", arXiv 2511.16903 (21 Nov 2025) | FPT algorithm for the f-Simple Extension Problem (optimal circuits linear size, polynomially many, bounded fan-out); XOR_n satisfies this; characterizes optimal XOR_n circuits with NOT free; states that with NOT counted, Kombarov (2011) showed optimal XOR_n circuits are binary trees of n-1 (not)XOR_2 subcircuits | arXiv abstract page via WebFetch (tool-paraphrased abstract). Full text NOT read. It proves nothing like C(x XOR f) >= max(C f, C not f)+3 for arbitrary f, as far as the abstract says. |
| Carmosino, Dang, Jackman, "Convergent Gate Elimination and Constructive Circuit Lower Bounds", arXiv 2602.17942 (20 Feb 2026) | generalizes Schnorr's XOR_n >= 3(n-1) in the DeMorgan basis (NOT free); Theorem 18; says nothing on Red'kin's 4(n-1) in the portion read | first 100k of 128k characters via WebFetch summarizer; NOT the whole paper, not checked for exact-extension lemmas. Possibly relevant to `se`; UNVERIFIED. |
| Schnorr 1974, "Zwei lineare untere Schranken fuer die Komplexitaet Boolescher Funktionen", Computing 13(2) | XOR_n needs 3(n-1) over DeMorgan basis (NOT free) per the 2602.17942 attribution | secondhand only. The "2n-3 / 3n-3" figures from the task: 3(n-1) for XOR is supported; "2n-3" NOT verified; a search snippet says Blum 1983 reports a gap in Schnorr's 3n proof for Paul's function (UNVERIFIED, one snippet). |
| Red'kin 1973, "Proof of minimality of circuits consisting of functional elements", Systems Theory Research (Problemy Kibernetiki), pp. 85-103 | minimality of XOR circuits; the figure 4(n-1) with NOT counted is the standard attribution (also in the repo note) | existence and bibliographic data confirmed by a search result for the Springer chapter. The value 4(n-1) is NOT confirmed from the source: UNVERIFIED. A 2025 arXiv paper (2509.13966; search summary only) credits Red'kin with optimality of the 5n-3 ripple-carry adder over the full binary basis, a different statement. The repository itself proves 4(n-1) (L031), so this does not block anything. |
| Kombarov 2011 | optimal XOR_n circuits are trees of XOR_2 blocks, NOT counted | only via the 2511.16903 abstract: UNVERIFIED primary source. |
| Ilango 2020 | ETH-hardness of partial MCSP via the f-Simple Extension Problem with f = OR_n | only via the 2511.16903 abstract. A direct search returned a different Ilango paper (FOCS 2023, random oracle); I did not find the 2020 paper: UNVERIFIED which 2020 venue/title. |
| Kulikov, Pechenev, Slezkin, "SAT-based Circuit Local Improvement", MFCS 2022, arXiv 2102.12579 | local SAT search for smaller subcircuits; upper bounds for symmetric functions; exact synthesis feasible for s <= 6 in seconds, 7-12 in days, 13+ out of reach | search summary of the abstract. Not about lower-bound theorems. Matches the repo's `tools/xor-extension/` limits (exact m <= 7). |

No source found stating `C(x XOR f) >= max(C f, C not f)+3` for arbitrary f, or the fresh-literal rows of section 2.A. Weak evidence of novelty (few queries, no full texts).

## 4. Top 5 next rows (value per Lean work)

1. **NOT-free normal form at 7/7.** For G with every cycle of length >= 7 and any two distinct vertices of degree >= 3 joined only by walks of length >= 7: every fan-in-2 circuit C computing the edge function has a NOT-free fan-in-2 circuit D with the same function and D.size <= C.size. Together with L204 (A empty) and L154/L105 this gives C_top(f_G) = C_mono(f_G) = |E|+tau-1 on the class. Work: copy L113 with weaker hypotheses (about 10 lines, no new mathematics). (Hand-checked reading only.)
2. **Fresh literal table.** For nonconstant f on n variables and fresh x: (i) C(x OR f) = C(f)+1; (ii) C(f)+1 <= C(not x OR f) <= C(f)+2. Proof: `restrict_one` with c=false (i) / c=true (ii) for the lower bounds; the upper bounds are one gate (i) and L195 (ii). About 40 lines, patterned on NegLiteral.lean. Completes the table started by L174 and NegLiteral.
3. **Read-once substitution.** For g on n+1 variables depending on its last variable z, and phi a read-once AND/OR formula with k >= 1 distinct fresh leaves: C(g[z := phi]) = C(g) + k - 1. Corollaries: C(X XOR phi) = min(C X, C not X) + k + 3 when C X != C not X, and C(MAJ-type gadgets) with wider fresh blocks. Work: induction on phi using L175/L176 and a variable-permutation lemma. About 80-120 lines.
4. **XOR with k fresh variables, lower bound.** For nonconstant f: C(f XOR x_1 XOR ... XOR x_k) >= max(C f, C not f) + 3k, by induction with `restrict_three` (both branches are of the same form). Upper bound min+4k from L716 iterated. States the gap (3k versus 4k) that L031 closes only for parities; the open exactness question is then sharply posed. About 60 lines.
5. **Duality lemma.** For a circuit C with gates AND/OR/NOT, swapping AND and OR gives a circuit of the same size for f^d(x) = not f(not x); so C(f^d) = C(f). Needed formally by the note's class reductions and by any symmetric treatment of `restrict_three` (c = 0 versus c = 1), and it yields C(not x OR g) = C(not x AND g^d) from NegLiteral for free. About 60 lines (wire induction); `Outside/L_meta_193` has the wire lemmas.

Not recommended now: the exact value of C(not x AND f) and the disjoint-variable XOR/AND direct sum (both (b), no proof idea beyond the stated conjectures); any generalization of the AND-count / OR-count rows (false with NOT).

## 5. What I did not check

- No Lean was compiled; classification of rows rests on the statements of the final theorems (scripted extraction, some truncated) and on skimming proofs of L031 (Helpers/Parity4), L113, NegLiteral. For most rows the rung is read from the statement, not from the proof.
- Rows I did not open beyond the statement: L_meta_885-900/L745 internals, L724, all of L514-L528 certificates, L402/L629/L649/L663 beyond docstrings.
- Whether "x OR f = C(f)+1" and "not x OR f" already exist under some other row number (grep of statements only).
- All literature items marked UNVERIFIED above; no primary source (PDF) of any cited paper was read in full.
