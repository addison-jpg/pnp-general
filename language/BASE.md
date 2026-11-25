# Language: what can be proved of it

Source: Addison, 2026-11-25 (`ontology/SOURCES.md`): give asteroid its own Qwen; prove what can be proved of language.
Code: `language/check.py` (standard library, exact). Programs: `language/language.ath`, `frames_language.ath`, `language/propose_demo.ath`. Level: `language/level.json`. Fingerprints: `language/fingerprints.json`.

Words: fact, checked-finite, checked-infinite (written reduction), tested, proposed (model output, never a result), analogy, open.

## a. The Chomsky hierarchy, exactly

What is checked. Every DFA with k = 1, 2, 3 states over {a, b} (start state 0, every transition table, every accepting set: 2 + 80 + 5832 machines). For each, its verdict on all 511 strings of length <= 8.
- No such DFA accepts exactly the strings a^n b^n among those 511. Checked-finite.
- The worst first disagreement (the longest a DFA can agree before it errs) is 1, 2, 4 for k = 1, 2, 3. Checked-finite.
- Distinct languages, restricted to length <= 8, of DFAs with <= k states: 2, 26, 1054. Checked-finite.
- Every k (checked-infinite, written reduction). Take a DFA with k states. Of the k + 1 prefixes a^0, ..., a^k, two reach the same state: a^i and a^j with i < j <= k. Then a^i b^i and a^j b^i get the same verdict. Exactly one of them is in a^n b^n. So the DFA errs on a string of length i + j <= 2k - 1. The check confirms the bound for k <= 3 (1 <= 1, 2 <= 3, 4 <= 5). This is the pumping lemma's argument (Rabin, Scott 1959; Bar-Hillel, Perles, Shamir 1961; cited, not re-read). It shows a^n b^n is not regular.
- Grammars. S -> aSb | e makes one string at each even length, none at odd, n = 0..16, one parse each. S -> (S)S | e makes exactly the balanced strings: compared with brute force over all 2^n strings, n <= 12; counted by the grammar to n = 16. Balanced strings of length 2m: 1, 1, 2, 5, 14, 42, 132, 429, 1430 (Catalan, m = 0..8). One parse each, so the grammar is unambiguous on these lengths. Checked-finite.

## b. Ambiguity counted exactly

- E -> E+E | E*E | x. Every sentence with n operators (all 2^n choices of + and *) has Catalan(n) parse trees, n = 0..8. Counted by a chart; trees listed one by one and found distinct for n <= 6. Checked-finite.
- Every n: a tree is a root operator with a parsed left part and a parsed right part. That gives C(n) = sum C(i) C(n-1-i), the Catalan recurrence. Checked-infinite (written reduction, in `level.json`).
- The precedence grammar E -> E+T | T, T -> T*F | F, F -> x gives exactly 1 parse to every sentence, n = 0..8. Checked-finite. For every n it is the textbook result (the grammar is LR(1)); not written here. Open here.

## c. A Montague fragment

Sentences "Q1 student reads Q2 book", Q in {every, some}. Two readings: surface scope (Q1 outside) and inverse scope (Q2 outside). Evaluated exactly on every model with domain size 1, 2, 3 and every interpretation of student, book, reads: 8 + 256 + 32768 = 33032 models. Domains are non-empty.
- "every student reads some book". The readings differ. Smallest model: one element, no students, no books (surface true by vacuity, inverse false). Smallest with students and books non-empty: domain {0, 1}, both are students and books, reads = {(0,1), (1,0)}. Checked-finite.
- The inverse reading implies the surface one on all 33032 models. Checked-finite. Every model: if one book is read by every student, each student reads a book. Checked-infinite (one line).
- Readings per pattern: every..every 1, some..some 1, every..some 2, some..every 2. "Some student reads every book": surface implies inverse on every model. Checked-finite.
- Montague 1973 (The proper treatment of quantification in ordinary English) is cited, not re-read. The fragment is ours.

## d. Joins

- Ambiguity as qual-quant: a sentence that means more than one thing has a count. Here the count is exact: readings (1 or 2) and parse trees (Catalan(n)). The link to `ontology/QUALQUANT.md` is analogy.
- Catalan counts parse trees and also the ordered arbor shapes of `brain/neuron`. Checked as shapes, not only counts: erase the operators of the trees of x+...+x with n+1 leaves; the set equals the ordered binary shapes with n+1 tips, n = 0..6. The counts match the brain fingerprint on all 9 terms (`claim parses matches catalan`). Join, checked-finite. Every n: both are full binary plane trees with n+1 leaves. That is a definition, not a coincidence.

## e. Proposals: asteroid's own Qwen

`asteroid/ext_qwen.py` adds `propose NAME "TASK"`. The model guesses, asteroid decides (`asteroid/SPEC.md`).
Run once on 2026-11-25, `language/propose_demo.ath`, Qwen2.5-1.5B-Instruct, greedy, 3 candidates per task. Tested, model output:
- Catalan formula: 0 of 3 TRUE. All 3 REJECTED (not asteroid syntax: `C(n) = ...`, `binomial`, `^`).
- Segmental (2n-3)!!: 0 of 3 TRUE. All 3 REJECTED (not asteroid syntax).
- Modal formula for symmetric frames: 0 of 3 TRUE. All 3 parsed and were FALSE (tautologies like `p -> p -> p`; a countermodel on R = {(0,1)} was printed). The known answer is B, `p -> []<>p`, checked in `time/` and `metaphysics/`.
- Total: 0 of 9 passed. An earlier run with 0.5B gave 4 candidates, all REJECTED.
Outputs are cached in `asteroid/out/qwen_cache.json`, so a rerun prints the same verdicts at once. Nothing proposed became a claim or a record.
