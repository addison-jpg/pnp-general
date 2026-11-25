# The official Clay problem description, read against this repository

Board item "Next up 5". Read 2026-11-24 by session_01GmnDhgAdyDijthBgZgJFWn from
`https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf` (HTTP 200, 176,204 bytes, 12 pages):
Stephen Cook, "The P versus NP Problem", the Clay Mathematics Institute's official problem description.
It cites Agrawal, Kayal, Saxena (2004), so this version is later than the 2000 original.
Quotes are verbatim; everything else is a paraphrase or a comparison and says so.

## What the description fixes

- **Model.** A one-tape Turing machine `⟨Σ, Γ, Q, δ⟩` (Appendix): input alphabet `Σ ⊆ Γ`, blank
  `b ∈ Γ - Σ`, states `q0, q_accept, q_reject`, `δ : (Q - {q_accept, q_reject}) × Γ → Q × Γ × {-1, 1}`;
  the input is written on adjacent squares, the head on its left-most symbol.
- **Time.** `t_M(w)` is the number of steps; `T_M(n) = max{t_M(w) | w ∈ Σ^n}`; "M runs in polynomial
  time if there exists k such that for all n, T_M(n) ≤ n^k + k".
- **P.** "P = {L | L = L(M) for some Turing machine M that runs in polynomial time}", languages over a
  finite alphabet `Σ` "with at least two elements".
- **NP.** A checking relation `R ⊆ Σ* × Σ1*` is polynomial-time iff `L_R = {w#y | R(w, y)} ∈ P`;
  "a language L over Σ is in NP iff there is k ∈ ℕ and a polynomial-time checking relation R such that
  for all w ∈ Σ*, w ∈ L ⟺ ∃y(|y| ≤ |w|^k and R(w, y))".
- **The problem.** "Problem Statement. Does P = NP?"
- **Alphabet.** "the answer is independent of the size of the alphabet Σ (we assume |Σ| ≥ 2) ...
  (For |Σ| = 1 the problem is still open, although it is possible that P = NP in this case but not in
  the general case.)"

## Against `proofs/main/PEqualNP/Defs/Base.lean` (comparison, not a checked statement)

| Point | Clay (Cook) | This repository | Same class? |
|---|---|---|---|
| Machine | one-tape Turing machine | Mathlib `Turing.FinTM2` (finitely many stacks) | yes up to a polynomial simulation in both directions; standard, not proved in Lean here |
| Alphabet | any finite `Σ`, `|Σ| ≥ 2` | `Bool` (`Language Bool`) | yes: Cook's alphabet-independence remark; `|Σ| = 2` is the case stated |
| Time bound | `T_M(n) ≤ n^k + k` | a `Polynomial ℕ` bound (`TM2ComputableInPolyTime`) | yes |
| NP witness | `|y| ≤ |w|^k`, `y` over a second alphabet `Σ1`, pair coded as `w#y` | `w.length ≤ p.eval x.length`, `w : List Bool`, pair coded by `encodePair` over `Bool ⊕ Bool` | yes: for `|x| ≥ 2` some `|x|^k'` dominates `p`, and the finitely many shorter inputs can be hard-coded into `R`; `Σ1` codes into `Bool` |
| Statement | "Does P = NP?" | `P = NP` as sets of `Language Bool` | yes, given the rows above |

So a proof of `P ≠ NP` (or of `P = NP`) for the repository's definitions answers the official question,
provided the standard model equivalences above, which are not formalized here.

## What the description says that bears on the board

- Circuits (section 3, verbatim): "It is not hard to see that if L is a language over {0, 1} that is in P,
  then there is a polynomial-size family of Boolean circuits ⟨B_n⟩ ... Thus to prove P ≠ NP it suffices to
  prove a super-polynomial lower bound on the size of any family of Boolean circuits solving some specific
  NP-complete problem, such as 3-SAT." This is the route of L-gen-101.
- "Proposition 2. If P ⊆ LINEAR-SIZE, then P ≠ NP." (from Kannan: the polynomial hierarchy is not inside
  LINEAR-SIZE, and P = NP collapses it to P). Not yet a row here; it needs the hierarchy (cf. Next up 3).
- "Assertion A. There is L ∈ E and ε > 0 such that, for every circuit family ⟨B_n⟩ computing L and for all
  sufficiently large n, B_n has at least 2^{εn} gates." "Proposition 3. If A then BPP = P. If not A then
  P ≠ NP." (Impagliazzo–Wigderson; Kabanets.)
- Barriers named: relativization (Baker, Gill, Solovay), natural proofs (Razborov, Rudich), with the remark
  that "a nonrelativizing construction will be needed" for Proposition 3's route. Matches the board's
  barrier rows L-lib-061/062/086.
- Dated figures: "the best such lower bound proved so far is about 4n" (general circuits for explicit
  functions); the board's literature list has the later 5n - o(n) (De Morgan basis) and 3.1n - o(n).
