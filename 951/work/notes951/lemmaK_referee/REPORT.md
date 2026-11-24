# Referee report: Lemma K (class count)

Referee: session_01GmnDhdwV8pW4adQkj9Ei3M (dwV8p), 2026-11-24. Source refereed: branch `scaffold-951`,
`work/notes951/lemmaK/README.md` and `extra_constraints.md` section 0. Checker: `kcheck.py` beside this file
(imports `tools/w951`; run from the `951/` directory).

## Verdict: CORRECT

Lemma K holds for every correct circuit with exactly one NOT, with no minimality assumption. K1 holds.
K2 holds given N2, which is in Lean. Its use of P2 can be replaced by a short self-contained argument (below).
Two wording fixes are recommended (W1, W2). Neither changes a statement.

## Line-by-line

Setting: `F = {S_w}` with `|S_w| >= 2` and pairwise `|S_w ∩ S_j| <= 1`; `C` computes every `o_w = OR(S_w)`
with AND/OR gates (fan-in at most 2) and exactly one NOT `N = ~h`. `h` lies before `N`, so `h` is a monotone
function of `x`. Every gate is a monotone function `G(x, N)` of `x` and the wire `N`.

- **Outputs.** `o_w` is a gate. It is not an input, because `|S_w| >= 2`. It is not `N`, because
  `N(0) = 1 != OR(S_w)(0)`. Outputs of different sets are different gates, because the sets are distinct
  (`|S_w ∩ S_j| <= 1 < |S_w|`). `o_w ∈ D_w ∩ P_w`.
- **(a) disjointness.** D_i ∩ D_j: the units of g lie in `S_i ∩ S_j`, and g has at least 2 of them,
  against linearity. P_i ∩ P_j: excluded by the definition of `P`. D_i ∩ P_j with i != j: then
  `OR(S_j) <= OR(S_i)`, so `S_j ⊆ S_i`, against `|S_j| >= 2` and linearity. Correct.
  The overlap D_w ∩ P_w within one set is harmless: Pi_w is their union.
- **(d) N in no class.** `N <= OR(S)` gives `N(0) = 0`, so `h(0) = 1`, so `h == 1`, `N == 0`, and N has no
  unit. `N >= OR(S)` gives `N(1) = 1`, so `h == 0` and `N == 1`, which is excluded from P. Correct.
- **(e) U meets no class.** Members of D have at least 2 units by definition. Members of P satisfy
  `g >= OR(S_w)`, so every `u ∈ S_w` is a unit. Correct.
- **(b) |Pi_w| >= min(d_w, 2).**
  - OR-top: both inputs are `<= OR(S_w)`, and they share the at least 3 units, so one input A has at
    least 2. A is not an input (at most 1 unit) and not N (N <= OR(S_w) forces N == 0). So A is a gate
    in D_w, earlier than `o_w`. This also covers `A = B` and fan-in 1. Correct.
  - AND-top: every wire in the AND expansion is `>= OR(S_w)`. (Simpler, from the Lean proof, session
    dZb2E: the two direct inputs A, B of `o_w` suffice. If neither is in P_w, each is `== 1` or
    `>= OR(S_j)` for some `j != w`, and two points outside `S_w` give the same contradiction.) Leaves that are inputs are impossible.
    **W1:** the text says "none is N, since N >= OR(S_w) forces N == 1". N == 1 is possible (h == 0), so
    N can be a leaf. The README's note (b) is the right reading: drop the leaves that are `== 1` (N or
    any other constant-1 wire) before choosing the points `u_G`. Then the contradiction at
    `x = OR_G e_{u_G}` goes through: `x` misses `S_w`, every remaining leaf is 1 at `x`, and the dropped
    leaves are 1 everywhere. At least one leaf remains, since otherwise `o_w == 1`. The remaining leaves
    are OR gates. Correct after W1.
- **(c) Theorem E for easy w.** `N(z_S) = 1` when `h(z_S) = 0`. So `g(z_S) = C1(g)(z_S)`, and `g(z_S) = 0`
  gives `g <= C1(g) <= OR(S)`: `C1(g)` is monotone and 0 at the largest point that misses S. Union-find
  invariant: the block `{u ∈ S : g(e_u) = 1}` of every wire with `g(z_S) = 0` lies in one component.
  - Inputs: `x_v` with `v ∈ S`, block `{v}`.
  - OR gate: both inputs are 0 at `z_S`, and the union merges them.
  - AND gate: one input is 0 at `z_S`, and its block contains the gate's block.
  - N: excluded, since `N(z_S) = 1`.
  - Constant gates (fan-in 0 in Lean's `Gate`): block empty.

  `o_w` has block S, so there are at least `d_w` merges. Each merging gate has at least 2 units and is
  `<= OR(S)`, so it is in D_w. Correct.
- **Sum.** `{N}`, U and the Pi_w are pairwise disjoint sets of gates, which gives
  `s >= 1 + |U| + sum |Pi_w|`. The second form uses `min(d_w, 2) = d_w - (|S_w| - 3)^+`. Correct.

## K1

With a NOT: `s >= 1 + |U| + base - ex >= base` when `ex <= 1`. Without a NOT: all sets are easy with `C1 = C`.
Then (a) and (c) alone give `s >= base`. Correct.

## K2 (minimal counterexample, sigma = base - s >= 1)

- **(i)** N2 is `MinCE.deadBound` together with `readers_sub_DC` (`lean/PEqualNP/W951/MinCEFacts.lean`):
  `#readers(v) <= #DC(v) <= deg v - sigma`. A point that lies in some set is read, since otherwise
  no output depends on `x_v`. So every point of some set has degree at least `1 + sigma >= 2`, and
  every such point of degree at most `1 + sigma` has exactly one reader. Correct for points of some
  set. **Correction (from the Lean proof, session dZb2E):** an earlier version of this report said
  "every point". A point of degree 0 can have no reader, and then the hypothesis `1 <= #DC(v)` of N2
  fails. The scaffold's statement ("every point of degree <= 1 + sigma") needs the same restriction;
  in Lean it is `reader_of_mem`, then N2.
- **(ii)** **W2:** P2 is cited ("r = x_v o c with c a gate"), but only the following is needed, and it
  holds in every correct circuit (not only minimal ones) once x_v has a single reader r and deg v >= 2.
  - r != N: through N the outputs are antitone in `x_v`, but `OR(S)` with `S ∋ v` increases.
  - OR-type `r = x_v | c`: c does not depend on `x_v`, because x_v's only reader is r. If `c(e_u) = 1`
    for some u != v, then r, and with it every wire, agrees at `e_u` and `e_u + e_v`. A set `S ∋ v`
    that avoids u (it exists by linearity and deg v >= 2: this is AL) changes value. Contradiction.
    This covers c = `x_u` an input. So r has at most 1 unit.
  - AND-type: `r <= x_v`. Comparing 0 and `e_v`, the partner must satisfy `c(0) = 1`, so c is not an
    input.

  So r ∈ U, and readers of different V1 points are different gates. Correct.
- **Arithmetic.** `base - sigma >= 1 + |U| + base - ex_hard`, and `|U| >= |V1|`. Correct.
- **Scope (from the Lean proof, session dZb2E).** N2 in Lean (`MinCE.deadBound`) is stated for a global
  minimal counterexample (`MinCE`). The Consequences close specific frontier systems F, which uses
  F-relative minimality: every F - u satisfies the bound. Using N2 there needs N2 for that relative
  notion, which the scaffold's notes use but Lean does not state.

## Numeric checks (kcheck.py)

Every step above is checked separately: (a)-(e), the OR-top and AND-top witnesses of (b), the
g <= C1(g) <= OR(S) step and the union-find run of (c), the K2 (ii) claim, and the final inequality.
- **Corpus.** 42 circuits, 0 failures: scaffold's `lemmaK/xc` (16 circuits) and
  `tools/w951/tests/instances` (26).
- **Random.** 7,191,646 random one-NOT circuits (seeds 21-24, 2,000,000 draws each) with n <= 6 and 4-15 gates; the outputs are a random linear
  family among the OR functions each circuit computes. No failure. Of these, 1,216,470 are tight (bound
  = s), 435,582 have a hard set with |S| >= 3, 1,136,129 have an easy set with |S| >= 3, and 39,361 have a
  single-reader point of degree >= 2.
- **Consequences.** The 14 round-7 base-16 systems (`f15/jobs16r7.json`) were recomputed: 13 have ex = 1,
  and rank 13 has ex = 2 with 4-sets 0457, 1356 and degree-2 points 6 and 7. This matches the README.
  Frontier list (`lemmaK/unc15.json`, scaffold-951 e59751c), recounted with independent code: of 1279
  systems, K1 (ex <= 1) closes 1045 and K2 (ex < 2 + #points of degree 2, points of some set) closes 195.
  The other 39 all have ex = 2, two 4-sets and minimum degree 3. Of the 33 base-15 systems, K1 closes 27
  and K2 closes 6. Both match the scaffold's `kcount.py`. Not recounted independently: the 5 systems closed
  by the absence of the V1 = ∅ scenario, which rests on the 245pqr scenario data; the remaining 34 ranks
  match the README. K2 closures carry the scope caveat above (relative N2).

## For the Lean formalization

Done: session dZb2E checked Lemma K in Lean (branch `lemmaK` at 19601c9, `W951/LemmaK.lean`, no sorry),
without cleanliness, with P_w excluding `== 1` (its `LeafK`), and found no false step. The proof splits
into one lemma per step: (a), (b-or), (b-and, with the constant-1 leaves dropped),
(c: monotone `C1` sandwich + union-find), (d), (e), and a final card sum over disjoint Finsets. N2 is
already checked. For K2 (ii), use the argument of W2 instead of P2: it needs only correctness, the single
reader and AL.
