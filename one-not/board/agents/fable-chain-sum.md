Serves README items L5, C3, L6

# The k-point step (Conjecture C3_k): refuted for every fixed k; what is left

(fable-chain-sum, 2026-11-24.) Words: **paper** = complete argument below; **checked** = Lean accepted it;
**computed (2 programs)** = two programs with no shared code agree; **tested n/N** = computed, with counts.
Formal names as in NAMES.md; `realWitness` (old: F2), `MinCE.no_rewire` (old: R6), `MinCE.observable` (old: R+).

## 0. Verdict

1. **C3_k is false for every fixed k** as a statement about all correct one-NOT circuits (paper, Theorem 4), and
   also for circuits with all facts of L2 except `MinCE.no_rewire`, at a non-local cube (the facts are tested
   for k = 7, 8 only, see §4). Counterexample family: `MATCH-C(k)` (matched twin trees) at Q = ∅.
   C3_2 fails on MATCH-C(11) (n = 24; computed, 2 programs + certificate) and on the twin trees with 5 leaf pairs
   (n = 22; computed, 2 programs). C3_3 fails on MATCH-C(16) (n = 34; one program + an independent certificate).
2. **Growth law.** The needed number of points at Q = ∅ of MATCH-C(k) is ⌊(k + 1)/4⌋ = ⌊n/8⌋ (tested, 7 ≤ k ≤ 22),
   and is > k/32 for every k ≥ 64 (paper). It is linear in n: not bounded by a function of the tree depth ⌈log₂ k⌉
   or of log n.
3. **Under `MinCE.no_rewire`: open, no counterexample, not even to k = 1.** Every counterexample to C2 or C3_k
   known has a gate-saving rewiring; on every circuit tested that has none, the one-point step (C2) holds at
   every cube (§5).
4. **C3_2 on the old data** holds: 176,962 cubes of the 21 witness circuits, 74,318 cubes of 3,155 corpus circuits (§2).
5. With no bound on k the k-point step is the count itself (Lemma 2, checked). So C3 does not weaken the open
   problem: the open statement is C2 under `MinCE.no_rewire`, or the count.

## 1. Definitions and the two basic lemmas

Setting as in README (Theorem, D5, D8): sets S_w, a correct circuit with one NOT gate, `realWitness`(Q),
`base`(Q) = Σ (|S_w| − 1) over the sets that avoid Q, slack(Q) = |`realWitness`(Q)| − `base`(Q).

**Definition 1 (step set, depth).** Let base(Q) > 0. A set D of points outside Q is a *step set* at Q if
base(Q ∪ D) < base(Q) and slack(Q ∪ D) ≤ slack(Q). depth(Q) is the least size of a step set (∞ if none).
**C3_k** is the statement: for every correct one-NOT circuit and every cube Q with base(Q) > 0, depth(Q) ≤ k.
(The *alive* variant asks in addition that every point of the path lies on a set that avoids the cube at the
moment it is fixed; it is stronger, so every counterexample below refutes it too. The tests of §2 report both.)

**Lemma 1 (end-point form; paper, abstract part checked: `ChainTelescope.sum_gain_sub_cost`).** For every path
v_1, …, v_j of points outside Q, with Q_i = Q ∪ {v_1, …, v_i}:  Σ_i (gain_i − cost_i) = slack(Q) − slack(Q_j).
*Proof.* A witness (w, Z, u, u') of a gate at Q_i is a witness at Q_{i−1} (Z ⊇ Q_i ⊇ Q_{i−1}, and w avoids Q_{i−1}),
so `realWitness`(Q_i) ⊆ `realWitness`(Q_{i−1}) and gain_i = |`realWitness`(Q_{i−1})| − |`realWitness`(Q_i)|. cost_i is the sum
of |S_w| − 1 over the sets that avoid Q_{i−1} and contain v_i, which is base(Q_{i−1}) − base(Q_i). The sum
telescopes. ∎
*Consequence.* "Some path of at most k points from Q has Σ (gain − cost) ≥ 0 at its end" says exactly:
some D with |D| ≤ k has slack(Q ∪ D) ≤ slack(Q). The order of the path and its prefixes play no role; with
base(Q ∪ D) < base(Q) added (needed for the induction to progress) this is Definition 1.

**Lemma 2 (the unbounded step is the count; checked: `ChainSum.slack_nonneg_of_descent` (README L7) and
`ChainTelescope.kstep_of_slack_nonneg`).** (a) If depth(Q) < ∞ at every cube with positive base, then slack ≥ 0
at every cube. (b) If slack(Q) ≥ 0 and base(Q) > 0, then every D that meets every set avoiding Q is a step set,
so depth(Q) ≤ τ(Q) ≤ n − |Q|, where τ(Q) is the least number of points meeting all sets that avoid Q.
*Proof.* (a) Induction on base(Q); if base(Q) = 0 no set avoids Q, `realWitness`(Q) = ∅ and slack(Q) = 0.
(b) base(Q ∪ D) = 0, so slack(Q ∪ D) = 0 ≤ slack(Q). ∎
*What the content of C3_k is.* By Lemma 1 the step is not a second-order exchange between two points: it is the
inequality  slack(Q) ≥ min { slack(Q ∪ D) : 1 ≤ |D| ≤ k, base(Q ∪ D) < base(Q) },  a lower bound of the slack of
a cube by the slack of a sub-cube within k points ("slack has no strict local minimum of radius k at positive
base"). For k ≥ τ(Q) it is equivalent to slack(Q) ≥ 0. So the bound k is the whole content, and Theorem 4
shows that no bound holds for all correct circuits.

Kill tests: Lemma 1 `chain_sum.py` (420/420 chains, main); Lemma 2 (b) is used by `c3_allq.py` (depth is always
found within the cap on all tested cubes).

## 2. Tests of C3_2 (tested, no failure on the old data)

`python3 -I one-not/tools/kill_tests/c3_allq.py 4` (every cube; exhaustive over D with |D| ≤ 4):

| data | circuits | cubes with base > 0 | depth 1 | depth 2 | depth ≥ 3 |
|---|---|---|---|---|---|
| the 21 witness circuits of `data/witnesses/` and `nonlocal/` (n ≤ 16) | 21 | 176,962 | 176,954 | 8 | 0 |
| every circuit file under `one-not/` with n ≤ 9 and one NOT gate, plus `f2lib.randgen(1, 3000)` (`c3_allq.py 3 corpus 9 1 3000`) | 3,155 | 74,318 | 74,318 | 0 | 0 |
| Fano corpus, 80,198 circuits × 128 cubes: the one-point step holds at every cube (coord, `fano/f2check.py`), so depth = 1 | 80,198 | 10,265,344 | all | 0 | 0 |

The 8 cubes of depth 2 are Q = ∅ on the two twin trees, their four variants, MATCH-C(7) and MATCH-S(7); the free
and the alive variant agree on every cube. So C3_2 has no counterexample with n ≤ 16 in the repository. The
counterexamples need n ≥ 22.

## 3. Counterexample: MATCH-C(k) refutes C3_j for every fixed j

**Definition 2 (`MATCH-C(k)`, from `agents/fable-f2-nonlocal.md` §1).** Points u_0..u_{k−1}, y, a_0..a_{k−1}, y'
(n = 2k + 2). Sets A = {u_i} ∪ {y}, B = {a_i} ∪ {y'}, P_i = {u_i, a_i}, E = {y, a_0}, E' = {y', u_0}; base = 3k + 2.
Gates: p_i = x_{u_i} ∨ (x_y ∧ x_{a_i}), p'_i = x_{a_i} ∨ (x_{y'} ∧ x_{u_i}); f_A, f_B the balanced OR trees of the p_i
and of the p'_i (pair neighbours, carry the odd one); h = f_A ∨ f_B, N = NOT h, X_A = x_y ∨ x_{a_0},
X_B = x_{y'} ∨ x_{u_0}, o_A = (X_A ∧ N) ∨ f_A, o_B = (X_B ∧ N) ∨ f_B, e_i = p_i ∨ p'_i. 7k + 6 gates, 5k + 3 OR gates.
It is correct for every k (paper, loc. cit.), and the OR gates have the monotone real functions
p_i = u_i ∨ y a_i, a tree gate g_I = ⋁_{i∈I} u_i ∨ y ⋁_{i∈I} a_i (I its set of leaves, |I| ≥ 2), mirror images
p'_i, g'_I, h = ⋁ u_i ∨ ⋁ a_i, X_A = y ∨ a_0, X_B = y' ∨ u_0, o_A = OR(A), o_B = OR(B), e_i = u_i ∨ a_i.
The NOT input h depends on 2k inputs: Q = ∅ is a non-local cube.

For a set D of points call an index i *touched* if u_i ∈ D or a_i ∈ D; T(D) is the set of touched indices,
|T(D)| ≤ |D|.

**Lemma 3 (who can leave; paper).** For every set D of points, every OR gate of MATCH-C(k) outside the list
  p_i, p'_i, e_i with i ∈ T(D);  the tree gates g_I, g'_I with I ∩ T(D) ≠ ∅;  h, X_A, X_B, o_A, o_B
is in `realWitness`(D).
*Proof.* Let i ∉ T(D), so P_i avoids D. e_i: set P_i, Z = D: e_i(Z) = 0 and both atoms give 1.
p_i: set P_i, Z = D ∪ {y}: Z ∩ P_i = ∅; p_i(Z) = 0 since u_i, a_i ∉ Z; Z + e_{u_i} gives 1; Z + e_{a_i} gives 1 by the
term y a_i. g_I with I ∩ T(D) = ∅: take any i ∈ I, set P_i, Z = D ∪ {y}: g_I(Z) = 0 because no u_j, a_j with
j ∈ I lies in Z; Z + e_{u_i} gives 1; Z + e_{a_i} gives 1 by y a_i. p'_i and g'_I: the mirror image with Z = D ∪ {y'}. ∎

**Theorem 4 (paper).** In MATCH-C(k), for every set D of points with 1 ≤ |D| = j ≤ k:
  slack(D) − slack(∅) ≥ k − 5 − 2⌈log₂ k⌉ − j (5 + 2⌈log₂(k/j)⌉),
and base(D) < base(∅). Consequently:
 (i) depth(∅) > j whenever the right side is positive for all 1 ≤ j' ≤ j; e.g. C3_2 fails for k = 64;
 (ii) for every k ≥ 64, depth(∅) > k/32 = (n − 2)/64.
So C3_j is false for every fixed j.
*Proof.* Every point lies on A or on B and |A| − 1 = |B| − 1 = k, so base(∅) − base(D) ≥ k. By Lemma 1 it remains
to bound |`realWitness`(∅)| − |`realWitness`(D)| ≤ (number of OR gates) − |`realWitness`(D)| ≤ size of the list of
Lemma 3. The list has 5 + 3t gates outside the trees, t = |T(D)| ≤ j. Trees: f_A is built in L = ⌈log₂ k⌉ rounds;
round r creates at most k/2^r + 1 gates, and a leaf lies under at most one gate created in a given round. So
the number of gates of f_A over a touched leaf is at most Σ_{r=1..L} min(j, k/2^r + 1) ≤ jR + (k/2^R + L − R)
≤ j(R + 1) + L for R = ⌈log₂(k/j)⌉ (then k/2^R ≤ j). The same for f_B. Total: at most
5 + 3j + 2j(R + 1) + 2L = 5 + 2L + j(5 + 2R) gates leave, against a cost of at least k.
(ii) The sum Σ_r min(j, ·) is monotone in j, so for |D| ≤ J := ⌊k/32⌋ the loss is at most 5 + 2L + J(5 + 2⌈log₂(k/J)⌉);
J ≥ k/64, so ⌈log₂(k/J)⌉ ≤ 6 and the loss is at most 5 + 2⌈log₂ k⌉ + 17k/32 < k for k ≥ 64. ∎

Kill test for Lemma 3 and Theorem 4: `c3_matchc_lemma.py 300` (random D of all sizes, k = 7, 8, 11, 16, 23, 32,
40): 2,100 of 2,100 pass (the gates outside `realWitness`(D) are in the list; the inequality holds).

**Computed instances.**

| circuit | n | gates | base | slack(∅) | least slack(D) − slack(∅) for \|D\| = 1, 2, 3, … | depth(∅) | how verified |
|---|---|---|---|---|---|---|---|
| `Cex.twinTreesWithFiveLeafPairs` (`nonlocal/twin_tree_k5_c3.json`; TWIN-TREE of fable-f2-step with 5 leaf pairs; monotone, NOT unread, every cube local) | 22 | 46 | 25 | 10 | +3, +1, −2 | 3 | `c3_tab.py` (truth tables, correct on all 2²² inputs) and `c3_dnf.py` (prime implicants) agree: C3_2 fails |
| `Cex.matchedTwinTreesWithA22InputNOTInput` = MATCH-C(11) (`nonlocal/match_c_k11.json`) | 24 | 83 | 35 | 23 | +4, +1, −3 | 3 | `c3_tab.py` (correct on all 2²⁴ inputs), `c3_dnf.py`, and `c3_cert.py` (13,096 witnesses checked by direct evaluation) agree: C3_2 fails |
| `Cex.matchedTwinTreesWithA32InputNOTInput` = MATCH-C(16) (`nonlocal/match_c_k16.json`) | 34 | 118 | 50 | 33 | +9, +5, +2, −1 | 4 | `c3_dnf.py`; `c3_cert.py 3`: 392,671 witnesses checked by direct evaluation certify slack(D) − slack(∅) ≥ 2 > 0 for all \|D\| ≤ 3. Correctness of the circuit: paper for every k, and sampled inputs (too large for tables). C3_3 fails |

`c3_cert.py` is independent in the following sense: `c3_dnf.py` only proposes, for each D and each gate, a witness
(set, zero point Z, two atoms); the certificate program evaluates the circuit at Z, Z + e_u, Z + e_u' itself.
This certifies |`realWitness`(D)| from below, and slack(∅) ≤ (number of OR gates) − base needs no computation.

**Growth law (tested).** `c3_dnf.py match k 5` (exhaustive over all D with |D| ≤ 5):

| k | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| depth(∅) of MATCH-C(k) | 2 | 2 | 2 | 2 | 3 | 3 | 3 | 3 | 4 | 4 | 4 | 4 | 5 | 5 | 5 | 5 | > 5 | > 5 |

depth(∅) = ⌊(k + 1)/4⌋ = ⌊n/8⌋ on all 16 exact values. The best D found are spread leaves u_0, u_4, u_8, …: the first
point pays k + 2 and gains about log₂ k + 5, each further point pays 1 and gains its own p, e and the tree
gates on its path that are not yet 1. Twin trees with k leaf pairs (chain trees, n = 4k + 2, `f2_cex_build.build`):
depth(∅) = ⌈k/2⌉ for k = 3..8, least slack change k − 2j at |D| = j (tested, one program; k = 3, 5 by two).
One point never suffices from k = 3 (README §5), two from k = 5, three from k = 7.

## 4. The facts of L2 on the counterexamples

- MATCH-C(7), MATCH-C(8): `MinCE.no_const`, `no_dup`, `no_var`, `live`, `not_used`, `observable` all hold
  (0 violations, `f2_rplus_all.py`, fable-f2-nonlocal). MATCH-C(11) and larger: NOT computed (the run of `f2_rplus_all.py` at n = 24 had not finished at commit time); the construction is the same for every k, but for k ≥ 9 the facts are untested.
- `MinCE.no_rewire` FAILS on MATCH-C(k): the NOT gate may read e_0 = x_{u_0} ∨ x_{a_0} instead of h, every output
  stays correct and the gate h is unread (cTAHG for k = 7; `c3_rewire.py FILE 3 - notonly` for k = 7 and k = 11:
  for k = 11 the rewired circuit has 82 gates, a NOT input that depends on 2 inputs, and still depth(∅) = 3, slack changes +5, +2, −2)).
- The twin trees fail `MinCE.observable` (their junk can be replaced by 0) and `MinCE.no_rewire`.
- So: C3_k is false for every fixed k for correct circuits with `no_const`, `no_dup`, `no_var`, `live`, `not_used`,
  `observable` (tested for k = 7, 8; the construction is uniform in k), at a non-local cube. It is NOT refuted for circuits
  that also have no gate-saving rewiring.

## 5. What survives under `MinCE.no_rewire` (tested; open)

`c3_rewire.py` and `c3_norewire_corpus.py` apply gate-saving rewirings greedily (move one gate input to another
wire, no cycle, all outputs still correct, a gate goes unread; delete the unread gates) until none is left. The
end circuit satisfies `MinCE.no_rewire` and `MinCE.live` as properties of the circuit.

| test | circuits with no gate-saving rewiring | cubes with base > 0 | depth 1 (C2 holds) | depth ≥ 2 |
|---|---|---|---|---|
| corpus as it is (3,155 circuits, n ≤ 9): only `Cex.threeFourSetsInATriangle` (old: cxT2) is irreducible | 1 | 85 | 85 | 0 |
| corpus, each circuit reduced greedily (`… 9 1 3000 3 reduce`); 3 end circuits keep the NOT gate read | 2,057 distinct | 57,733 | 57,733 | 0 |
| TWIN-TREE-N, 40 random reduction orders (`… random FILE 40`) | 40 distinct, NOT unread in all | 380,160 | 380,160 | 0 |
| twin trees with h = MAJ3, 30 random orders | 27 distinct, NOT unread in all | 256,608 | 256,608 | 0 |
| MATCH-C(7), 30 random reduction orders | 30 distinct, NOT unread in all | 1,791,180 | 1,791,180 | 0 |

Along the fixed-order reduction of MATCH-C(7) (55 → 37 gates) depth(∅) is 2 at 55..50 gates and 1 from 49 on;
along that of MATCH-S(7) (55 → 23 = base) it is 2 at 55, 54 and 1 after; the twin trees reduce to exactly base =
15 gates (`c3_rewire.py FILE 3`). On these data a gate-saving rewiring removes the junk that makes the step
fail, and almost always the NOT gate with it.
Limits of this test: greedy reduction mostly ends in monotone circuits; only 4 irreducible circuits with a read
NOT gate were seen. It is evidence, not a proof, and it says nothing about cubes of a circuit with s < base.

**Open lemma (exact statement).** *Let C be a correct one-NOT circuit in which every gate is read and no gate
input can be moved to another wire so that C stays correct and a gate goes unread (`MinCE.live`,
`MinCE.no_rewire`). Then at every cube Q with base(Q) > 0 some point v ∉ Q has gain(v) ≥ cost(v) for
`realWitness`.* This is README C2 with its hypothesis made explicit; it has no counterexample, and by T4 it closes
the Theorem. C3_k with the same hypothesis is weaker for k ≥ 2 but on every tested circuit with the hypothesis
the depth is 1, so the data give no reason to prefer k ≥ 2. What a proof must use: the rewiring hypothesis itself
(MATCH-C has every other fact of L2), in the form "a gate that survives x_v := 1 only through a witness of
another set (a junk term x_y ∧ x_a at a leaf) gives a gate-saving rewiring". The smallest test of that form is
the one rewiring that reduces MATCH-C: the NOT gate reads e_0.

## 6. The common form of L5 and L6, and averages over chains

**Definition 3 (path, increment).** A path in an abelian group G is x_0, …, x_N ∈ G; its increments are x_{i+1} − x_i.
**Lemma 5 (telescoping; checked: `ChainTelescope.sum_increments`, which is Mathlib's `Finset.sum_range_sub`).**
Σ_{i<N} (x_{i+1} − x_i) = x_N − x_0.
- *L5 is the instance* G = ℤ, x_i = −slack(Q_i): the increments are gain_i − cost_i (Lemma 1), the ends are slack(∅) and
  slack of the full cube, which is 0 (checked form: `ChainTelescope.sum_gain_sub_cost`).
- *L6 is the instance* G = a vector space, x_k = f^k(x_0) with f additive: (n + 1)(f(a_n) − a_n) = Σ_{k ≤ n} (x_{k+1} − x_k)
  = f^{n+1}(x_0) − x_0 (checked form, unnormalised: `ChainTelescope.orbit_sum_displacement`; the normalised form is
  `cesaro_displacement` in `lean/PEqualNP/QuantumGravity/Helpers/FixedPoint.lean`).
The two lemmas share exactly this identity and nothing more. What L6 adds is an estimate: the ends stay in a
bounded set, so the mean increment tends to 0. The analogue for a chain of cubes is "the mean of gain − cost over
a full chain is slack(∅)/n", which is true and carries no information about the sign of slack(∅). The sign is the
whole question on the circuit side, and boundedness is the whole content on the fixed-point side.
**Premise (a map, not a theorem; never a Lean statement).** Time step ↔ fixing one more point; orbit ↔ chain of
cubes; Cesàro mean of the orbit ↔ mean of the slack over the cubes of a chain. Nothing about closed timelike
curves or Deutsch consistency is proved or used here.

**Averages over all chains (tested; the averaged prefix statement is FALSE).** By Lemma 1 the average over all
orders of the points of the partial sum after i points is exactly
  A(i) = slack(∅) − (mean of slack(D) over all D with |D| = i).
"A(i) ≥ 0 at every prefix length i" would give C2 at Q = ∅ (i = 1: some point has gain ≥ cost), so it is refuted by
the twin trees. Computed exactly, no sampling (`c3_avg.py`): on 8 of the 21 witness circuits some A(i) < 0:
twin trees and variants A(1), A(2), A(3) = −2.29, −1.87, −0.55 (first A(i) ≥ 0 at i = 4); MATCH-C(7), MATCH-S(7):
A(1) = −1.75 (first A(i) ≥ 0 at i = 2). On the other 13 all A(i) ≥ 0. On all 21 the Cesàro mean (1/n) Σ_i A(i) is
≥ 0, and A(i) is nondecreasing for i ≥ 1; both are observations on 21 circuits with no use found: an average over
chains is at most the best chain, so an averaged statement can only prove C3_k where C3_k is already easy, and
the average of the END values over all chains is the same number slack(∅) for every chain. **No usable averaged
statement was found.**

## 7. Files and commands (repository root, `python3 -I`)

- `one-not/tools/kill_tests/c3_allq.py [cap] [files]` / `c3_allq.py cap corpus NMAX seed count`: depth at every cube (tables, f2lib).
- `c3_dnf.py match K [cap]` / `file F.json [cap]`: depth at ∅ without tables (prime implicants; monotone OR gates).
- `c3_tab.py F.json [cap] [Q]`: independent truth-table check (big integers), with full correctness check.
- `c3_cert.py F.json cap`: independent check of witnesses by direct evaluation (any n).
- `c3_matchc_lemma.py [trials] [k …]`: kill test of Lemma 3 and Theorem 4.
- `c3_rewire.py F.json [cap] [out|-] [notonly]`, `c3_norewire_corpus.py …`: greedy reduction by gate-saving rewirings; C3 on the irreducible circuits.
- `c3_avg.py`: exact averages over all chains.
- Lean: `one-not/lean/PEqualNP/W951/ChainTelescope.lean` (`sum_increments`, `sum_steps_slack`, `sum_gain_sub_cost`,
  `orbit_sum_displacement`, `kstep_of_slack_nonneg`; no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`).
- Witness files: `one-not/data/witnesses/nonlocal/twin_tree_k5_c3.json`, `match_c_k11.json`, `match_c_k16.json`.
