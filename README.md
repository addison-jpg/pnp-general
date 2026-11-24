# pnp-general (by addison mccarl)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE.md)
disclaimer that a lot of the readmes are vibecoded. 
the higher level gist is: quantum/gravity relativity maps onto the relativity barrier to P/NP, and can help bypass it. 

**Claim of this repository.** Lower bounds for circuits of AND, OR and NOT gates, written as a formal proof. Each numbered item below is a Definition, Lemma, Theorem, Conjecture or Counterexample; each says whether it is **checked** (the Lean checker accepted it, axioms `propext`, `Classical.choice`, `Quot.sound`), **paper**, or **tested n/N**. Nothing here says that P versus NP is settled. Names: [`NAMES.md`](NAMES.md). Sources: [`LITERATURE.md`](LITERATURE.md). Work in progress: [`BOARD.md`](BOARD.md) and the four boards under [`boards/`](boards/).

## Theorem (`L_meta_951`, one `sorry`)

Let S_1, …, S_m ⊆ {1, …, n} with |S_w| ≥ 2 and |S_v ∩ S_w| ≤ 1 for v ≠ w. Let C be a circuit of fan-in-2 AND and OR gates and at most one NOT gate whose w-th output is the OR of the inputs in S_w. Then

    #gates(C) ≥ base := Σ_w (|S_w| − 1).

Without the NOT gate this is the theorem of Wegener and Mehlhorn, and `base` is exact. The statement is rung 1 of the NOT gate ladder (§7).

## 1. Definitions

- **D1** `MinCE`. A minimal counterexample: a correct circuit with #gates < `base` and the fewest gates among such.
- **D2** `notInput`, `faceZero`, `faceOne`. h is the wire the NOT gate reads. Replacing the NOT gate by 0 or by 1 gives two monotone circuits with `faceZero` ≤ C ≤ `faceOne`.
- **D3** `cube`, `CubeLocal`. The cube of Q is the set of inputs with x_v = 1 for v ∈ Q. It is local when h, restricted to it, is one input or constant.
- **D4** `ZeroPoint`, `atom`, `mergeSet`. A zero point of S_w is an input that is 0 on S_w; an atom is a zero point with one point of S_w switched on. A union-find run over S_w at a zero point marks the OR gates that join two blocks: the merge set.
- **D5** `realWitness` (old: F2). The OR gates g with g(Z) = 0 and g(Z + e_u) = g(Z + e_u') = 1 for a zero point Z of a set that avoids Q and two points u ≠ u' of it.
- **D6** `lift`, `LTS`, `LTSCert`, `UGameWon`. The lift replaces the NOT gate by a fresh input. A lifted test system of a set is a zero point with atoms in the lift. A pair of sets has a certificate when at most one atom of one system is not below the zero point of the other. The certificate game is won when every set has a system and every pair has a certificate in one direction.
- **D7** `LiftSDR`. One lifted class per set, pairwise disjoint, each of size |S_w| − 1.

## 2. Lemmas

- **L1** `merge_run` (checked). Every merge set of S_w has exactly |S_w| − 1 gates.
- **L2** `MinCE.no_const`, `MinCE.no_dup`, `MinCE.no_var`, `MinCE.live`, `MinCE.not_used`, `MinCE.observable`, `MinCE.no_rewire` (checked). In a minimal counterexample: no constant gate; no two gates compute the same function; no gate computes an input; every gate is read; both faces are incorrect; no constant on any set of readers of a wire keeps the circuit correct; no rewiring of a gate input leaves a gate unread.
- **L3** `no_minCE_of_liftSDR` (checked). If every minimal counterexample has `LiftSDR`, there is none.
- **L4** (paper, refereed). Any argument that reads only gate values at test points proves exactly the won games (Proposition S); with outputs in two-world normal form and all |S_w| ≥ 3 a winning choice stays in one world (Theorem D); a merge gate splits every set it serves by one colouring (Lemma T).

## 3. Theorems

- **T1** `liftSDR_of_ugame`, `no_minCE_of_ugame` (checked). `UGameWon` ⇒ `LiftSDR`. Hence the Theorem holds for every circuit whose lift wins the certificate game.
- **T2** `ugame_of_G1`, `ugame_of_G0`, `ugame_of_allHeavy`, `ugame_of_typeB` (checked). The game is won in four named cases.
- **T3** `muF2_of_notVar` (checked). The Theorem holds when the NOT gate reads an input, with no minimality.
- **T4** `no_minCE_of_gainF2_or_cubeLocal` (checked). If at every cube with positive `base` the cube is local, or some point v has gain(v) ≥ cost(v) for `realWitness`, there is no minimal counterexample.
- **T5** `small3_bound`, `bound_of_noDD`, `partial_bound` (checked). The Theorem holds when all |S_w| ≤ 3; when no output is in two-world normal form (any number of NOT gates); and a partial bound.

## 4. Proof of the Theorem, as far as it goes

Suppose the Theorem fails and take a minimal counterexample (D1). By L2 it is clean. If its lift wins the certificate game, T1 gives `LiftSDR` and L3 a contradiction. ∎ in that case.

**Open (the one `sorry`, `no_minCE`).** A minimal counterexample whose lift loses the certificate game.

- **Conjecture C1.** Every minimal counterexample has `LiftSDR`. Smallest lost game: S = {0,1,2}, {0,3,4}, h = x_1 ∨ x_3; a violation there is a configuration of three gates. Hard core: `Cex.threeFourSetsInATriangle` (old: cxT2), which satisfies L2 and loses the game.
- **Conjecture C3** (§6): the k-point step, the integral form of C2.
- **Conjecture C2.** Under `MinCE.no_rewire`, at every non-local cube some point has gain ≥ cost for `realWitness` (then T4 closes the proof).
- **Tested, no failure.** |`realWitness`(Q)| ≥ `base`(Q) at every cube of every suite (19,534 suite instances; 80,198 Fano circuits × 128 cubes).

## 5. Refuted, each with its counterexample

Seven families, 60+ rows: [`one-not/DEAD_ENDS.md`](one-not/DEAD_ENDS.md). The ones a new proof must not repeat:

| Refuted statement | Counterexample |
|---|---|
| induction that sets a point to 0 | `Cex.fanoFormulaWithAnUnusedNOTGate` |
| point step for one-face witness gates | `Cex.pappusConfigurationWithJunkGates` |
| point step for `realWitness`, all correct circuits | `Cex.twinBalancedORTreesWithLeafJunk` |
| the same under L2 without `no_rewire`, at a non-local cube | `Cex.matchedTwinTreesWithA14InputNOTInput` |
| disjoint representatives over pure classes, all correct circuits | `Cex.twoTwoWorldSetsSharingOneMergeGate` |
| price inequality over real merge sets, without minimality | `Cex.starOfFourPairsWithAThresholdNOTInput` |
| correctness on inputs of weight ≤ k only, any fixed k | Hiltgen and Paterson 1995; AG(2,25) construction |

## 6. The chain sum (Riemann sum) and the gravity/quantum link

How the proof extends itself: the step is a derivative, the count is its integral.

- **D8** `chain`, `gain`, `cost`, `slack`. A chain is an order v_1, …, v_n of the points, with cubes Q_i = {v_1, …, v_i}. gain_i = |`realWitness`(Q_{i−1}) \ `realWitness`(Q_i)|. cost_i = Σ (|S_w| − 1) over the sets that avoid Q_{i−1} and contain v_i. slack(Q) = |`realWitness`(Q)| − `base`(Q).
- **L5** chain sum. For every chain: Σ_i gain_i = |`realWitness`(∅)| and Σ_i cost_i = `base`. Hence slack(∅) = Σ_i (gain_i − cost_i): the count is the sum of the steps along any chain. Checked for every decreasing chain of finite sets: `ChainSum.card_eq_card_add_sum_gain`, `base_le_card_iff_sum_cost_le_sum_gain`, `base_le_card_of_step` (`one-not/lean/PEqualNP/W951/ChainSum.lean`). The instance (`realWitness` decreases along a chain, each set is paid once) is tested on 420 of 420 chains.
- **Reading.** Conjecture C2 asks every term gain_i − cost_i ≥ 0 for some chain: the pointwise form. The Theorem needs only the sum ≥ 0: the integral form. Every counterexample of §5 to the pointwise form has one term −1 and a positive sum (twin trees: +6; matched twin trees: +15).
- **Conjecture C3** (k-point step, new). At every cube with positive `base` some path of at most k points has Σ (gain − cost) ≥ 0 at its end. k = 1 is C2; k = n is the count; C3 for any fixed k proves the Theorem by the same induction. Tested at the empty cube: k = 2 suffices on all 21 counterexample circuits, including every circuit that refutes k = 1.
- **L6** time average (checked, `QuantumGravity/Helpers/FixedPoint.lean`: `cesaro_mem`, `cesaro_displacement`; rows L-qg-008, L-qg-102). A Deutsch-consistent state of a closed timelike curve is reached by Cesàro averages a_n = (n+1)⁻¹ Σ_{k ≤ n} f^k(x_0) of the orbit, and f(a_n) − a_n = (n+1)⁻¹ (f^{n+1}(x_0) − x_0): the sum of the steps is the difference of the end points.
- **Map (premise, never a Lean statement).** L5 and L6 are the same identity: a sum of increments along a path equals the difference of its ends. Time ↔ chain of cubes; state ↔ `realWitness`(Q); consistency (the displacement vanishes) ↔ the count (the slack does not go negative). On the quantum side the acceptance amplitude is a sum over computation paths; on the gravity side the path is closed. This is the link the owner's gist names; it selects statements, it proves none.
- **Limit.** A Riemann sum over inputs at one length (the density 2⁻ⁿ Σ_x f(x)) is a property of the function, not of the circuit, and cannot see size. The sums that see size run over cubes and chains, as above. Across input lengths there is no coherence to take a limit of ([`one-not/DEAD_ENDS.md`](one-not/DEAD_ENDS.md), family G).

## 7. The ladder, the barriers, the physics

- **T6** `Fischer.L104`, `Fischer.stage1` (checked; Markov, Fischer). `SIZE s ⊆ SIZENot (2s + n + 2) n`: ⌈log₂(n+1)⌉ NOT gates suffice with polynomial overhead. So a superpolynomial bound at that rung is a bound for all circuits. Rung 0 is monotone; rung 1 is the Theorem above.
- **T7** (checked). The size hierarchy; C(x ⊕ f) ≥ max(C f, C ¬f) + 3, with equality min + 4 when C(f) ≠ C(¬f); SAT ∉ SIZE((a/b)n + c) for a/b < 5/4. Open: L-gen-101 to 103; the case C(f) = C(¬f).
- **T8** (checked). The three barriers: relativization (L-lib-061, 062), algebrization (L-lib-065, 076), natural proofs (L-lib-086).
- **T9** (checked, 47 rows, [`lean/PEqualNP/QuantumGravity/README.md`](lean/PEqualNP/QuantumGravity/README.md)). The classical cores of the quantum gravity arguments: NP and coNP are inside P_CTC; if P = NP every polynomial-time length-preserving function is invertible in polynomial time; gate-word counting; the five-qubit code. Open: L-qg-115, 116, 119, 169.
- **Premise (never a Lean statement).** A physical model is an oracle world. This is the map from quantum/gravity relativity to the relativization barrier: it says which arguments cannot work in which world. [`SYNTHESIS.md`](SYNTHESIS.md).

## 8. Check it

`cd lean && lake exe cache get && lake build PEqualNP.General.L001` for one row; `cd one-not/lean && lake build` for the 951 development (exactly one `sorry`, `no_minCE`). Never run `lake update`.

| Path | What it is |
|---|---|
| `lean/` | the Lean project; `PEqualNP/General/` (L-gen), `PEqualNP/QuantumGravity/` (L-qg), barriers under `PEqualNP/Library/` |
| `one-not/` | the Theorem above: `lean/PEqualNP/W951/`, counterexamples in `data/witnesses/`, tests in `tools/kill_tests/`, [`one-not/README.md`](one-not/README.md) |
| `notes/`, `tools/`, `MST.json`, `NAMES.json` | write-ups; build queue, checker, name generator; the file tree and the name tree as data |

The Lean project started from `brilliant-hq/pequalnp-proofs` (Apache License 2.0); see [License](#license).

## License
MIT License; see [`LICENSE.md`](LICENSE.md). The Lean project started from `brilliant-hq/pequalnp-proofs`, which is distributed under the Apache License 2.0; code taken from it remains under that license. New work in this repository is by addison-jpg and contributors.
