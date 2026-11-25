# Synthesis

One page. It is the parent of three longer leaves in `workshop/notes/synthesis/` (`three-layers-long.md`,
`big-picture.md`, `collation-2026-11-24.md`); nothing in them was dropped. Names follow
[`NAMES.md`](NAMES.md); sources are in [`LITERATURE.md`](LITERATURE.md). Nothing here says that
P versus NP is settled.

## 1. Three layers

| Layer | What lives there | Word |
|---|---|---|
| A. Theorems | statements the Lean checker accepted | checked |
| B. Certificates and data | counterexamples, kernel-checked certificates, corpus tests | tested n/N |
| C. Premises and maps | assumptions about physics; maps between a complexity statement and a physics statement | premise, map |

Flow: data proposes a lemma → a kill test tries to break it → a paper proof → a referee → a checked
row. A claim may move up a layer; it is never quoted above the layer it is in. Layer C never
enters a Lean statement; it decides which statements are worth stating.

## 2. Relativity on both sides

The owner's gist: quantum/gravity relativity maps onto the relativization barrier to P versus NP.

| Barrier (checked rows) | What it forbids | Physics map (premise) |
|---|---|---|
| Relativization (L-lib-061, 062) | arguments valid in every oracle world | a physical model is an oracle world; closed timelike curves give the collapse side (NP ⊆ P_CTC, checked) |
| Algebrization (L-lib-065, 076) | arguments that survive low-degree extensions | quantum query algorithms are low-degree polynomials in the oracle |
| Natural proofs (L-lib-086) | constructive, large properties against P/poly | pseudorandomness assumptions behind hardness of decoding |

Limit of the map: physics says what is computable in a model and which hardness claims rest on
which assumptions. P versus NP is a statement about Turing machines; no physics map passes a
barrier. Use: a filter that discards an argument before anyone spends time on it.

## 3. Where the proof effort sits

The NOT gate ladder: rung 0 (no NOT gate) is known; rung 1 is `L_meta_951`; rung ⌈log₂(n+1)⌉ is
general circuits (Markov and Fischer, checked: `Fischer.L104`).

**`L_meta_951`** (one NOT gate saves nothing on Boolean sums). One `sorry`: `no_minCE`.

| | |
|---|---|
| Theorem (checked) | `no_minCE_of_ugame`: true when the certificate game on the lifted outputs is won (`UGameWon`) |
| Theorem (checked) | `muF2_of_notVar`, `no_minCE_of_gainF2_or_cubeLocal`: true when the NOT gate reads an input, or every cube is `CubeLocal` or has a point step |
| Lemma (checked) | `MinCE.no_const`, `no_dup`, `no_var`, `live`, `not_used`, `observable` |
| Lemma (paper) | `MinCE.no_rewire`; reach of value arguments, no mixing of worlds, one colouring per merge gate |
| Open | circuits that lose the certificate game (smallest: sets {0,1,2}, {0,3,4}, `notInput` = x1 ∨ x3; hard core `Cex.threeFourSetsInATriangle`, old cxT2) |
| Open | `GainF2` under `MinCE.no_rewire` |
| Refuted | seven families, each with its counterexample: [`one-not/DEAD_ENDS.md`](one-not/DEAD_ENDS.md) |
| Tested | `realWitness` count ≥ `base` at every cube of every suite: no failure |

Every open item concerns a `notInput` that depends on at least two inputs. The technique reads the
inside of the circuit at Boolean points, so it does not relativize or algebrize, and it concerns
one explicit sparse family, so it is not a natural property; it is also far below the range the
barriers speak about (table per technique: `workshop/notes/synthesis/big-picture.md` section 3).

**General circuits.** Checked: `Fischer.L104`; the size hierarchy; C(x ⊕ f) ≥ max + 3 and = min + 4
when C(f) ≠ C(¬f); Kannan's uniform half reduced to a polynomial-time check. Open: L-gen-101 to
103; the XOR extension when C(f) = C(¬f).

**Quantum gravity.** 47 rows checked (gate-word counting; P = NP inverts every polynomial-time
length-preserving function; NP and coNP inside P_CTC; the five-qubit code). Open: L-qg-115, 116,
119, 169.

## 4. What has to stay consistent

1. One name per item, in formal style (`NAMES.md`); the old code in brackets once.
2. One word per layer: checked, paper, tested n/N, premise.
3. A refuted statement names its counterexample; a counterexample says what it refutes.
4. Literature is never dropped (`LITERATURE.md`).
5. The board is where questions go, not the owner.
