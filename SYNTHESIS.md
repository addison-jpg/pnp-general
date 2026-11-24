# Synthesis: how the pieces fit

One page that places every line of work in one structure. Draft by the board integrator,
2026-11-24, at the owner's request; coord and the referee should correct it. Nothing here says
that P versus NP is settled, and every correspondence with physics below is a MAP between
statements, not a derivation of one from the other.

## 1. Three layers

| Layer | What lives there | Status word | Where |
|---|---|---|---|
| A. Theorems | Lean statements the checker accepted | "checked" | `lean/`, `951/lean/` |
| B. Certificates and data | per-circuit witnesses the kernel checks; corpus tests that can kill a lemma | "kernel-checked on N circuits", "tested, 0 failures on N" | `951/lean/.../*Witness*.lean`, `951/tools/kill_tests/`, `951/DEAD_ENDS.md` |
| C. Premises and maps | assumptions about physics; correspondences between a complexity statement and a physics statement | "premise", "map" | `BOARD.md` track pairs, `lean/PEqualNP/QuantumGravity/README.md` |

**Going beyond pure theorems** means using B and C on purpose, with a fixed direction of flow:
data proposes a lemma → a kill test tries to break it → a paper proof → the referee → a checked
row. A certificate is the bridge: a search program finds a small witness, Lean only checks it
(`951/PIPELINE.md`). Layer C never enters a Lean statement; it decides WHICH statements are worth
stating. A claim may move up a layer, never be quoted above the layer it is in.

## 2. "Relativity" on the complexity side and on the physics side

On the complexity side the word is **relativization**: a proof technique relativizes when it
stays valid with every oracle. The three barrier rows say what a proof of P ≠ NP cannot be.

| Barrier (checked rows) | What it forbids | Physics map (layer C) | Checked on the physics side |
|---|---|---|---|
| Relativization: L-lib-061, L-lib-062 | arguments valid in every oracle world | a physical resource acts as an oracle; choosing the physics chooses the world. Closed timelike curves are the model case | NP and coNP inside P_CTC: L-qg-160 to L-qg-168 |
| Algebrization: L-lib-065, L-lib-076 | arguments that survive low-degree extensions of the oracle | quantum amplitudes are low-degree polynomials in the oracle | quantum circuit rows L-qg-110 to L-qg-118; the degree-2T statement is not yet a row |
| Natural proofs: L-lib-086 | properties that are easy to recognise and hold for most functions, if strong pseudorandom functions exist | pseudorandom boundary states under complexity = volume; hardness of decoding Hawking radiation | L-qg-103 (P = NP inverts every polynomial-time function); pseudorandom states need definitions |

**What the map says, and its limit.** A physical model is an oracle world. "Relative to the
physics" on one side is "relative to the oracle" on the other. So physics can tell us what is
computable IN a world (model route), and which hardness claims rest on which assumptions
(assumption route), but a statement that holds in every world is exactly a relativizing one, and
those cannot settle P versus NP. The team's earlier verdict stands: no physics map passes a
barrier. The maps are useful as a filter: an argument that would work unchanged in the P_CTC
world, or for low-degree amplitudes, is ruled out before anyone spends time on it.

## 3. Where the current proof effort sits

- **L-meta-951** (one NOT gate saves nothing on Boolean sums) is rung 1 of the NOT gate ladder
  (`SIZENot`, L-gen-003, L-gen-004; top of the ladder = unrestricted circuits, gap L-gen-104).
- It is a gate-level, exact, linear bound in a restricted model. It reads the inside of the
  circuit, so it is not an oracle argument, and it is far below the range the barriers speak about
  (superpolynomial bounds against all circuits). It does not pass a barrier; it does not need to.
- Its internal structure has the same shape as section 2, as an ANALOGY only: the single NOT gate
  splits every wire into two monotone "worlds" (NOT := 0, NOT := 1). Everything that stays inside
  one world is settled by monotone arguments (`CanonClass.lean`); the whole difficulty is the
  gates that differ between the worlds. The open step (the count MU for the union `UC`, by
  induction on points) is a statement about how the two worlds share gates.
- The ladder is the path from 951 to the general targets L-gen-101 to L-gen-103. Each rung adds
  NOT gates, i.e. more worlds per wire (k NOT gates: up to 2^k). The honest expectation: the
  barriers start to bite somewhere on the ladder, and locating that rung is itself a result.

## 4. What has to stay consistent

1. One vocabulary: row, gap, certificate, tested, premise, map. A sentence uses the word of its
   layer.
2. Every physics counterpart on the board names its checked row or says "needs definitions".
3. Every statement about all correct circuits is tested on the corpus before it is a target; a
   statement about minimal counterexamples cannot be tested and must say which checked `MinCE`
   fact it uses.
4. When 951 closes: write rung k as a gap, and for each technique used record whether it would
   survive (a) an oracle, (b) a low-degree extension, (c) the natural-proofs test. That table is
   where the two "relativities" actually meet.
