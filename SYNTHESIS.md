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
| Relativization: L-lib-061, L-lib-062 | arguments valid in every oracle world | a physical resource used only as a black box is an oracle. Both sides are realized: COLLAPSE side, closed timelike curves (Deutsch's model): P_CTC = PSPACE (Aaronson and Watrous 2009), the world of a PSPACE-complete oracle, where P = NP; SEPARATION side, quantum mechanics as a black box: relative to a random oracle, NP is not solved by a quantum machine in time o(2^{n/2}) (Bennett, Bernstein, Brassard and Vazirani 1997) | collapse side: P, NP and coNP inside P_CTC (L-qg-161, L-qg-162, L-qg-165; supporting rows L-qg-160, 163, 164, 166 to 168). P_CTC inside EXP is gap L-qg-169; P_CTC = PSPACE is cited, not a row. Separation side: not a row (no oracle BQP in `Defs`) |
| Algebrization: L-lib-065, L-lib-076 | arguments that survive low-degree extensions of the oracle | after T queries, the acceptance probability of a quantum query algorithm is a polynomial of degree at most 2T in the oracle bits (Beals, Buhrman, Cleve, Mosca and de Wolf 2001): the same object as an extension oracle. Aaronson and Wigderson also give oracles A, Ã with NP^A not inside BQP^Ã, so algebrizing arguments cannot show NP inside BQP | none yet. L-qg-110 to L-qg-118 define quantum circuits and count them; they are not the polynomial method. The degree-2T statement and the BQP separation are not rows |
| Natural proofs: L-lib-086 (not L-lib-035: its hypothesis holds for no function, L-lib-093) | natural properties (constructive: decidable in time polynomial in the truth table; large) useful against P/poly, provided an exponentially secure pseudorandom function exists in P | complexity = volume needs states whose complexity grows; Bouland, Fefferman and Vazirani (ITCS 2020): pseudorandom boundary states defeat every efficient boundary test, the same shape as a pseudorandom function defeating every constructive test. Hardness of decoding Hawking radiation (Harlow and Hayden; Aaronson) rests on the same kind of cryptographic premise | L-qg-103 (if P = NP, every polynomial-time, length-preserving function is invertible in polynomial time): the classical core, a complexity row. Pseudorandom states need definitions |

**What the map says, and its limit.** A physical theory enters in one of two ways
(`notes/checker/note-2-physics-models-and-the-three-barriers.md`, section 1): a resource used
only as a black box is an oracle, so "relative to the physics" is "relative to the oracle"; or
the theory changes the machine model itself (quantum: BQP; closed timelike curves: P_CTC), which
is not an oracle but can land where an oracle world lands (P_CTC = PSPACE, as with a
PSPACE-complete oracle). So physics can tell us what is computable IN a model (model route), and
which hardness claims rest on which assumptions (assumption route). A proof that works unchanged
for every oracle proves its conclusion relative to every oracle, and neither P = NP nor P ≠ NP
holds relative to every oracle (L-lib-061, L-lib-062; the two-line corollary `relativization_map`
in `notes/checker/BarrierMap.lean`), so no such proof settles P versus NP. P versus NP itself is a
statement about Turing machines; no physical theory changes its truth value. The team's earlier
verdict stands: no physics map passes a barrier, and unified gravity (Partanen and Tulkki 2025)
supplies no resource of either side. The maps are useful as a filter: an argument for P ≠ NP that
would go through unchanged relative to a PSPACE-complete oracle (the world P_CTC lands in, where
P = NP) proves something false there, and one that survives access to a low-degree extension is
ruled out by L-lib-076; both can be discarded before anyone spends time on them.

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
  induction on points) is a statement about how the two worlds share gates. Nothing transfers
  along this analogy in either direction: the worlds of section 2 are oracles outside the machine;
  these two are the values of one wire inside the circuit (a restriction, as in gate elimination),
  which is why an argument that uses them does not relativize.
- The ladder is the path from 951 to the general targets L-gen-101 to L-gen-103. Each rung adds
  NOT gates, i.e. more worlds per wire (k NOT gates: up to 2^k). The ladder is short: every
  function of n inputs is computed with ceil(log2(n+1)) NOT gates (Markov 1958), and a circuit of
  size s becomes one of size at most 2s + O(n^2 log^2 n) with that many (Fischer 1975). So a
  superpolynomial bound at rung ceil(log2(n+1)) for an NP function is a general one, and the three
  barriers apply there in full. The honest expectation: they start to bite at or below that rung,
  and locating the rung is itself a result.

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
