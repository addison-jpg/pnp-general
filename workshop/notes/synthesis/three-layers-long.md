# Synthesis: how the pieces fit

One page that places every line of work in one structure. Draft by the board integrator,
2026-11-24, at the owner's request; coord and the referee should correct it. Nothing here says
that P versus NP is settled, and every correspondence with physics below is a MAP between
statements, not a derivation of one from the other.

## 1. Three layers

| Layer | What lives there | Status word | Where |
|---|---|---|---|
| A. Theorems | Lean statements the checker accepted | "checked" | `lean/`, `one-not/lean/` |
| B. Certificates and data | per-circuit witnesses the kernel checks; corpus tests that can kill a lemma | "kernel-checked on N circuits", "tested, 0 failures on N" | `one-not/lean/.../*Witness*.lean`, `one-not/tools/kill_tests/`, `one-not/DEAD_ENDS.md` |
| C. Premises and maps | assumptions about physics; correspondences between a complexity statement and a physics statement | "premise", "map" | `BOARD.md` track pairs, `lean/PEqualNP/QuantumGravity/README.md` |

**Going beyond pure theorems** means using B and C on purpose, with a fixed direction of flow:
data proposes a lemma → a kill test tries to break it → a paper proof → the referee → a checked
row. A certificate is the bridge: a search program finds a small witness, Lean only checks it
(`one-not/PIPELINE.md`). Layer C never enters a Lean statement; it decides WHICH statements are worth
stating. A claim may move up a layer, never be quoted above the layer it is in.

### Layer B for 951, concretely (certificates and data; pnp-subproblem, 12:50)

| Checker | Code | What it establishes | Scale |
|---|---|---|---|
| Lean certificates | `one-not/lean/.../PureSDRWitness.lean`, `SDRWitness*.lean` (`decide`) | the statement is a THEOREM for that one circuit (kernel-checked) | PureSDR on 36 circuits, MergeSDR on 35 |
| kill tests (board integrator) | `one-not/tools/kill_tests/` (on `tools/w951`) | candidate lemmas tested on the corpus; one failure kills a lemma (`one-not/DEAD_ENDS.md`) | corpus, per test |
| scaffold | scaffold-951 branch (`f15/`), OR-only merge rule | PureSDR / MergeSDR with 0 failures | 75,619 records, 62,463 distinct circuits |
| independent re-implementation | `one-not/tools/referee_b/` (no `w951`, no `kill_tests`) | the same claims with separate code: guards against implementation bugs, NOT against wrong definitions. Classes match Lean's certificates 181/181 | 44,713 circuits |
| cross-check of the cross-check | `one-not/tools/referee_b_xcheck/` (research, on `w951`) | referee_b's survey re-derived with `w951`: 0 disagreements | 339 circuits |

**Corpus.** Reproducible from the repos: `data-corpora` (pequalnp-work, 2aa9856) plus every circuit file in `one-not/`:
44,713 circuits after the filters (one NOT, correct, n ≤ 16). Scaffold's 75,619 records = data-corpora 40,533 +
named 14 + instances 25 + **35,047 that exist only in scaffold's scratchpad** (xgen dumps, adv). Those are not
reproducible, and pequalnp-work is frozen and not reachable from every session. **Action:** copy data-corpora and
scaffold's dumps into `one-not/data/` so every "0 failures on N" can be rerun.

**Results that stand on two independent checkers** (referee_b and scaffold / kill_tests):
- PureSDR exists: 44,713 / 44,713; every class has exactly d_w merges.
- Type-A collisions: kinds (i), (ii), (iii) all occur (5,019 / 1,331 / 228 circuits), no other kind.
- Dichotomy (CSP after fixing free classes and arc consistency): holds on 44,707; only cxT2 is not globally
  consistent, and with ALL I0 atom tuples cxT2 is consistent too (its 2-class core was a cap artefact).
- MU slack ≥ 0 on all 44,710 (WIDE and NARROW). It FAILS off-corpus: `one-not/data/witnesses/cxMU_dd.json` has pure
  |U| = 5 < base 6, while lifted |U| ≥ 14. Corpus data never produced this, so data alone cannot certify a lemma.

**Barrier suite.** The small fixed set every candidate lemma runs on first (PROOF_PLAN rule 1): CfgI, ADV3, ADV4,
cxT4, cxU_8_4, cxr, HARD4, the 24 forced-h fixh16 circuits, plus the kernel-certified cxT2, cxe3, ce3 and the
witnesses in `one-not/data/witnesses/` (cxMU_dd, Pasch s14). Hand-built circuits break lemmas that random and SAT corpora
never do (B1 disjointness, merge-tree support, MU over pure classes), so the suite carries more weight than the 44k.

## 2. "Relativity" on the complexity side and on the physics side

On the complexity side the word is **relativization**: a proof technique relativizes when it
stays valid with every oracle. The three barrier rows say what a proof of P ≠ NP cannot be.

| Barrier (checked rows) | What it forbids | Physics map (layer C) | Checked on the physics side |
|---|---|---|---|
| Relativization: L-lib-061, L-lib-062 | arguments valid in every oracle world | PREMISE: a physical model is an oracle world; choosing the physics chooses the world. Both sides are realized: COLLAPSE side, closed timelike curves (Deutsch's model): P_CTC = PSPACE (Aaronson and Watrous 2009), the world of a PSPACE-complete oracle, where P = NP; SEPARATION side, quantum mechanics as a black box: relative to a random oracle, NP is not solved by a quantum machine in time o(2^{n/2}) (Bennett, Bernstein, Brassard and Vazirani 1997) | collapse side: P, NP and coNP inside P_CTC (L-qg-161, L-qg-162, L-qg-165; supporting rows L-qg-160, 163, 164, 166 to 168). P_CTC inside EXP is gap L-qg-169; P_CTC = PSPACE is cited, not a row. Separation side: not a row (no oracle BQP in `Defs`) |
| Algebrization: L-lib-065, L-lib-076 | arguments that survive low-degree extensions of the oracle | after T queries, the acceptance probability of a quantum query algorithm is a polynomial of degree at most 2T in the oracle bits (Beals, Buhrman, Cleve, Mosca and de Wolf 2001): the same object as an extension oracle. Aaronson and Wigderson also give oracles A, Ã with NP^A not inside BQP^Ã, so algebrizing arguments cannot show NP inside BQP | none yet. L-qg-110 to L-qg-118 define quantum circuits and count them; they are not the polynomial method. The degree-2T statement and the BQP separation are not rows |
| Natural proofs: L-lib-086 (not L-lib-035: its hypothesis holds for no function, L-lib-093) | natural properties (constructive: decidable in time polynomial in the truth table; large) useful against P/poly, provided an exponentially secure pseudorandom function exists in P | complexity = volume needs states whose complexity grows; Bouland, Fefferman and Vazirani (ITCS 2020): pseudorandom boundary states defeat every efficient boundary test, the same shape as a pseudorandom function defeating every constructive test. Hardness of decoding Hawking radiation (Harlow and Hayden; Aaronson) rests on the same kind of cryptographic premise | L-qg-103 (if P = NP, every polynomial-time, length-preserving function is invertible in polynomial time): the classical core, a complexity row. Pseudorandom states need definitions |

**What the map says, and its limit.** Premise (layer C, owner): a physical model is an oracle
world, so "relative to the physics" is "relative to the oracle". (P_CTC is a computational model, not an
oracle; the identification is the premise, not a result.) Closed timelike curves are taken
as the world of a PSPACE-complete oracle (P_CTC = PSPACE), quantum black-box access as a
random-oracle world (`workshop/notes/checker/note-2-physics-models-and-the-three-barriers.md`). So physics can tell us what is computable IN a model (model route), and
which hardness claims rest on which assumptions (assumption route). A proof that works unchanged
for every oracle proves its conclusion relative to every oracle, and neither P = NP nor P ≠ NP
holds relative to every oracle (L-lib-061, L-lib-062; the two-line corollary `relativization_map`
in `workshop/notes/checker/BarrierMap.lean`), so no such proof settles P versus NP. P versus NP itself is a
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
  (superpolynomial bounds against all circuits): gate-level counting of this kind is not blocked by
  the barriers, which concern superpolynomial lower bounds for unrestricted circuits. It does not
  pass a barrier; it does not need to. The whole 951 chain in the three layers, with a barrier
  check per technique: [`one-not/SYNTHESIS-one-not.md`](one-not/SYNTHESIS-one-not.md).
- Its internal structure has the same shape as section 2, as an ANALOGY only: the single NOT gate
  splits every wire into two monotone "worlds" (NOT := 0, NOT := 1). Everything that stays inside
  one world is settled by monotone arguments (`CanonClass.lean`); the whole difficulty is the
  gates that differ between the worlds. The official target (owner, 2026-11-24) is the LIFTED
  count MUL (`no_minCE_of_MUL`) or the lifted disjoint choice LiftSDR (`no_minCE_of_liftSDR`); the
  same counts over the narrower pure classes are FALSE for general correct circuits (cxMU_dd:
  5 < 6) and could only hold for a minimal counterexample through s < base. The open step (the
  count MU for the count-set union `UC` (every OR gate false at a zero point Z of some set and
  true at Z + e_u for two u of it, in one monotone face), a gate family that is sufficient on its own because
  Σ d_w ≤ |UC| ≤ s, and that has not failed on any circuit; by induction on points: HEAVY-COUNT
  and LIGHT-COUNT) is a [UPDATE 12:42: over UC the light step is FALSE for general circuits (PAPPUS-JUNK, s = 66, base 18) though UC-MU still holds there; the candidate counted family is F2 (OR gates with a REAL witness: g(Z) = 0, g(Z + e_u) = g(Z + e_u') = 1), which passes the count on everything tested. UPDATE 14:30: the F2 step is false for all correct circuits (TWIN-TREE) and is needed only at cubes where the NOT input depends on ≥ 2 inputs; the other cubes are closed in Lean (CubeF2.lean). LIGHT-COUNT is not an open lemma any more.]
  statement about how the two worlds share gates. Nothing transfers
  along this analogy in either direction: the worlds of section 2 are oracles outside the machine;
  these two are the values of one wire inside the circuit (a restriction, as in gate elimination),
  which is why an argument that uses them does not relativize.
- **A second decomposition of the same count (research, `one-not/board/agents/research-typeA-increment.md`).** Split the
  sets by the NOT's input h at their top point top_w (1 off S_w): a set is FREE if h(top_w) = 0 and TYPE A if
  h(top_w) = 1. Free sets cost nothing: their world-1 classes K_1(w) at top_w are pairwise disjoint and have d_w gates each
  (W1, `disjoint_K1`, `card_K1`, checked), they lie in UC, and every count set of another set at a zero point Z that misses
  S_v avoids K_1(v), in either world (P1/P2: one-line instances of Lemma D, `orClz_disjoint`; paper proofs, not yet Lean
  statements). So MU over UC reduces to the TYPE-A INCREMENT INC_UC_A: the count sets of the type-A sets add
  Σ_{type A} d_w gates outside the free classes. This fits the heavy / light split of the point induction: a heavy point u
  (h(e_u) = 1) lies in EVERY free set (otherwise e_u ≤ top_w forces h(top_w) = 1), so the free sets are exactly the part
  that one world settles, and they sit inside the star of every heavy point; the cross-world work that HEAVY-COUNT (front
  A2, every heavy point) and LIGHT-COUNT (no heavy alive point) pay point by point is, summed over the induction, the
  type-A increment. Proved: the reduction (W1 + P1/P2), and that every class gate of w lies at or before its output
  wire. Open: INC_UC_A itself (tested, 0 failures on 19,828 corpus circuits, 67 repository circuits and the 6-circuit
  barrier suite; tight on 8,442 and on Pasch s = 14). Refuted, so a proof must combine both worlds and may need zero points
  that meet free sets: world 1 alone (848 corpus failures), world 0 alone (7 hand-built circuits), the heavy-point world
  rules, the version over pure classes (cxMU_*), and the version restricted to zero points avoiding every free point
  (68 corpus failures, K4 − e).
- The ladder is the path from 951 to the general targets L-gen-101 to L-gen-103. Each rung adds
  NOT gates, i.e. more worlds per wire (k NOT gates: up to 2^k). The ladder is short: every
  function of n inputs is computed with ceil(log2(n+1)) NOT gates (Markov 1958), and a circuit of
  size s becomes one of size at most 2s + O(n^2 log^2 n) with that many (Fischer 1975). This is now a
  ROW (layer 1): L-gen-104, `Fischer.L104 : Gap.L104` (polynomial 30 (X + 1)^3; `General/FischerMain.lean`),
  with rung n checked as `Fischer.stage1` (SIZE s ⊆ SIZENot (2s + n + 2) n). So a
  superpolynomial bound at rung ceil(log2(n+1)) for an NP function is, in Lean, a general one, and the three
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
