# Collation of findings, 2026-11-24 (main session)

Owner, 14:20 UTC: "can we collate current findings please, and pause." Everything is paused.
This file collates what is on `BOARD.md` (THE WALL) and in `951/board/agents/` as of main `6217a97`
plus cTAHG's `0c92c69`. The 951 coordinator has its own collation, `951/FINDINGS_2026-11-24.md`,
local to its session.

Names: every term below is in `NAMES.json` / `NAMES.md` (one flat tree, name -> parent); the old code is in brackets.

Words: **checked** = the Lean checker accepted a proof (axioms `propext`, `Classical.choice`,
`Quot.sound`). **proved (paper)** = a complete written argument, not in Lean. **tested n/N** = a
program ran on N instances. **premise** = an assumption about physics; never a Lean statement.
Nothing here says that P versus NP is settled.

## 0. Literature

Organized in `LITERATURE.md` (ten sections, every entry with its read status and its note). Headline:
951 appears to be new (255 citing works of 28 seed papers, no one-NOT bound for Boolean sums).

## 1. Problem 951 (rung 1 of the NOT gate ladder)

Statement: sets S_w with |S_w| ≥ 2 and pairwise intersections of size ≤ 1; a circuit of AND and OR
gates and one NOT gate computes every sum of a set; then #gates ≥ the monotone optimum (base) = Σ(|S_w| − 1).
In Lean, `L_meta_951` rests on one unproved declaration, `no_minCE` (no minimal counterexample).

### 1.1 Checked

| Result | Where |
|---|---|
| 951 for every circuit whose lifted outputs win the certificate game (Theorem G) | `W951/UGame.lean`: `liftSDR_of_ugame`, `no_minCE_of_ugame`; won in the cases G1, G0, all points heavy, all sets type B |
| 951 if at every cube the NOT input is local (one input, or constant on the cube) or the point step for real-witness gates holds | `W951/CubeF2.lean:353` `no_minCE_of_gainF2_or_cubeLocal` |
| 951 when the NOT gate reads an input (h = x_p), no minimality | `NotVarF2` (`muF2_of_notVar`) |
| 951 when all sets have size ≤ 3; Two-World reduction; partial bound; union-find merge count (Lemma M) | `small3_bound`, `TwoWorld.lean`, `PartialBound.lean`, `MergeRun.lean`, `CanonClass.lean` |
| Structural facts of a minimal counterexample: R2, R3, R4, R5', R+ | `MinCERed` |

### 1.2 Proved (paper), refereed, not in Lean

- Proposition S: the certificate game is the exact reach of any argument that reads only gate values at the
  test points.
- Theorem D: for DD-normal outputs with all |S_w| ≥ 3, a winning selection never mixes worlds.
- Lemma T: at a common frame a merge gate splits every set it serves by one colouring; it forbids
  odd cycles of 2-point traces and nothing else.
- Lemma K (constant-h cube classes); the staircases of Theorem G's corollaries.

### 1.3 Refuted (witness in `951/data/witnesses/`, row in `951/DEAD_ENDS.md`)

| Statement | Witness |
|---|---|
| Point deletion (x_v := 0) | Fano formula with an unused NOT gate (FANO-FORMULA) |
| The step for the one-face witness gates (UC); LIGHT-COUNT over UC | Pappus configuration with junk gates (PAPPUS-JUNK) |
| disjoint representatives and the count over pure classes (PureSDR, MU), for all correct circuits | two two-world sets sharing one merge gate (cxMU_dd) |
| Price inequality over real merge sets, without minimality | star of four pairs with a threshold NOT input (STAR4, STAR4b) |
| The point step for real-witness gates (F2 step) for all correct circuits | twin balanced OR trees with leaf junk (TWIN-TREE, TWIN-TREE-N) (the NOT gate reads one input, so these are closed by `CubeF2`) |
| The point step for real-witness gates (F2 step), and the step for cone-restricted witness gates (F4, F5), under the six checked facts of a minimal counterexample (R1 to R5', R+) at a cube where the NOT input depends on ≥ 2 inputs | matched twin trees with a 14-input NOT input (MATCH-C; n = 16, 55 gates, base 23). Not a 951 counterexample: the count holds at 59,706 of 59,706 cubes and its certificate game is won |

### 1.4 Open

1. **The circuits that lose the certificate game.** On the barrier suite: `cxMU_dd` and `cx44_1_junk` (19 of 21
   win). Smallest lost instance: sets {0,1,2}, {0,3,4}, h = x1 ∨ x3, where a violation is a
   3-gate configuration. At n = 5, 10,095 of 113,685 pairs (sets, h) lose. cTAHG names three 4-sets in a triangle (`cxT2`) as
   the hard case: no gate-saving rewiring in 1,679 tries, certificate game lost, disjoint representatives over real merge sets (MergeSDR) hold.
2. **The point step for real-witness gates (F2 step) among circuits with no gate-saving rewiring (R6).** R6 (cTAHG): a minimal counterexample admits no
   rewiring of a gate input that leaves a gate unread. MATCH-C is reducible by R6 (the NOT gate can
   read x_{u0} ∨ x_{a0}; main reran this: correct, 55 → 54 read gates). cTAHG reports the step
   holding at 46 to 49 gates. R6 is in Lean (`MinCE.no_dead`, `MinCE.no_rewire`, `W951/MinCERewire.lean`, cTAHG 20e06fa); script `951/tools/kill_tests/rewire_r6.py` and note `951/board/agents/cTAHG-ddcore.md` on main.
3. A mixed induction (x_v := 0 at some points, x_v := 1 at others) is not refuted; evidence: two
   circuits, one cube each.

Tested, no failure: the count real-witness gates ≥ monotone optimum of the cube (|F2(Q)| ≥ base(Q)) on every instance of every suite (19,534 suite
instances; 80,198 Fano circuits × 128 cubes, coord); the point step for real-witness gates at 6,320 cubes with an essential
NOT whose input depends on ≥ 2 inputs (dwV8p); the lifted price LP on 8,378 circuits.

## 2. General circuits (L-gen) and the ladder

- Checked: L-gen-104 (Markov and Fischer: `SIZE s ⊆ SIZENot (2s+n+2) n`), so a superpolynomial
  bound at rung ⌈log₂(n+1)⌉ is a general bound. L-gen-005 / 006: C(x ⊕ f) ≥ max + 3, and = min + 4
  when C(f) ≠ C(¬f). Size hierarchy (circuit half of Kannan). Kannan's Σ3 half is reduced to a
  polynomial-time check, with circuit evaluation checked polynomial-time (`cpt_circEval`).
  SAT ∉ SIZE((a/b)n + c) for a/b < 5/4.
- Refuted in Lean: L-meta-574 at h = 1.
- Open: L-gen-101 to 103; the case C(f) = C(¬f) of the XOR extension (neither proved nor refuted;
  SAT finds no counterexample with m ≤ 6); the rest of the Kannan machine.
- Density barrier (GeNeRALIZE): the edge-function route to a superlinear general bound needs a new
  idea on dense C4-free graphs.

## 3. Quantum gravity (L-qg)

47 rows checked: gate-word counting and complexity growth; P = NP inverts every polynomial-time
length-preserving function (L-qg-103); P, NP, coNP ⊆ P_CTC (Deutsch model); the five-qubit code and
the six-qubit perfect state; a fixed-point lemma for Deutsch consistency. Open gaps: L-qg-115, 116,
119, 169 (P_CTC ⊆ EXP). Physics premises (complexity = volume, the holographic bound, closed
timelike curves) appear in no Lean statement.

## 4. How the parts fit (three layers, `SYNTHESIS.md`, `BIGPICTURE.md`)

- Layer 1, theorems: the checked rows above.
- Layer 2, certificates and data: witnesses, kernel-checked SDR certificates, the suites.
- Layer 3, premises and maps: physics premises; the barriers (relativization, algebrization, natural
  proofs). The physics side fixes the model of computation; it cannot settle P versus NP. The
  ladder: rung 0 (monotone) is known, rung 1 is 951, rung ⌈log₂(n+1)⌉ is general circuits.
- One meeting point inside 951: every open item in 1.4 concerns a NOT input that depends on at
  least two inputs.

## 5. Corrections made today (so nobody rebuilds on the old lines)

- "The F2 GainOne hypothesis is false" → false for all correct circuits only; the Lean route needs
  it only at non-local cubes (coord).
- "The step is false under all local MinCE facts" (MATCH-C) → holds for the six checked facts of a minimal counterexample (R1 to R5', R+) only; R6
  reduces MATCH-C (cTAHG).
- LIGHT-COUNT is refuted, not open. PureSDR is not the target; the target is the lifted forms.

## 6. State of the repository

- `addison-jpg/pnp-general` is public. A ruleset ("please be nice", 14:06 UTC) requires pull
  requests, signed commits, linear history and status checks on every branch; no session can push.
  Local, unpushed: main's wall correction and this file; cTAHG's `rewire_r6.py` and
  `cTAHG-ddcore.md`; coord's `FINDINGS_2026-11-24.md`.
- Notes are indexed by part of the route in `951/board/agents/INDEX.md`; 10 notes are marked
  `OFF THE ROUTE`, 38 are candidates for a second pass.
- Not checked by main: the proofs of Theorem G's paper items, cTAHG's reduction of MATCH-C to 45
  gates, scaffold's k = 3 test, the L-gen and L-qg rows of other sessions.
