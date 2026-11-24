# asteroid

A small language over three engines (owner, 2026-11-24: "lean for brute force, python for speed/background,
and matplotlib as an available tool... take what they've built and integrate it into a novel, relatively
simple, framework"; "please call it asteroid").

| Engine | Does | Built on |
|---|---|---|
| Python | evaluates every claim at once, searches, runs background jobs | `one-not/tools/search` |
| Lean | brute force in the kernel: a `by lean` claim becomes a theorem proved by `decide +kernel` | `one-not/lean/PEqualNP/W951/Asteroid.lean`, `SearchCheck.lean` |
| matplotlib | pictures | `asteroid/out/*.png` |

An object is written once; asteroid sends the same object to all three.

```
circuit tiny 4            # 4 inputs, named 0 1 2 3
  a = or 0 1
  b = or a 2
  c = or 2 3
  set 0 1 2 -> b          # the output for the set {0,1,2} is the wire b
  set 2 3 -> c
end
claim correct(tiny) by lean
claim slack(tiny) = 0 by lean
claim forall cubes slack(tiny) >= 0 by lean

let fano = load one-not/data/witnesses/fano_formula.json
claim forall cubes slack(fano) >= 0 by lean
plot phi tiny fano -> asteroid/out/first.png
hunt "C4 count (flip classes)" 20 4 1 &
record one-not/data/witnesses C2 checked "…"
```

```bash
python3 -m asteroid run asteroid/examples/first.ast
python3 -m asteroid test
```

The exact grammar is in [`SPEC.md`](SPEC.md). On every push that touches the language or a program, GitHub Actions runs `python3 -m asteroid test --no-lean` (workflow `.github/workflows/asteroid.yml`); the Lean kernel job is started by hand.

## The language

| Verb | Meaning |
|---|---|
| `circuit NAME N` … `end` | a circuit written in the script: gates `W = or X Y`, `W = and X Y`, `W = not X`; outputs `set I J K -> W` |
| `let NAME = load FILE.json` | a circuit from a file |
| `show NAME` | gates, NOT gates, base, witness counts, correctness |
| `claim EXPR [by lean]` | `correct(NAME)`, or `F(NAME) OP RHS` with `F` in `gates nots base witness orwitness slack anyslack margin["conjecture"]`, `OP` in `= != < <= > >=` |
| `claim forall cubes slack(NAME) >= 0 [by lean]` | slack at every cube; with `by lean` the kernel checks all 2^n cubes |
| `corpus NAME = GLOB [where n <= K] [where nots <= T]` | load every correct circuit of the matching `.json` / `.jsonl` files (extension `ext_corpus.py`) |
| `claim forall c in NAME: EXPR [by lean]` | EXPR with the variable `c` on every circuit of the corpus; one summary line; `by lean` adds one theorem per circuit (at most 40 circuits) |
| `count c in NAME: EXPR` | how many circuits satisfy EXPR |
| `plot hist FUNC NAME -> FILE.png` | histogram of FUNC(c) over the corpus |
| `claim mslack(NAME, {Q}, {R}) OP k`, `claim forall states mslack(NAME) >= 0`, `claim forall states mixedstep(NAME)` | mixed states: points of Q fixed to 1, points of R fixed to 0; MixedStep = at every state with positive base some paying 0-step or 1-step has mslack no larger (extension `ext_mixed.py`; definitions in `SPEC.md`) |
| `prove "STATEMENT" by TACTIC` | stand-in for "Lean Eureka" (see `EUREKA.md`): a Lean proposition proved with one of decide, omega, simp, aesop, norm_num, rfl; the kernel accepts or rejects; skipped under `--no-lean` (extension `ext_eureka.py`) |
| `conjecture NAME: EXPR` | a statement with the circuit variable `c`, written once; then `NAME(X)` is a claim, `forall c in W: NAME(c)` runs it over a corpus, and `hunt NAME …` searches against it |
| `hunt NAME SECONDS MAXNOT [SEED]` | mutation search for a circuit where the conjecture fails; a hit is bound to `NAME_cex` and saved in `asteroid/out/` |
| `plot phi NAME … -> FILE.png` | expected slack Φ(p) and the level means |
| `hunt "CONJECTURE" SECONDS MAXNOT [SEED] [&]` | mutation search; `&` puts it in the background |
| `record DIR ITEM WORD "STATEMENT"` | a finding in the board tree; skipped if a claim is false or Lean did not build |

Python proposes, Lean decides: a `by lean` claim counts only when the generated module
`one-not/lean/PEqualNP/W951/Asteroid_<script>.lean` builds. Lean forms exist for `correct`, `witness`,
`orwitness`, `slack` (at the empty cube) and `forall cubes slack ≥ 0`.

## Runs so far

| Script | Python | Lean kernel | Time |
|---|---|---|---|
| `examples/first.ast` | 7 claims true | 8 theorems, incl. slack ≥ 0 at all 16 cubes of `tiny` and all 128 cubes of the Fano formula | 14 s |
| `examples/many_not.ast` | 8 claims true | 5 theorems (the 4-NOT-gate circuit is correct and has 5 witness gates, below base 6) | 11 s |
| `examples/corpus.ast` | 3 claims true over 15 witness circuits (n ≤ 9); counts: 2 of 15 tight, 0 of 4 nonlocal files at or above base | 30 theorems (correct and slack ≥ 0 on each of 15 circuits) | 21 s |
| `examples/mixed.ast` | 11 claims true; mslack ≥ 0 and MixedStep at all 243 states of the n = 5 circuit `ess_rand_clean_744` (1 NOT gate) and all 81 states of a 4-input circuit written in the script; Python cross-checked against a direct implementation (`tests/test_mixed.py`) | 11 theorems, incl. `mixedStepAll` at 243 and 81 states | 7 s |

Axioms of the generated theorems: `propext` only.

## What the Lean theorems mean

A `by lean` theorem is a statement about asteroid's bit tables. These theorems, proved once for every circuit
(axioms `propext`, `Classical.choice`, `Quot.sound`), turn it into a statement about the project's circuits
(`Defs/CircuitLowerBounds.lean`: `Circuit.eval`). Files `one-not/lean/PEqualNP/W951/AsteroidSound.lean` and
`AsteroidSound2.lean`. `C.toGates` is the circuit as a gate list of the project, `C.setFin w` is set number `w`
as a `Finset (Fin n)`, `maskOf Q` is the cube `Q` as a bit mask.

| Theorem | Says |
|---|---|
| `tables_testBit` | for every input vector `r < 2^n`, bit `r` of the table of a wire is the value of that wire at `r` (`Circ.wiresAt`) |
| `correctB_sound` | `correctB C = true` ⇒ at every `r < 2^n` every output wire is the OR of the bits of `r` over its set |
| `wiresAt_eq_wires` | that pointwise evaluation is the project's `Circuit.wires` on `C.toGates` |
| `toGates_wf` | `C.toGates` has only AND, OR, NOT gates with at most two inputs |
| **`correctB_sound_project`** | `correctB C = true` and one output per set ⇒ `Circuit.eval ⟨C.toGates, C.outs.getD w 0⟩ (List.ofFn x) = decide (∃ v ∈ C.setFin w, x v = true)` for every set `w` and input `x`: the correctness hypothesis of `L_meta_951` |
| `hasWitnessAt_iff_F2Wit` | a table has an asteroid witness above the cube `Q` ⇔ the wire has a real witness (`F2Wit`) for a set alive at `Q` |
| **`card_F2_eq_orWitnessAt`** | `orwitness` at the cube `Q` is `(F2 C.toGates C.setFin Q).card` (`F2Induct.lean`) |
| `baseAt_eq_baseDQ` | `base` at the cube `Q` is the project's `baseDQ C.setFin ∅ Q` |
| **`slackNonnegAll_sound`** | `forall cubes slack(c) >= 0` ⇒ `baseDQ … Q ≤ (F2 … Q).card` at every `Q` |
| `MUF2_of_slackGe`, `base_le_gates_of_slackGe` | `slack(c) >= 0` ⇒ `MUF2`, and so Σ (\|S\| − 1) ≤ number of gates of `c` |

The last five need `SetsOk`: every set is written without a repeated point and with points below N (asteroid
counts list positions and reads table bits; with a repeated point or a point ≥ N the two counts can differ).
For `examples/first.ast`: `first_ast_tiny_concrete` (the three OR gates of `tiny` compute `x0 ∨ x1 ∨ x2` and
`x2 ∨ x3` under `Circuit.eval`) and `first_ast_tiny_slack`.

## Every run is also stated in the project's definitions

After the main module builds, asteroid writes a second one, `Asteroid_<program>_sound.lean`, and builds it too.
It restates each claim that has a soundness theorem (`AsteroidSound.lean`, `AsteroidSound2.lean`):

| Claim in the program | Theorem in the second module |
|---|---|
| `correct(c) by lean` | the project's `Circuit.eval` on the translated gates computes the OR of every set, on every input (the correctness hypothesis of `L_meta_951`) |
| `forall cubes slack(c) >= 0 by lean` | `baseDQ ≤ |F2|` at every cube, in the project's `F2` and `baseDQ` |
| `slack(c) >= 0 by lean` | the sum of (\|S\| − 1) is at most the number of gates of this circuit |

The well-formed-sets condition is proved for each circuit by `decide`. Claims about `witness` (gates of any
type) and about mixed slack have no soundness theorem yet and stay statements about asteroid's evaluator.

## Cheap theorems on top (AsteroidCheap.lean)

Short theorems (`one-not/lean/PEqualNP/W951/AsteroidCheap.lean`, `AsteroidCheapMixed.lean`), each connecting two
things already proved. Axioms of every one: `propext`, `Classical.choice`, `Quot.sound`. None uses the open
statement `no_minCE`; where it appears it is a hypothesis.

| Theorem | What it says |
|---|---|
| `not_isCE_of_slackGe`, `not_minCE_of_slackGe` | a literal with well-formed sets and `slack(c) >= 0` is not a counterexample to the Theorem, and not a minimal one, for any output wires |
| `slack_eq_asteroid` | the Lean `slack` (ContinuousAttach) at the cube `Q` is asteroid's `orWitnessAt − baseAt` at the mask of `Q` |
| `slack_nonneg_of_slackNonnegAll`, `Phi_nonneg_of_slackNonnegAll` | `forall cubes slack(c) >= 0` gives `0 ≤ slack` at every cube and `0 ≤ Φ(p)` for every `p` in `[0, 1]` |
| `F2_chain_sum`, `orWitnessAt_chain_sum` | along an increasing chain of cubes: count at the start = count at step `N` + gates lost at each step |
| `hypsB`, `hypsB_sound` | a Bool checker for the other hypotheses of `L_meta_951` (well-formed sets, an output per set, at least one gate, sets of ≥ 2 points, two sets share ≤ 1 point, at most one NOT gate) and its soundness for `C.setFin`, `C.toGates` |
| `isCE_of_checks`, `exists_minCE_of_hunt_hit`, `not_LMeta951Stmt_of_hunt_hit` | a literal passing `correctB` and `hypsB` with gates < base is a counterexample (`IsCE`), yields a minimal counterexample, and refutes the statement of `L_meta_951` (`LMeta951Stmt`, copied verbatim): a `hunt` hit is a formal counterexample |
| `base_le_gates_of_no_minCE`, `base_le_gates_of_LMeta951Stmt` | if there is no minimal counterexample (hypothesis), or the statement of `L_meta_951` holds, every literal passing `correctB` and `hypsB` has base ≤ gates, with no further work |
| `first_ast_fano_hypsB` | `hypsB fano = true` for the Fano circuit of `examples/first.ast`, by `decide +kernel` |
| `baseMixed_zero`, `hasWitnessMixedNaive_zero`, `mslackVal_zero`, `mslackGe_zero` (AsteroidCheapMixed) | at `r = 0` the mixed base is the base, the naive mixed witness test is `hasWitnessAt`, and, given the kernel check `naiveAgrees C`, `mslack` at `(q, 0)` is `slack` at `q` |

Not done: `asteroid.py` does not yet emit `hypsB c` as a claim; the bit-parallel mixed witness test is tied to
the naive one only per circuit (`naiveAgrees`). Notes: `one-not/board/agents/fable-cheap-proofs.md`.

## What is not there yet

- The soundness theorems are applied by hand: `asteroid.py` still writes only the statements about its own
  evaluator (`correctB c = true`, …). It does not yet write the corollary in the project's terms next to each
  claim, nor the proof of `SetsOk`. One hand-written instance exists (`first_ast_tiny_concrete`, `first_ast_tiny_slack`).
- `witness` (gates of any type, `witnessCount`) is tied to nothing: the project's `F2` counts OR gates only.
- `correct(c)` gives only the correctness hypothesis of `L_meta_951`. Its other hypotheses (every set has at
  least 2 points, two sets share at most one point, at most one NOT gate) are not asteroid claims.
- Python evaluates first and a false claim never reaches Lean, so Lean has not yet been seen to reject a claim
  Python accepted.
- `forall cubes … by lean` is brute force: fine at 7 inputs, not at 14 (the twin trees have 16,384 cubes).
- No functions defined in a script.
- Mixed slack (`ext_mixed.py`, `AsteroidMixed.lean`) is brute force over all 3^n states: the kernel decides `forall states mslack ≥ 0` and `forall states mixedstep` up to n = 7 (2,187 states; 33 s and 49 s, about 5 and 7 GB of memory, Fano formula). n = 8 (6,561 states) would need roughly 3 times the states and the memory: not tried.

## The proof as programs

Programs in [`programs/`](programs/README.md), one per group of numbered items; all exit 0 and `python3 -m asteroid test` runs them.

| Program | README items | What it checks | Python claims / Lean theorems | Time (Lean / no Lean) |
|---|---|---|---|---|
| `programs/theorem.ast` | Theorem, D5, D8, T3, T4 | all 15 witness circuits with n <= 9: correct (kernel), `gates >= base`, the count `slack >= 0` (kernel), 0 tight by gates / how many tight by count; a one-NOT circuit written in the script with `forall cubes slack >= 0` (16 cubes) and the Fano formula (128 cubes) in the kernel | 10 / 33 | 49 s / 1 s |
| `programs/refuted.ast` | section 5: C2 (twin trees, matched twin trees), pointwise 0-step (Pappus), induction on 0 (Fano), pure-class SDR (cxMU), price inequality (star4b), C4w | seven blocks, each with its counterexample file; the C2 step margin is below 0 on twin_tree_f2step and match_c_k7, the any-gate witness count is below base on general_count_below_base_min / t4 (kernel for the 4-NOT circuit); the count and `gates >= base` hold on every one | 28 / 2 | 32 s / 18 s |
| `programs/open.ast` | C1/C2/C4, the open step of `no_minCE` | conjectures `count`, `mixed` (MixedStep at all states), `flip` (C4 flip classes), `c2norewire` over 14 circuits, then `hunt` 8 s each (no counterexample) | 4 / 0 (3 hunts) | 30 s / 30 s |
| `programs/ladder.ast` | T6, C4, C4w, Theorem | rung 0 (circuits with no NOT gate: count >= 0 and `gates >= base`, kernel) against the four many-NOT files (all have `witness < base`, all have `gates >= base`, flip classes >= 0) | 10 / 6 | 15 s / 1 s |
| `programs/pictures.ast` | D8, L5 | plot phi for the twin tree, MATCH-C, Pappus, Fano; histograms of slack and gates over the corpus | 1 / 0 (6 PNGs in `asteroid/out/`) | 2 s / 2 s |

`python3 -m asteroid test` runs them (with Lean 2 min 44 s for examples and programs together; `--no-lean` 68 s).

### What the language cannot yet say (`# WISH:` lines in the programs)

1. Implication / hypothesis in a corpus claim: `forall c in W: nots(c) <= 1 -> gates(c) >= base(c)`, and the Theorem's other hypotheses (`sets_ok(c)`: every set has at least 2 points, two sets share at most one point).
2. Mixed-state quantifiers over single points: `exists v: mslack(c, {}, {v}) < 0`; pointwise gain and cost of a 0-step and 1-step (`gain0`, `cost0`, `gain1`, `cost1`), needed for the Pappus row and the induction-on-0 row.
3. Merge sets, pure classes and a system-of-distinct-representatives test (`sdr(pure_classes(c))`), and the fractional price of a gate (cxMU and star4b rows).
4. A negated claim over a corpus (`forall c in N: not (...)`) instead of two counts.
5. A Lean form for `gates(c) >= base(c)` (the Theorem has no kernel statement; only the OR-only count does) and for `witness` soundness.
6. `C3 two-point step` at k = 2 on the matched twin trees at n >= 16 is too slow in the registry (minutes), so the C3_k refutation is not shown.
7. Kernel claims for n = 14 to 16 (twin trees): tables of 16,384 inputs time out (a `correct` claim on the twin tree took more than 2 minutes).
