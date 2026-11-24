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

Axioms of the generated theorems: `propext` only.

## What is not there yet

- The Lean statements are about asteroid's own bit-parallel evaluator. The theorem tying it to the project's
  `Circuit.eval` (and so to `no_minCE`) is not proved.
- Python evaluates first and a false claim never reaches Lean, so Lean has not yet been seen to reject a claim
  Python accepted.
- `forall cubes … by lean` is brute force: fine at 7 inputs, not at 14 (the twin trees have 16,384 cubes).
- No mixed slack (points set to 0 as well as 1), no quantifier over circuits, no functions defined in a script.
