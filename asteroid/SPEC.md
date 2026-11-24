# asteroid: the language, exactly

A program is a text file `NAME.ast`. Lines are read top to bottom. `#` starts a comment. Blank lines are ignored.

```
program   := line*
line      := circuit | let | show | claim | plot | hunt | record
circuit   := "circuit" NAME N NEWLINE (gate | out)* "end"
gate      := NAME "=" ("or" | "and") WIRE WIRE  |  NAME "=" "not" WIRE
out       := "set" POINT+ "->" WIRE
let       := "let" NAME "=" "load" PATH
show      := "show" NAME
claim     := "claim" expr ["by lean"]   (also "claim!": forced to Lean even if Python says false)
expr      := "correct(" NAME ")"
           | term OP term
           | "forall cubes slack(" NAME ") >= 0"
           | "mslack(" NAME "," SET "," SET ")" OP INTEGER                 (extension ext_mixed)
           | "forall states mslack(" NAME ") >= 0"                          (extension ext_mixed)
           | "forall states mixedstep(" NAME ")"                            (extension ext_mixed)
SET       := "{" POINT* "}"            (first SET = Q, points fixed to 1; second = R, points fixed to 0; disjoint)
term      := INTEGER | FUNC "(" NAME ")" | "margin[" STRING "](" NAME ")"
FUNC      := gates | nots | base | witness | orwitness | slack | anyslack
OP        := = | != | < | <= | > | >=
plot      := "plot phi" NAME+ "->" PATH
corpus    := "corpus" NAME "=" GLOB ["where n <=" K] ["where nots <=" T]          (asteroid/ext_corpus.py)
forall    := "claim forall c in" NAME ":" expr ["by lean"]                          (expr written with the variable c)
count     := "count c in" NAME ":" expr
hist      := "plot hist" FUNC NAME "->" PATH
prove     := "prove" STRING "by" TACTIC                                              (asteroid/ext_eureka.py; STRING is a Lean proposition)
hunt      := "hunt" STRING SECONDS MAXNOT [SEED] ["&"]
record    := "record" DIR ITEM WORD STRING
WIRE      := POINT | NAME            (a point 0 .. N-1, or an earlier gate name)
WORD      := checked | paper | tested | refuted | open | premise
```

## Meaning

- A **circuit** has N inputs (points). `set I J K -> W` says: the wire W must compute the OR of the inputs I, J, K.
- `base(c)` = sum over the sets of (size − 1). `witness(c)` = gates of any type that are 0 at a zero point of a set and 1 at two of its atoms; `orwitness(c)` = the same for OR gates only. `slack(c)` = `orwitness(c)` − `base(c)`; `anyslack` uses `witness`. A **cube** is a set of points fixed to 1; `slack` at a cube counts only the sets that avoid it.
- `corpus W = GLOB` loads every circuit of every matching `.json` (one circuit) or `.jsonl` (one per line, bare or under the key `circuit`) file; files that are not circuits, are incorrect, or break the `where` limits are skipped and counted in the printed line. `claim forall c in W: EXPR` evaluates EXPR with `c` replaced by each circuit, in Python, and prints one summary line (TRUE on all, or FALSE with the first failing files); it is true only if it holds on all. With `by lean` each circuit is registered under a generated name `W_<i>` and one Lean claim per circuit goes into the one module; refused above 40 circuits, or above n = 8 for `forall cubes`. `count c in W: EXPR` prints how many satisfy EXPR. `plot hist FUNC W -> F.png` histograms FUNC(c).
- `margin["name"](c)` is the margin of a conjecture in `one-not/tools/search/conjectures.py`; below 0 means a counterexample.

## Mixed states (extension `asteroid/ext_mixed.py`; Lean: `one-not/lean/PEqualNP/W951/AsteroidMixed.lean`)

- A **mixed state** (Q, R): disjoint sets of points, the points of Q fixed to 1 and those of R fixed to 0. There are 3^n states.
- The sets of the restricted problem are S_w ∖ R for the w with S_w ∩ Q = ∅ and |S_w ∖ R| ≥ 2 (**alive**). `base(Q, R)` = sum over alive w of (|S_w ∖ R| − 1).
- An OR gate g is a **witness** at (Q, R) if for some alive w there is an input Z with Z ⊇ Q, Z ∩ R = ∅, Z ∩ S_w = ∅ and two points u ≠ u' of S_w ∖ R with g(Z) = 0, g(Z + e_u) = g(Z + e_u') = 1. `mslack(Q, R)` = #witness gates − base(Q, R). `mslack(∅, ∅)` is `slack`.
- **MixedStep** at a state with base > 0: some point v outside Q ∪ R such that moving v into Q (a 1-step) or into R (a 0-step) gives a state whose mslack is ≤ the current mslack, where the step must **pay**: the base of the new state is strictly smaller than the base of the current one (exactly `continuous.py`: `cmd_mixed` and `mixed_margin`, which take the least mslack change over the paying steps and ask it to be ≤ 0). Python: `claim forall states mixedstep(c)` is true iff `mixed_margin(c)` is ≤ 0 at the states with positive base. Lean: `mixedStepAll`.
- `claim mslack(c, {q…}, {r…}) OP k`: one state (Lean: `mslackGe`, `mslackLe`, `mslackVal`). `claim forall states mslack(c) >= 0` (Lean: `mslackNonnegAll`). `claim forall states mixedstep(c)` (Lean: `mixedStepAll`). `claim!` forces any of them to Lean.
- Python cross-check: every single-state claim is compared with a naive direct implementation (`direct_parts`); `python3 -I asteroid/tests/test_mixed.py` compares all states and MixedStep on two circuits.

## prove (extension `asteroid/ext_eureka.py`)

`prove "P" by T` writes `theorem asteroid_prove : P := by T` into a scratch module (import Mathlib) and runs `lake env lean` in `one-not/lean`. Accepted = true claim, rejected = false claim (exit code 1). Skipped without effect under `--no-lean` or without `lake`. T is one of decide, omega, simp, aesop, norm_num, rfl, simp_arith, trivial, `decide +kernel`. It is a stand-in; no tool called Eureka was found (`EUREKA.md`).

## Engines

| Step | Engine |
|---|---|
| every `claim` is evaluated when its line is read | Python |
| every `claim … by lean` that Python found true is written as a theorem into `one-not/lean/PEqualNP/W951/Asteroid_<program>.lean` and built once at the end, each theorem by `decide +kernel` | Lean |
| `plot` | matplotlib |
| `hunt … &` | a background Python process |

Lean forms: `correct`, `witness`, `orwitness`, `slack` against an integer (or `base` for the two counts), and `forall cubes slack ≥ 0`.

What a Lean form says about the project's circuits (`Circuit.eval`, `F2`, `baseDQ`): `one-not/lean/PEqualNP/W951/AsteroidSound.lean` (`correctB_sound_project`) and `AsteroidSound2.lean` (`card_F2_eq_orWitnessAt`, `slackNonnegAll_sound`); table in `README.md`, section "What the Lean theorems mean". Not covered: `witness`.

## Result of a run

Exit code 0 when every claim is true and (unless `--no-lean`) the Lean module builds; 1 otherwise. A `record` writes a finding to `findings.jsonl` in DIR, citing the program and the Lean theorem, only on exit code 0.

```bash
python3 -m asteroid run asteroid/examples/first.ast
python3 -m asteroid test            # every program under asteroid/examples
python3 -m asteroid test --no-lean  # Python and plots only (what GitHub Actions runs on every push)
```
