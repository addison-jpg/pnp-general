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
claim     := "claim" expr ["by lean"]
expr      := "correct(" NAME ")"
           | term OP term
           | "forall cubes slack(" NAME ") >= 0"
term      := INTEGER | FUNC "(" NAME ")" | "margin[" STRING "](" NAME ")"
FUNC      := gates | nots | base | witness | orwitness | slack | anyslack
OP        := = | != | < | <= | > | >=
plot      := "plot phi" NAME+ "->" PATH
hunt      := "hunt" STRING SECONDS MAXNOT [SEED] ["&"]
record    := "record" DIR ITEM WORD STRING
WIRE      := POINT | NAME            (a point 0 .. N-1, or an earlier gate name)
WORD      := checked | paper | tested | refuted | open | premise
```

## Meaning

- A **circuit** has N inputs (points). `set I J K -> W` says: the wire W must compute the OR of the inputs I, J, K.
- `base(c)` = sum over the sets of (size − 1). `witness(c)` = gates of any type that are 0 at a zero point of a set and 1 at two of its atoms; `orwitness(c)` = the same for OR gates only. `slack(c)` = `orwitness(c)` − `base(c)`; `anyslack` uses `witness`. A **cube** is a set of points fixed to 1; `slack` at a cube counts only the sets that avoid it.
- `margin["name"](c)` is the margin of a conjecture in `one-not/tools/search/conjectures.py`; below 0 means a counterexample.

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
