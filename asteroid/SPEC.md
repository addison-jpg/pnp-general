# asteroid: the language, exactly

A program is a text file `NAME.ath`. Lines are read top to bottom. `#` starts a comment. Blank lines are ignored.

```
program   := line*
line      := circuit | let | save | show | claim | plot | corpus | forall | count | conjecture | hunt | prove | verify | theorem | levelmeans | record | seq | check | frame
circuit   := "circuit" NAME N NEWLINE (gate | out)* "end"
gate      := NAME "=" ("or" | "and") WIRE WIRE  |  NAME "=" "not" WIRE
out       := "set" POINT+ "->" WIRE
let       := "let" NAME "=" "load" PATH            (PATH ends in .bench: the format of BENCH.md, asteroid/ext_bench.py; or in .json)
save      := "save" NAME "->" PATH                (PATH ends in .bench; asteroid/ext_bench.py)
show      := "show" NAME
claim     := ("claim" | "claim!") expr ["by lean"]   ("claim!": forced to Lean even if Python says false, to watch the kernel reject it)
expr      := "correct(" NAME ")"
           | term OP term
           | "not" expr                                                      (Python only)
           | "if" expr "then" expr | expr "and" expr                         (Python only; extension ext_edges)
           | "hyps(" NAME ")" ["=" ("true" | "false")]                       (extension ext_edges; Lean: hypsB)
           | "theorem(" NAME ")"                                             (extension ext_edges; hyps and correct imply gates >= base)
           | "forall p phi(" NAME ") >= 0"  |  "monotone phi(" NAME ")"      (extension ext_continuous)
           | "forall cubes slack(" NAME ") >= 0"
           | "mslack(" NAME "," SET "," SET ")" OP INTEGER                 (extension ext_mixed)
           | "forall states mslack(" NAME ") >= 0"                          (extension ext_mixed)
           | "forall states mixedstep(" NAME ")"                            (extension ext_mixed)
SET       := "{" POINT* "}"            (first SET = Q, points fixed to 1; second = R, points fixed to 0; disjoint)
term      := INTEGER | FUNC "(" NAME ")" | "margin[" STRING "](" NAME ")" | "phi(" NAME "," RATIONAL ")" | CONJECTURE "(" NAME ")"
FUNC      := gates | nots | base | witness | orwitness | slack | anyslack | flip | flipclasses | flipslack   (last three: ext_edges, Python only)
OP        := = | != | < | <= | > | >=
plot      := "plot phi" NAME+ "->" PATH
corpus    := "corpus" NAME "=" GLOB ["where n <=" K] ["where nots <=" T]          (asteroid/ext_corpus.py)
forall    := "claim forall c in" NAME ":" expr ["by lean"]                          (expr written with the variable c)
count     := "count c in" NAME ":" expr
hist      := "plot hist" FUNC NAME "->" PATH
prove     := "prove" STRING "by" TACTIC                                              (asteroid/ext_eureka.py; STRING is a Lean proposition)
conjecture := "conjecture" NAME ":" expr                                           (expr written with the variable c; NAME(X) is then a term)
hunt      := "hunt" (STRING | NAME) SECONDS MAXNOT [SEED] ["&"]                    (NAME: a conjecture of the script, a hit is bound to NAME_cex)
verify    := "verify lean" DIR ["within" SECONDS]                                   (asteroid/ext_verify.py)
theorem   := "theorem" FULL_NAME "from" MODULE "in" DIR                              (asteroid/ext_verify.py)
levelmeans := "levelmeans" NAME                                                      (asteroid/ext_continuous.py)
record    := "record" DIR ITEM WORD STRING
seq       := "seq" NAME "=" ("from" PATH [STRING] | "run" STRING [STRING] | LIST)    (asteroid/ext_finite.py)
check     := "check" STRING                                                          (asteroid/ext_finite.py; STRING is "python3 -I path.py [args]")
claim     := "claim" NAME "=" LIST | "claim" NAME "matches" NAME [FORM] | "claim formula" NAME "=" STRING ["from" INTEGER]   (ext_finite)
FORM      := as-is | diff | partial | plus1
frame     := "frame" STRING "reading" STRING "->" CLAIMREF "label" WORD ["reach" INTEGER] ["cost" NUMBER]   (asteroid/ext_frame.py)
CLAIMREF  := LINE | PATH | "none"          (LINE: an earlier claim or check of this file; PATH: another .ath file)
LIST      := "[" INTEGER ("," INTEGER)* "]"
EXPR      := integers, n, + - * // ** ( ), postfix ! and !!, "C(" EXPR "," EXPR ")", "sum(" VAR "," EXPR "," EXPR "," EXPR ")"
WIRE      := POINT | NAME            (a point 0 .. N-1, or an earlier gate name)
WORD      := checked | checked-finite | checked-infinite | paper | tested | refuted | open | premise
```

## Meaning

- A **circuit file** is an ISCAS `.bench` netlist with `#@ or OUT = IN IN …` directives for the sets; the grammar and the mapping to (n, sets, gates, outs) are in [`BENCH.md`](BENCH.md). `save` writes inputs as `x0 x1 …` and gates as `g0 g1 …`.
- A **circuit** has N inputs (points). `set I J K -> W` says: the wire W must compute the OR of the inputs I, J, K.
- `base(c)` = sum over the sets of (size − 1). `witness(c)` = gates of any type that are 0 at a zero point of a set and 1 at two of its atoms; `orwitness(c)` = the same for OR gates only. `slack(c)` = `orwitness(c)` − `base(c)`; `anyslack` uses `witness`. A **cube** is a set of points fixed to 1; `slack` at a cube counts only the sets that avoid it.
- `corpus W = GLOB` loads every circuit of every matching `.json` (one circuit) or `.jsonl` (one per line, bare or under the key `circuit`) file; files that are not circuits, are incorrect, or break the `where` limits are skipped and counted in the printed line. `claim forall c in W: EXPR` evaluates EXPR with `c` replaced by each circuit, in Python, and prints one summary line (TRUE on all, or FALSE with the first failing files); it is true only if it holds on all. With `by lean` each circuit is registered under a generated name `W_<i>` and one Lean claim per circuit goes into the one module; refused above 40 circuits, or above n = 8 for `forall cubes`. `count c in W: EXPR` prints how many satisfy EXPR. `plot hist FUNC W -> F.png` histograms FUNC(c).
- `margin["name"](c)` is the margin of a conjecture in `one-not/tools/search/conjectures.py`; below 0 means a counterexample.

## Finite claims (extension `asteroid/ext_finite.py`)

Meaning. These lines let any level state an exact claim about an integer sequence.
- `seq NAME = from PATH "KEY"` reads the one entry of a `fingerprints.json` whose name contains KEY. Without KEY, PATH is a `.json` list of integers. `seq NAME = [ ... ]` is a literal.
- `seq NAME = run "CMD" "KEY"` runs CMD from the repository root. It must exit 0. The sequence is then read from the `fingerprints.json` beside the script.
- CMD is always `python3 -I path.py [args]`, with the path inside the repository. It runs with a timeout of 900 s.
- `claim NAME = [ ... ]`: the first terms are exactly these.
- `claim NAME matches NAME2 FORM`: FORM applied to NAME equals NAME2 on their common prefix. The prefix must have at least 5 terms. FORM is `as-is` (the default), `diff` (first differences), `partial` (partial sums) or `plus1`. These are the centre's matcher forms.
- `claim formula NAME = "EXPR" from K`: term i of NAME equals EXPR at n = K + i - 1. K is 1 by default. Integers only. `//` must divide exactly, else the claim is FALSE. `0!! = (-1)!! = 1`. `C(a, b)` is 0 when b < 0 or b > a.
- `check "CMD"`: CMD must exit 0. One stdout line must be exactly `PASS`. No line may hold the word FAIL. It counts as a claim.
- `seq ... run` says whether CMD wrote `fingerprints.json`. If not, the output says the file is the committed copy. Then the run vouches for the script, not for the file.
- Empty data proves nothing. A formula claim on a sequence with no terms is FALSE. `claim NAME = []` is FALSE.
- Each item of a literal list must be a plain integer. `[1-2]` is an error, not a crash.
- Errors in a formula make the claim FALSE: `n!` for n < 0, `n!!` for n < -1, a negative top in `C(a, b)`, a negative exponent, an unknown name.
- Unary minus binds looser than `**`. So `-3**2` is -9.
- Size limits. n!, n!! and C(n, k) need n <= 10^6. One sum adds at most 10^6 terms. One claim takes at most 10^7 steps. Past a limit the claim is FALSE.
- Each claim prints TRUE or FALSE and counts in the summary. `by lean` is not available for them.
- Each passing `check` or `seq ... run` becomes the runner of the program's records. So `record ... checked-finite` carries a runner. The files read are cited as evidence.

## Frames (extension `asteroid/ext_frame.py`)

A frame ties an idea to the claim that formalizes it. The first string is the source: what was brought, and where it is written. The second is the reading.
- `-> LINE`: the claim or check on that earlier line of this file. It must have printed TRUE.
- `-> PATH`: another `.ath` file. It is run with `--no-lean`. It must exit 0.
- `-> none`: no claim yet.
- The frame is TRUE only if its claim passed in this run. Otherwise it is OPEN, and its label is forced to `open`.
- A Python claim supports at most `checked-finite`. A frame labelled `checked` or `checked-infinite` is downgraded to `checked-finite`, and the output says so.
- A frame is not a claim. It does not change the summary or the exit code.

Score: `score = reach * chance / cost`.
- reach: an integer >= 1, the fields or groups it helps. Default 1.
- cost: thousands of tokens. Default 80, the cost of one plain seat (`ath_prompts/measure/cost_per_result.md`).
- chance: 1.0 if the claim passed. Otherwise a prior by label: `open` 0.3.
- These weights are choices, not measurements. Change them in `ext_frame.py`.

Each frame is written to `frames.jsonl` at the repository root (or `$ASTEROID_FRAMES`). Fields: source, reading, claim, label, score, status, reach, cost. One line per (source, reading, claim). A rerun replaces that line, so there are no duplicates. `center.py` reads it as record kind `frame`. `python3 -I center.py queue` lists the open frames, highest score first. `frames.ath` at the root holds the backfilled frames.

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
bin/asteroid asteroid/examples/first.ath
bin/asteroid test            # every program under asteroid/examples
bin/asteroid test --no-lean  # Python and plots only (what GitHub Actions runs on every push)
```

## One name for each thing typed in the terminal (old -> kept)

The old spelling keeps working quietly; the kept one is what the docs use.

| old | kept |
|---|---|
| `bin/setup`, `bin\setup.cmd`, `bin\setup.ps1` | `bin/asteroid setup` (the `setup` scripts are what it runs) |
| `--doctor` | `doctor` |
| `--version`, `-V` | `version` |
| `--no-proof` | `--no-lean` |
| `run FILE.ath` | `FILE.ath` |
| `.ast` files | `.ath` |
| `python -m asteroid` | `bin/asteroid` (the launcher picks the right Python) |
| nothing typed | the interactive prompt (`bin/asteroid repl` is the same) |

Language verbs are not renamed. `claim EXPR by lean` and the extension verb `prove` stay as they are: they differ in what they send to Lean.
