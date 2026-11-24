# trio: one small language, three engines

Owner, 2026-11-24: "building a very simple language is worth a try, if we properly incorporate lean for brute
force, python for speed/background, and matplotlib as an available tool... take what they've built and
integrate it into a novel, relatively simple, framework."

| Engine | Does | Built on |
|---|---|---|
| Python | evaluates every claim at once, searches, runs background jobs | `one-not/tools/search` (core, conjectures, hunt, continuous) |
| Lean | decides: a `by lean` claim becomes a theorem proved by `decide +kernel` | `one-not/lean/PEqualNP/W951/SearchCheck.lean` |
| matplotlib | pictures | `trio/out/*.png` |

Nothing is synced by hand: a script names a circuit once, and trio sends the same object to all three.

```
let c = load one-not/data/witnesses/nonlocal/general_count_below_base_min.json
show c
claim correct(c) by lean
claim witness(c) < base(c) by lean
claim margin["C4 count (flip classes)"](c) >= 0
plot phi c -> trio/out/c.png
hunt "C4 count (flip classes)" 20 4 1 &
record one-not/data/witnesses/nonlocal C4 checked "The circuit is correct and has fewer witness gates than base."
```

```bash
python3 -I trio/trio.py trio/examples/many_not.trio
```

Verbs: `let … = load`, `show`, `claim … [by lean]`, `plot phi … -> FILE`, `hunt "…" SECONDS MAXNOT [SEED] [&]`,
`record DIR ITEM WORD "…"`. Functions in a claim: `correct gates nots base witness orwitness slack anyslack
margin["conjecture name"]`. A `record` writes a finding into the board tree (`boards.py`) and is skipped if any
claim is false or, for the word `checked`, if Lean did not build.

First run (`examples/many_not.trio`): 8 claims true in Python; 5 decided by the Lean kernel in 11 s (axiom:
`propext`); one plot; one background hunt; one finding.

## What is not there yet (be honest about it)

- Lean decides only `correct(c)` and `witness(c) OP number-or-base(c)`. Every other function is Python only;
  trio says so on the line instead of pretending.
- The Lean statements are about `SearchCheck`'s own bit-parallel evaluator. The theorem tying it to the
  project's `Circuit.eval` is not proved.
- Python evaluates first and a false claim never reaches Lean, so Lean has not yet been seen to REJECT a
  claim that Python accepted.
- One kind of object (a circuit from a JSON file) and one plot. No variables over cubes, no quantifiers.

Next, in order: `slack` and the mixed slack as Lean definitions (so the remaining `sorry` can be stated in a
script); `claim … for all cubes`; circuits built in the script; the bridge theorem.
