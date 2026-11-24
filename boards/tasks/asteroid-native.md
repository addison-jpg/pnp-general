# Task: asteroid-native

- **Serves:** the asteroid language.
- **Source:** owner, 2026-11-24: one pre-existing format; no Python at all; a clean open-source project with a website and a command line; "I dont want it to look ugly and vibecoded".
- **Statement:** asteroid with no Python: a command-line program written in Lean (one Lake executable) that reads an asteroid program, evaluates its claims, writes the proof module and has the proof checker decide it.
- **Done when:** `lake exe asteroid hello.ath` prints the same verdicts as the Python version on the core verbs, with no Python process involved.
- **Seats:** one Fable of main.

## Lines (TAKEN / DECIDED only)

- 22:56 Sonnet 2 TAKEN (finishing)
- 23:07 Sonnet 2: loader wired, Lean and Python agree on 23 claims in 3 programs, eval_sound proved for correct/hyps/forall cubes/comparisons of gates, base, orwitness, slack (NATIVE.md); open: witness/nots/anyslack terms and the negated checks.
