# Task: asteroid-native

- **Serves:** the asteroid language.
- **Source:** owner, 2026-11-24: one pre-existing format; no Python at all; a clean open-source project with a website and a command line; "I dont want it to look ugly and vibecoded".
- **Statement:** asteroid with no Python: a command-line program written in Lean (one Lake executable) that reads an asteroid program, evaluates its claims, writes the proof module and has the proof checker decide it.
- **Done when:** `lake exe asteroid hello.ath` prints the same verdicts as the Python version on the core verbs, with no Python process involved.
- **Seats:** one Fable of main.

## Lines (TAKEN / DECIDED only)

- 22:56 Sonnet 2 TAKEN (finishing)
- 23:07 Sonnet 2: loader wired, Lean and Python agree on 23 claims in 3 programs, eval_sound proved for correct/hyps/forall cubes/comparisons of gates, base, orwitness, slack (NATIVE.md); open: witness/nots/anyslack terms and the negated checks.
- 23:57 main's Opus TAKEN: Lean-native asteroid on Windows / Git Bash
- 23:57 main's Sonnet (tests) [BUG] asteroid/asteroid.py:39 does os.chdir(ROOT), so a relative `load` in a program run from another folder is not found. Repro: in a temp dir with only_here.bench, `<repo>/bin/asteroid relative.ath --no-lean` (line `let hello = load only_here.bench`) gives `FileNotFoundError: [Errno 2] No such file or directory: 'only_here.bench'` (ext_bench.py:180); hello.bench "works" only because the repo has its own copy. Should resolve against the program's folder.
- 23:57 main's Sonnet (tests) [BUG] a path with a space in `load` is not parsed: `let hello = load /tmp/asteroid e2e x/hello_crlf.bench` gives `noplot_crlf.ath:4: cannot parse: let hello = load /tmp/asteroid e2e x/hello_crlf.bench` (Git Bash on Windows: C:/Users/Some Name/...). Needs quoting or rest-of-line paths.
- 23:57 main's Sonnet (tests) [BUG-minor] `bin/asteroid --doctor` prints the usage text and exits 2 (flag not there yet); test_e2e.py treats that as SKIP. Run the test: `python3 asteroid/tests/test_e2e.py`.
