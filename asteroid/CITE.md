# cite: a claim lives as long as its citation does

    cite KEY [KEY ...]                     (an asteroid line, below the claim it supports)
    ... cite:KEY ...                       (a token, in Markdown and Lean)

Every new claim in this repository says where it comes from. A citation is **ALIVE** if it resolves now and
**DEAD** otherwise. There is no third state, and nothing passes by default.

## KEY

| KEY | alive when |
|---|---|
| `lit:"TEXT"` | a table row of `LITERATURE.md` contains TEXT (case-insensitive) |
| `doi:X`, `arxiv:X` | X appears in `LITERATURE.md`: an outside source enters the literature index first |
| `lean:NAME` | a Lean declaration has full name NAME, or is the only one whose full name ends in `.NAME`. An `axiom` is refused: it is a premise, not a source |
| `file:PATH` | a file of the repository (inside the root after symlinks, not under `.git`) |
| `commit:HASH` | a commit, 7 to 40 hex digits, reachable from HEAD |
| `ath:PATH` | an asteroid program in which every claim line is itself cited and alive (checked recursively) |
| `original` | the statement is new here. An explicit choice: it is never filled in for you |

## What must be cited (the gate)

`tools/cite/gate.py` forces citations on lines ADDED by a commit. Old lines are not forced; `--all` audits them.

| File | A claim is | It needs |
|---|---|---|
| `.ath` | a line starting `claim`, `claim!`, `check`, `prove`, `record` | a `cite` line below it, before the next claim line |
| `.md` | a line with `[PROVED]` `[TESTED ...]` `[DATA]` `[DEAD]` `[LEAN]` `[REFUTED]` `[CHECKED]` | a `cite:KEY` token on the same line (definition: cite:file:tools/cite/gate.py) |
| `.lean` | a `theorem` or `lemma` | a `cite:KEY` token on its line, in the 8 lines above it, or in the first 40 lines of the file (one header cite covers the file) |

Every `cite` line and `cite:KEY` token on an added line must be alive. `LITERATURE.md` and `NAMES.md` are not gated.

## In a run (`asteroid/ext_cite.py`)

Each KEY is resolved when its line is read. ALIVE prints and changes nothing. DEAD counts as a FALSE claim: the
run exits 1, no `record` is written, and `commit` is skipped. So deleting a cited theorem, file or literature row
kills every claim that cites it, at the next run.

## Where it is enforced

1. `git config core.hooksPath .githooks` (once per clone): the pre-commit hook runs `gate.py --staged`.
2. `.github/workflows/cite.yml`: every push to main and every pull request runs `gate.py --range`.
3. Blocking on the server needs one setting: GitHub, Settings, Branches, a rule on `main` with the status
   check `cite` required. Without it the workflow only marks the push red.

## Limits (hard: past one the citation is DEAD or the gate FAILS)

| Limit | Value |
|---|---|
| bytes of `LITERATURE.md` read | 2 000 000 |
| Lean files indexed | 20 000, at most 2 000 000 bytes each |
| `ath:` nesting, programs visited | 3 deep, 64 programs (asteroid's child-run limits) |
| resolutions per run | 4096 |
| seconds per git call | 60 |
| added lines, changed files per gate run | 200 000, 4000 |

Each resolution is one lookup in an index built once per run, so a gate run is linear in the size of the diff
plus the size of the indexes. These numbers are choices, not measurements; change them in `tools/cite/cite.py`
and `tools/cite/gate.py`, and here.

## What a citation does not say

An alive citation says the source EXISTS and is the one named. It does not say the source proves the claim.
That is the job of the claim's own word (checked, tested, paper, ...).
