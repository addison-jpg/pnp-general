# ask: a question, not a claim

```
ask "show open frames about time"
```

`ask "QUESTION"` puts one question to the repository's recorded results and prints the answer. The question is one line of the controlled English in `core/ontology/ASK.md`. The answer comes from data: the current board findings (verified or not, with their second seat), center nodes, RESULTS.md rows, frames, the modules in `core/ontology`, and the proposed tag tables. Nothing is inferred.

```
ask "show verified findings about time"
ask "what is open about time"
ask "what connects beauvoir and time"
```

## What it is not

- It is not a claim. It does not appear in the `claims:` line and does not change the exit code.
- It writes no record, no frame and no file. It never writes `frames.jsonl`.
- It runs nothing from the question. A word with shell or path characters is refused, not run.

## How it prints

Each answer line starts with its label in brackets: `[checked]`, `[checked-finite]`, `[tested]`, `[refuted]`, `[analogy]`, `[open]`, `[proposed]`. An unverified finding prints as not verified. Nothing is upgraded. A frame is capped at `[checked-finite]`. A module off the board is `[open]`, whatever its docstring states. A row from a tag table is always `[proposed]`: the tags are an agent's proposal and have not been reviewed. The row's own label is shown as `row label`.

A question the grammar does not parse prints `did not understand`, the grammar and the closest match. The program goes on. This is on purpose: an ask line is a read, so a typo does not fail a run. Check the output.

## Notes

- A `#` starts a comment in asteroid, so it cuts a question short.
- The form must be `ask "..."` with double quotes. Anything else is an error.
- `ASK_ROOT` (an environment variable) points the data at another folder. Tests use it.
- The extension is `asteroid/ext_ask.py`. It loads `core/ontology/ask.py` by path and writes no bytecode.
- Test: `python3 -I asteroid/tests/test_ask.py`.
