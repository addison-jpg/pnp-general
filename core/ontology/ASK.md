# ask: a controlled-English query interface

```
python3 -I core/ontology/ask.py show open frames about time
python3 -I core/ontology/ask.py --model "what do we have that is open about time"
```

It answers from data. It does not infer. It is read-only: a plain query writes no file.

## Data it reads

| data | where | what it holds |
|---|---|---|
| findings | `center/shards/*.jsonl` (kind `finding`) | text, recorded word, `why_not` |
| frames | `frames.jsonl` | source, reading, label, TRUE or OPEN, score |
| culture tags | `core/ontology/tags/tags_culture.json` | structure tags on works. Proposed, unreviewed |
| formal tags | `core/ontology/tags/tags_formal.json` | structure tags on formal results. Proposed, unreviewed |

The tag files are built by `core/ontology/tags/build_tags.py` from two markdown tables an agent wrote. Same input, same bytes. Three new tags the tables proposed (`diagonal`, `min-cut`, `seriality`) are listed apart as "proposed, not adopted".

## Grammar

Case does not matter. The words `the`, `a`, `an`, `please`, `kindly`, `me`, `us` are ignored. A final `?`, `!`, `.` or `,` is ignored.

```
status
how many results are verified
show open frames [about WORD]
show frames [about WORD]
which results use TAG          formal results, by tag
which works use TAG            culture works, by tag
what links CORPUS and PILLAR   tags a culture corpus and a formal pillar share
list tags | list corpora | list pillars
what is TAG
explain WORD                   findings and frames whose text mentions WORD
```

WORD, TAG, CORPUS and PILLAR are one token each, made of letters, digits, `_`, `'` and `-`. Anything else (shell characters, `/`, `.`, quotes, spaces inside the token) is refused. A query longer than 300 characters is refused.

## Examples

```
status
how many results are verified
show frames about bridges
which results use exhaustive-check
what links beauvoir and physics
what is fixed-point
explain asymmetry
```

## Labels

Every answer line starts with a label in brackets.

- A finding prints with its recorded word. It is "verified" only if the word is `checked`, `checked-finite` or `checked-infinite` and it has no `why_not`. A finding recorded as checked that has a `why_not` prints as `[open]` and says why.
- A frame prints with its label. An OPEN frame is `[open]`.
- A row from a tag table prints as `[proposed]`. Its own label is shown as `row label: ...` and is never moved to the front.
- A line that says nothing was found is `[open]`.

## When it does not understand

It prints `did not understand`, the grammar and a closest-match suggestion (from `difflib`), and exits with code 2. It never guesses and answers a different question.

## --model: a model proposes, the parser decides

`--model "loose question"` asks a small local model (Qwen2.5-0.5B-Instruct, greedy, 40 new tokens, chat template) to write exactly one query line. The prompt holds the grammar, six worked examples and the names of the corpora, pillars and tags. Then:

1. The first line of the reply is checked by the same parser.
2. If it parses, the interface prints `[proposed] model proposed: QUERY` and then the exact answer from the data path.
3. If it does not parse, the interface says so, shows the grammar and exits 2. It does not repair or guess.
4. If transformers or the model is missing, it prints a message and exits 3.

The model never writes answer text. Its output is "proposed" until the parser accepts it, and even then the line is only a query.

The model runs in a Python with transformers and torch (`ASK_QWEN_PYTHON`, else `ASTEROID_QWEN_PYTHON`, else `.venv`, else the current Python), with `HF_HUB_OFFLINE=1`. Outputs are cached by prompt hash in `core/ontology/.ask_cache.json` (in `.gitignore`; `ASK_CACHE` moves it). This cache is the only file the program ever writes, and only in `--model` mode.

## Exit codes

0 answered. 2 did not understand. 3 the model is missing.

## Honest limits

- The tags are proposed and unreviewed. A shared tag between a corpus and a pillar is a proposed link, not a check, and not a join.
- It answers from data. `explain WORD` is a plain substring match, so `asymmetry` does not find `asymmetric`.
- The verified count follows the repo's rule (a checked word and no `why_not`). It does not re-run any check.
- Frames count as TRUE only as recorded in `frames.jsonl`. The interface does not re-run them.
- A 0.5B model often writes a line that does not parse. That is counted as a failure of the proposal, not worked around.
- Tests: `python3 -I core/ontology/test_ask.py`.
