# ask: a controlled-English query interface

```
python3 -I core/ontology/ask.py show open frames about time
python3 -I core/ontology/ask.py what connects beauvoir and time
python3 -I core/ontology/ask.py --model "what do we have that is open about time"
```

It answers from data. It does not infer. It is read-only: a plain query writes no file.

## Data it reads

| data | where | what it holds |
|---|---|---|
| board findings | every `findings.jsonl` (the current findings) | statement, recorded word, evidence, who, by |
| center nodes | `center/shards/*.jsonl` | cells, levels, fingerprints, and findings not on a board |
| results rows | `RESULTS.md` | the generated table of verified findings |
| frames | `frames.jsonl` | source, reading, label, TRUE or OPEN, score |
| in-between results | `core/ontology/*.py` | the docstring only. The file is parsed, never run |
| culture tags | `core/ontology/tags/tags_culture.json` | structure tags on works. Proposed, unreviewed |
| formal tags | `core/ontology/tags/tags_formal.json` | structure tags on formal results. Proposed, unreviewed |

Board findings are read live. Lines with the same id are merged, as `boards.py` does. Each finding is checked by the `boards.py` rule, recomputed with paths relative to the root. The tests check that the two agree on every finding in the repository. An evidence path that leaves the root counts as missing.

A center finding whose id is on a board is dropped. The board copy is the current one.

The tag files are built by `core/ontology/tags/build_tags.py` from two markdown tables an agent wrote. Nobody has reviewed them. The JSON says so in its `status` and `note` fields. Same input, same bytes. Three new tags the tables proposed (`diagonal`, `min-cut`, `seriality`) are listed apart as "proposed, not adopted".

## Grammar

Case does not matter. The words `the`, `a`, `an`, `please`, `kindly`, `me`, `us` are ignored. A final `?`, `!`, `.` or `,` is ignored.

```
status
how many results are verified
show open frames [about WORD]
show frames [about WORD]
show findings [about WORD]           board and center findings, verified or not
show verified findings [about WORD]
what is verified about WORD          verified findings and RESULTS.md rows
what is open about WORD              open frames, unverified findings, open cells and modules
what connects WORD and WORD          shared tags, shared findings, in-between results
which results use TAG                formal results, by tag
which works use TAG                  culture works, by tag
what links CORPUS and PILLAR         tags a culture corpus and a formal pillar share
list tags | list corpora | list pillars
what is TAG
explain WORD                         everything on record whose text mentions WORD
```

WORD, TAG, CORPUS and PILLAR are one token each. A token is letters, digits, `_`, `'` and `-`. Anything else is refused: shell characters, `/`, `.`, quotes, NUL, control characters. A query longer than 300 characters is refused.

WORD is matched as plain text (through `re.escape`) at the start of a word. So `time` finds `times`, and `ime` does not find `time`.

## What connects WORD and WORD

Three parts, each with its own labels.

1. Shared tags. The tag rows each word points at: its corpus or pillar, a tag of that name, or a row whose text mentions it. The tags both sets carry are listed. These lines are `[proposed]`.
2. Shared text. Findings, RESULTS.md rows, frames and center nodes whose text mentions both words. Each keeps its own label.
3. In-between results. Modules in `core/ontology` whose docstring mentions both words, such as the 2-chain claim in `asymmetry.py`. That claim is on no board and has no second seat, so it prints as `[open]`.

A shared tag or a shared word is not a link that was checked. It is a pointer.

## Labels

Every answer line starts with a label in brackets. Nothing is upgraded.

- A finding prints with its recorded word, and says if it is verified. Verified means an empty `why_not` list and a word RESULTS.md lists (`checked`, `checked-finite`, `checked-infinite`, `tested`, `refuted`). This is the rule of `boards.py` and `results.py`. A verified tested finding stays `[tested]`.
- A finding recorded as checked that is not verified prints as `[open]` and says why. Other unverified findings keep their word and say "not verified" and why.
- A finding line names its second seat, or says there is none. A Lean check needs none.
- A RESULTS.md row prints with its row label.
- A frame prints with its label if it is TRUE. An OPEN frame is `[open]`.
- A frame is a reading. It is capped at `[checked-finite]`, as `asteroid/SPEC.md` caps it. A frame recorded as `checked` or `checked-infinite` says it was capped.
- If a frame's claim is a `check "CMD"` line and a board finding has CMD as its runner, the frame takes no stronger label than that finding. If the finding is not verified, the frame prints as `[open]` and names it.
- A finding with no `why_not` field is not verified.
- A center cell is `[open]`. A DECIDED cell says it is a board decision, not a result. A fingerprint is `[open]`: it is data, not a claim.
- A module takes the label of its board finding if it has one. The finding whose runner is the module comes first. Else the module is `[open]`. A label its docstring states (`Claim (checked-finite, ...)`) is named in the note, with "not on the board, no second seat". It is never the bracket label.
- A row from a tag table prints as `[proposed]`. Its own label is shown as `row label: ...` and is never moved to the front.
- A count line, or a line that says nothing was found, is `[open]`.

## When it does not understand

It prints `did not understand`, the grammar and a closest-match suggestion (from `difflib`), and exits with code 2. It never guesses and answers a different question.

## --model: a model proposes, the parser decides

`--model "loose question"` asks a small local model (Qwen2.5-0.5B-Instruct, greedy, 40 new tokens, chat template, `HF_HUB_OFFLINE=1`) to write one query line. The prompt holds the grammar, ten worked examples and the names of the corpora, pillars and tags. Then:

1. The first line of the reply is checked by the same parser.
2. If it parses, the interface prints `[proposed] model proposed: QUERY` and then the answer from the data path. That answer is the same as the plain query's.
3. If it does not parse, the interface says so, shows the grammar and exits 2. It does not repair or guess.
4. If transformers or the model is missing, it prints a message and exits 3.

The model never writes answer text. A line it writes that looks like an answer (`[checked] 99 ...`) does not parse, so it is refused.

The model runs in a Python with transformers and torch. It looks in `ASK_QWEN_PYTHON`, then `ASTEROID_QWEN_PYTHON`, then `.venv`, then the current Python. Outputs are cached by prompt hash in `core/ontology/.ask_cache.json`. That file is in `.gitignore`; `ASK_CACHE` moves it. It is the only file the program writes, and only in `--model` mode. The generator can be replaced (`answer_model(..., generator=f)`); the tests use a mock.

### One real run (tested)

Ten loose questions, one run each, 2026-11-25, on a shared CPU. Label: tested (one small sample, not a measure of the model).

| loose question | model proposed | parsed |
|---|---|---|
| what do we have that is open about time | show open frames about time | yes |
| how many of our results are actually verified | show verified findings [about WORD] | no |
| anything connecting beauvoir and asymmetry? | what connects beauvoir and asymmetry | yes |
| give me the verified findings about routing | show verified findings about routing | yes |
| which formal results are tagged fixed-point | what tags a culture corpus and a formal pillar share | no |
| what does branching-tree mean | show branches [about WORD] | no |
| what links homestuck to math | what links homestuck and math | yes |
| tell me about the 2-chain | explain 2-chain | yes |
| what is still unproved about language | what is unproven about language | no |
| overall status of the repo please | status | yes |

6 of 10 parsed and were answered from data. The 4 that did not parse were refused with exit 2. None was guessed. About 14 s per question after the first (75 s with the model load).

## Exit codes

0 answered. 2 did not understand. 3 the model is missing.

## Honest limits

- The tags are proposed and unreviewed. A shared tag is a proposed link, not a check.
- Matching is plain text. `asymmetry` does not find `asymmetric`.
- The verified rule is recomputed from the files. It does not re-run any check.
- RESULTS.md is read as written. It can be older than the boards.
- Frames count as TRUE only as recorded in `frames.jsonl`. The interface does not re-run them.
- A module's stated label is the author's. It is reported, not adopted. The module is `[open]` unless a board finding names it.
- A 0.5B model often writes a line that does not parse. That counts as a failed proposal. It is not worked around.
- Tests: `python3 -I core/ontology/test_ask.py`.
