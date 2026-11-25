# Qual-quant, generalized: which frames close?

Addison's qual-quant method: bring an idea (qualitative), find the smallest exact check (quantitative), and label the result no higher than the check. This file measures how that has gone across every frame. Code: `core/ontology/qualquant.py` (standard library, exact fractions). Frame: last frame of `frames_sync.ath`.

Words: fact, checked-finite, checked-infinite, tested, join, analogy (reading), open.

## Types (one line each)

- **structure**: the reading names a finite mathematical object or relation that a program can enumerate.
- **effect**: the reading claims a measured effect of an intervention; it needs runs, data or a model.
- **contested**: the reading is a question of interpretation (meaning, history of ideas, metaphysics) that no finite check decides.

## Rules (applied by code, in order)

1. Hand overrides, each with a reason in the code: Stirner (contested: needs sources read); the Car Seat lineage, the .ath/~ATH mirror and the Homestuck meteor (structure: each is a finite object whose check is simply not written yet).
2. effect if the reading has "succeed", "fewer corrections" or "cut duplicates".
3. contested if the claim is `none` and the reading has "contested", "song means", "which measure", "fixed idea" or "reading".
4. structure otherwise.

Closed means status TRUE in `frames.jsonl`. The qual-quant frame does not count itself.

## Result (checked-finite on the current frames.jsonl, 2026-11-25)

| type | closed | total | rate |
|---|---|---|---|
| structure | 45 | 49 | 45/49 |
| effect | 0 | 1 | 0 |
| contested | 0 | 5 | 0 |

Open structure: 4 frames (see the script output; the list moves as frames are added). Open effect: prompting claims C3 to C6. Open contested: time as socially constructed, Stirner's fixed ideas, the measure problem (merged), "High to Death" and "Kid War".

## The rule, as a measured claim

On this repo, a frame closes when its reading is cut down to a finite structure; frames left as interpretation or as effects do not close. Numbers: 45 of 49 against 0 of 6.

Limits, said plainly:
- n = 55 at this run. Small. The numbers move as frames are added; rerun `python3 -I core/ontology/qualquant.py`. This describes this repo, not a law.
- Partly by construction. Most checked frames were rewritten as "Kripke fact only" or "Boolean fact only" so that a check fits; a passing check is part of why rule 4 calls them structure. The rate measures how often a reading could be cut to a structure, not whether the reading is true.
- A closed frame closes its structure, never its reading. The reading stays analogy.
- Effect frames need the model or new runs; none were run here.
