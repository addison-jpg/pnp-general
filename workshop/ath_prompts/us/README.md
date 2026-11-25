# us

Addison asked the love model to look at us: Addison and the agents.
This is a reading (analogy). It models recorded behaviour, cost and results only. Nothing here is about anyone's feelings or inner life.
Run `python3 -I workshop/ath_prompts/us/us.py` (well under a second), or `bin/asteroid --no-lean love.ath`.

## Small: the answer

- The recorded assignment ("smallest agent that can do the job") is **stable**: no blocking pair.
- But the test has no power yet. Every ask was recorded on one seat size only, so no ask can rank two seats.
- The Beauvoir condition holds at 6 of 7 asks. It **fails** at "one paper attempt": runs A7 and A10 (Opus) ended in an obstacle,
  and the recorded files hold no follow-up line for them. Those are the two dead ends.

## Middle: the model

Asks are Addison's jobs. Seats are agent sizes: haiku, sonnet, opus. It is the capacity model of `culture/love`, with incomplete lists.

Data, and nothing else:
- the seat table in `ath_prompt_method.md` (Sonnet: A6, A8, A9, A11, A12, B8; Opus: A4, B5, A7, A10). The one Fable row is not a
  haiku, sonnet or opus seat, so it is left out;
- the C3 Haiku run, `workshop/ath_prompts/measure/trial/CLAUDE_HAIKU.md`: 84 asks, about 65k tokens each, result tested,
  and a written follow-up ("A harder set where the model fails some pairs is needed").

Preferences, derived:
- An ask finds a seat acceptable only if the data records that seat on that ask. It ranks acceptable seats by the best recorded
  result (checked > checked lemmas > tested > obstacle), then by lower mean recorded tokens.
- A seat ranks asks the same way: the ones it closed first, then lower recorded tokens.
- Capacity of a seat: the number of asks it was recorded on (haiku 1, sonnet 4, opus 2).
- A pair blocks when each would take the other. The comparison is `wants` from `culture/love/check.py`, imported.

| ask | seat | runs | result |
|---|---|---|---|
| one Lean lemma | sonnet | A6, A8 | checked |
| two Lean lemmas | sonnet | A9, A12 | checked |
| one Lean conditional | sonnet | A11 | checked |
| one Lean reduction | sonnet | B8 | checked |
| open attack | opus | A4, B5 | checked lemmas (with an obstacle or a reduction) |
| one paper attempt | opus | A7, A10 | obstacle |
| register trial (84 asks) | haiku | C3 | tested |

Power check (not data): if a haiku seat had recorded one checked Lean lemma at 60k tokens, the code finds the blocking pair
(one Lean lemma, haiku). So the check can fail. On the recorded data it does not, because the data never puts one ask on two sizes.

## Big: the Beauvoir condition

The frame: one world per ask, one per recorded run, and one "record" world (a finding, or a written follow-up line).
An ask reaches its runs. A run reaches "record" if its result is a finding (checked, checked lemmas, tested) or the files record a follow-up line.
[]<>T at an ask says: every run the ask reaches can itself go on. It is evaluated with the successor function of
`core/ontology/beauvoir.py`, imported; that file's own exhaustive check ([]<>T is successor-seriality, frames on 1..3 worlds) must pass first.

Result on the recorded data: true at 6 asks, false at "one paper attempt". Dead ends: A7, A10.
The board method says obstacles are posted as new lines. Whether such lines exist for A7 and A10 on the boards was not looked up:
only the seat tables and the C3 run were used. If they exist, adding them makes the condition true everywhere.

## Reading (analogy)

This is a reading, not a fact.
Stable here means: on what was recorded, no ask and seat would both rather have been paired with each other.
It does not show the size rule is right. To test it, the same ask must be recorded on two sizes (for example one Lean lemma on Haiku and on Sonnet).
The Beauvoir reading: whatever an ask reaches should be able to go on. An obstacle with a follow-up line goes on; one without is a dead end.
Kindness conjecture K (`ath_prompt_method.md`) stays a conjecture. Nothing here measures tone.

## Open

- The same ask on two seat sizes, so the stability check has power.
- Follow-up lines for A7 and A10, from the boards.
- The Fable seats, as a fourth size, if wanted.
