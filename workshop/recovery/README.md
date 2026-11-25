# Recovery under repeated harm: a toy model

This is a model. It describes no person and no group, and it makes no claim that any kind of psychosis, illness or harm is a method of adjustment. It is a small formal picture of one idea: a state can be pushed down by repeated harm and pulled back up by support, and the way back up depends on the structure of the moves, not on the will of the one moving.

## What is modeled

- Three states: 0 stable, 1 strained, 2 harmed.
- Moves go both ways between neighbours. Harm and strain push a state down. Support and repair pull it up.
- Nothing else is modeled: no causes, no diagnoses, no treatment, no prediction for anyone.

## What is checked (asteroid, `model.ath`)

| claim | meaning | status |
|---|---|---|
| `<>p` is exactly {1} | only the strained state can step to a stable state | checked-finite, 3 true, 0 false |
| `<>r` is exactly {1} | only the strained state can step to a harmed state | checked-finite |
| `<>q` is exactly {0,2} | the stable and harmed states can step to a strained state | checked-finite |

These are facts about this toy graph. They do not say what happens to any real person or community.

## What is not claimed

- That harm produces recovery, or that psychosis is a way of adapting. The model has no such move.
- That a model of this kind predicts anyone's life. It does not.
- Any link to the real struggles of people with mental illness, beyond the general idea that support and harm move a state in both directions. That link is an analogy and is labelled as one.

## Open

- A version with more states and real time steps would need data and a second seat to check it.
- Whether the analogy to collective trauma holds is open, and nothing here settles it.
