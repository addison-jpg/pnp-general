# C3 on a Claude-class model (Haiku), 2026-11-25. Label: tested.

Same 30 task pairs as the Qwen trial, plus 12 harder pairs written for this run (h01 to h12, answers computed by code). Each ask went to one fresh Haiku agent, once, with the same neutral wrapper on both registers ("Answer in the response field. Do not use any tools."). 84 asks, all returned. Data: `claude_haiku_rows.json`. Scorer: `score_claude.py` (run `python3 -I workshop/ath_prompts/measure/trial/score_claude.py`).

## Result

| set | scorer | informal | formal | informal only | formal only | exact sign test |
|---|---|---|---|---|---|---|
| all 42 | strict | 36 | 40 | 1 | 5 | p = 0.219 |
| all 42 | lenient | 41 | 42 | 0 | 1 | p = 1.0 |
| original 30 | strict | 25 | 29 | 0 | 4 | p = 0.125 |
| harder 12 | strict | 11 | 11 | 1 | 1 | p = 1.0 |

Verdict for C3 on this model: **toss-up, no register effect found.** The strict scorer (last number in the reply) tilts toward formal, but most of that is the scorer: replies like "7. ... 23 / 3 = 7 remainder 2" are correct and end in a different number. The lenient scorer (the answer appears among the numbers) leaves one difference, ar04.

## What the misses were

- **ar04 (informal):** "car goes 60 km/h 4 2 hrs" was read as 4.2 hours, 252 km. This is a real register effect, and the pair is already flagged as differing in content (the informal text has a typo that changes the meaning).
- **st07, both registers:** the task key says 3 but "mississippi" has two p's. Both registers answered 2. The key is wrong in `tasks.json` (and so in the Qwen trial); `score_claude.py` uses 2.
- **ar05, ar08, ar10, ex03, h02, h08:** correct answers that the last-number rule scored as wrong.

## Limits

- Ceiling: 41 to 42 of 42 pass under the lenient scorer, so the tasks cannot separate the registers on this model. A harder set where the model fails some pairs is needed.
- One model (Haiku), one run per ask, n = 42. The informal register is imitated, not Addison's own prompts.
- The wrapper text is the same on both sides, but it is not in the Qwen trial.
- Cost: 84 agents used about 5.5M tokens (about 65k each, mostly fixed agent overhead), so a larger run should call the model directly, not through agents.
