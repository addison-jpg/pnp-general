# C3 trial: informal vs formal asks, same content

Model: Qwen/Qwen2.5-1.5B-Instruct, local, CPU, float32, chat template. 30 tasks (`tasks.json`, built by `make_tasks.py`),
two asks each. One greedy run plus three sampled runs (temperature 0.7, seeds fixed per batch), max_new_tokens 120.
Scoring is automatic and blind to register: `harness.py:score` sees only the output and the task's checker.
Numbers below are from `python3 analyze.py results.json` (copied in `analysis.txt`). Run time 2621 s.

## Result

| run | informal ok | formal ok | informal-only | formal-only | exact McNemar p |
|---|---|---|---|---|---|
| greedy | 19/30 | 23/30 | 3 | 7 | 0.3438 |
| sampled s0 | 17/30 | 25/30 | 2 | 10 | 0.0386 |
| sampled s1 | 17/30 | 22/30 | 4 | 9 | 0.2668 |
| sampled s2 | 16/30 | 23/30 | 0 | 7 | 0.0156 |

Pooled over the three sampled runs, per task: informal better on 4 tasks, formal better on 12, ties 14; exact sign test p = 0.0768.
Run-to-run spread: informal 16-17, formal 22-25.

Ask length: informal 13.2 tokens mean, formal 18.1. Output length (greedy): mean 65.7 vs 55.8 tokens, median 59.0 vs 22.5;
informal output shorter in 9 pairs, longer in 16. Many informal outputs hit the 120-token cap.

**Verdict on C3 (on this model and these tasks): contradicted.** The claim needs informal success at least equal to formal.
Formal was ahead in all four runs (by 4 to 8 tasks). The greedy run alone is not significant (p = 0.34); two of three sampled
runs are (p = 0.039, 0.016); the pooled sign test is p = 0.077. The "fewer corrections" half was not tested (single turn).

## What went wrong in informal asks (spot-checked outputs in results.json)

- ar04 "car goes 60 km/h 4 2 hrs": the model read "4 2 hrs" as 4 hours. The "4 = for" convention is part of the imitated register; it is a real ambiguity, not a scorer error.
- st04 "reverse 'world' 4 me": greedy reply was a refusal.
- st10 "swap the dots 4 dashes": read as Morse code.
- py03/py05: informal asks drew longer, chattier code that failed the asserts; formal asks drew a bare `def f`.
- st02: informal reply was "PnP-General" (wrong case).

## Per-task table

Columns: task | greedy informal ok | greedy formal ok | sampled informal (of 3) | sampled formal (of 3) | greedy out tokens informal | formal |

|task|gI|gF|sI|sF|lenI|lenF|
|---|---|---|---|---|---|---|
| ar01 | 1 | 1 | 2 | 3 | 64 | 76 |
| ar02 | 1 | 1 | 3 | 3 | 57 | 120 |
| ar03 | 0 | 0 | 0 | 1 | 54 | 120 |
| ar04 | 0 | 1 | 0 | 3 | 120 | 118 |
| ar05 | 0 | 1 | 1 | 0 | 120 | 120 |
| ar06 | 1 | 1 | 3 | 3 | 81 | 112 |
| ar07 | 0 | 1 | 1 | 1 | 120 | 120 |
| ar08 | 0 | 0 | 1 | 0 | 120 | 120 |
| ar09 | 0 | 0 | 0 | 0 | 120 | 120 |
| ar10 | 1 | 0 | 2 | 2 | 119 | 120 |
| ex01 | 1 | 1 | 3 | 3 | 32 | 21 |
| ex02 | 1 | 0 | 1 | 0 | 14 | 12 |
| ex03 | 0 | 1 | 1 | 3 | 54 | 14 |
| ex04 | 1 | 0 | 3 | 3 | 120 | 73 |
| ex05 | 1 | 1 | 3 | 2 | 52 | 21 |
| py01 | 1 | 1 | 3 | 3 | 15 | 15 |
| py02 | 1 | 1 | 2 | 3 | 61 | 14 |
| py03 | 1 | 1 | 0 | 3 | 120 | 13 |
| py04 | 1 | 1 | 2 | 3 | 120 | 18 |
| py05 | 1 | 1 | 0 | 3 | 120 | 13 |
| st01 | 1 | 1 | 3 | 3 | 13 | 2 |
| st02 | 0 | 1 | 1 | 2 | 3 | 91 |
| st03 | 1 | 1 | 3 | 3 | 2 | 39 |
| st04 | 0 | 1 | 0 | 3 | 13 | 12 |
| st05 | 1 | 1 | 3 | 3 | 4 | 3 |
| st06 | 1 | 1 | 3 | 3 | 2 | 24 |
| st07 | 0 | 0 | 0 | 2 | 21 | 16 |
| st08 | 1 | 1 | 3 | 3 | 49 | 15 |
| st09 | 1 | 1 | 3 | 3 | 95 | 11 |
| st10 | 0 | 1 | 0 | 3 | 85 | 102 |

## Limits

- One small model (1.5B). Frontier agents, which is what Addison actually prompts, may close the gap; untested here.
- Tasks and both registers written by the agent, not Addison. Register imitated from `../../research-seat.md` style only.
- n = 30 tasks, single-turn, no corrections, no context or board. 120-token cap truncates some arithmetic (ar09 failed both ways).
- Checkers are crude (last number; substring; exec + asserts). Spot checks found no scorer error in the cases listed above, but not every output was read.
- Three sampled runs are a variance estimate, not independent tasks; the paired tests treat tasks as units.

Files: `harness.py`, `tasks.json`, `make_tasks.py`, `results.json` (every output), `analyze.py`, `analysis.txt`.

# C4 proxy: rule-following by register (`c4_rules.py`, output `c4_analysis.txt`, `c4_results.json`)

Same model, greedy, max_new_tokens 80. Ten rules, each written informally and formally, put in the system prompt; four
user questions each; rule compliance checked automatically. Run time about 40 min (CPU shared with other processes).

Informal 27/40, formal 28/40; informal-only 4, formal-only 5; exact McNemar p = 1.0000. Per rule (informal, formal):
end with DONE 3,1; start "ok so" 3,4; no letter z 4,4; all lowercase 1,4; under 20 words 3,3; "4" for "for" 2,1;
no lists 2,3; ALL CAPS 4,3; include "banana" 1,1; rule 9 (forbidden apology word) 4,4.

Verdict on C4 proxy: toss-up. This tests whether a model follows a rule, not whether a person remembers or quotes it,
and not correction cost. C4 itself stays untested.

# Claims not testable here

- C5 (boards cut duplicates, conflicts, questions): needs matched runs with and without per-task boards, logging real merge conflicts. No such arm exists in the repo.
- C6 (messages per task fall after one-owner boards): needs a timestamped message log over a before and after switch; only 14 messages, one day.
- C7 (cost is reading): needs per-seat logs of files read and ask length (at least 20 seats), then the regression c = a + b|F| + d|l|. Never logged.
- C4 proper: matched playful vs formal human sessions, at least 10 pairs, blind coding of corrections.
