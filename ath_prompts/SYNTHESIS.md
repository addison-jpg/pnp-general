# Qual-quant synthesis

Each claim got a measurable statement and a verdict from data in the repo. A second seat then checked each verdict. Sources are listed under each row. Scripts are in /tmp/claude-0/-home-user/c7c2895f-eb04-517d-b538-6d0d59d567a9/scratchpad/qq/.

| ID | Qualitative | Quantitative | Verdict | Numbers (source) | Checker agreed |
|---|---|---|---|---|---|
| C1 | Informal asks are shorter than formal ones. | Informal has fewer tokens in more than half of matched pairs and in the pooled sum. | supported (weak, typed prompts only) | 7 of 10 pairs shorter. Pooled 236 vs 267 tokens. Prefs block goes the other way, 226 vs 204. With prefs, 462 vs 471. Without pair 05:12, 172 vs 188. (ath_prompts/measure/results.md; c1.py) | yes |
| C2 | Informal asks carry more information per token. | Informal bits/char beat formal in at least 9 of 10 pairs at every model size, Wilcoxon p<0.05. | supported (numeric part only) | Informal higher: 0.5B 10/10 p=0.0020; 1.5B 10/10 p=0.0020; 3B 9/10 p=0.0039; 7B-q4 10/10 p=0.0020. Bits/char 2.11/1.46, 1.99/1.42, 2.11/1.44, 2.11/1.59. 6.01 vs 4.64 nats/token at 0.5B. (ath_prompts/measure/heavy/results.md, heavy/data/*.json, measure/results.md; c2_bpc.py) | yes |
| C3 | Informal asks are better instructions. | Same task: informal has equal or higher success and at least 1 fewer correction per task. | untested | No success or correction data. results.md line 100: "Token count and loss are not task success". | yes |
| C4 | Playful register makes corrections cheap and rules memorable. | Informal rules are quoted verbatim more often; corrections come in fewer turns. | untested | No formal-register session exists. One side only. | yes |
| C5 | Small informal asks scale only inside a strict frame. | Boards cut duplicates, merge conflicts and questions per checked finding. | untested | 48 files in boards/tasks. 82 merge commits. 490 commits before boards/tasks. Keyword hits: 3 "conflict", 8 "duplicate". These are not measured conflicts. (ath_prompt_method.md line 121; c5.py) | yes |
| C6 | One-owner boards mean few messages. | Messages per completed task fall after one-owner boards. | untested | Only 14 messages (6 + 8), all dated 2026-11-23. No before period. (one-not/tools/stat_search/INBOX.json, one-not/tools/l951_charging/INBOX.json) | yes |
| C7 | Cost is reading, not the ask. | In c = a + b\|F\| + d\|l\|, \|F\| explains most variance; narrow seats cost about 77-100k tokens. | untested (regression); seat cost range holds | 89,654 tokens per seat mean, 13 seats. Per seat range 76,792 to 99,716. 77,700 is per checked lemma, not per seat. Files read and ask length were never logged. (ath_prompts/measure/cost_per_result.md; ath_prompt_method.md lines 185-202) | yes |
| C8 | Board seats are flat in repo size. | Slope of tokens per checked result vs commit count is not different from 0, and cost stays under a bound. | toss-up (close to untested) | Slope +1,523 tokens per seat, r = 0.22, n = 18. Blocks 68,014 / 125,384 / 83,884. Plain lemmas 84-100k early, 78-91k late. Fit is on seat order, not commit count. No seat data past commit 868. (ath_prompts/measure/cost_per_result.md; c8.py) | yes |

The checker agreed on all eight. Two notes from the checker were applied as weaker wording. C1: most of the gap comes from one pair (05:12), so the verdict is marked weak. C8: commit count was never the regressor, so toss-up is marked close to untested. The checker counted 1012 commits, not 1011. A new commit landed between runs. No verdict changes.

## What melding qual and quant means here

Each qualitative claim was rewritten as a statement a count or a test could settle. Then the repo data gave it a verdict.

Claims about the text itself converted cleanly. C1 (length) and C2 (surprisal) are properties of a prompt. A tokenizer and a model can score them. Both got numbers.

Claims about outcomes resisted. C3 to C6 talk about success, memory, scaling and messages. These need a comparison the repo never ran: a formal arm, a no-board arm, or a before period. The data has one side only. So they stay untested.

Claims about cost sat in the middle. C7 and C8 have token totals per seat. But the causes (files read, repo size) were never logged. The totals fit the claims. They cannot test them.

C2 also shows the limit of conversion. The numeric part holds. "More surprising" is not "more useful". The useful part folds into C3, which is untested.

## Next measurements

Ranked by value.

1. Randomized informal vs formal trial on the 10 prompt pairs (C3). Twenty or more runs per pair, fresh context, blind scoring of success and corrections. This tests the core claim, and it also settles the useful part of C2.
2. Per-seat log of tokens, files read and ask length, 20 or more seats (C7). Cheap to add. Then fit the regression.
3. Fixed one-lemma Sonnet task at commits 556, 700, 868 and 1011, at least 5 seats each (C8). Regress on commit count.
4. A timestamped inter-seat message log with task ids, kept from now on (C6). Note: a before period no longer exists, so only a new switch could be compared.
5. Matched runs with and without per-task boards, logging real merge conflicts, duplicate tasks and questions per checked finding (C5).
6. Matched playful vs formal sessions, at least 10 pairs, with blind coding of corrections (C4).
7. More C1 pairs from more speakers, formal rewrites by people blind to the hypothesis, and a second tokenizer.
