# Cost per checked result (S5, Sonnet, 2026-11-25)

Session data, not a controlled experiment. Tokens and seconds are the tool reports main supplied (27 seats). There are no timestamps per seat, so "over time" uses the order main listed them in, which I take to be roughly chronological. That is an assumption. Repo size is proxied by commit count and by tracked `.lean` lines. No Qwen here; that line stays OPEN.

## Per seat kind

"Results" counts what the report says (A9, A12 = 2 lemmas; Q2 = 3; Fable unify = 5 files; BeauvoirQG = 19 theorems); every other checked seat counts as 1, which is my assumption.

| Kind | Seats | Checked results | Tokens | Tokens / seat | Tokens / checked result | Seconds / result |
|---|---|---|---|---|---|---|
| Sonnet, all 18 checked seats | 18 | 22 | 1,967,486 | 109,305 (median 92,050) | 89,431 | 240 |
| Sonnet, plain one-lemma lines (excl. C3, C4, C5, Q2, Q4) | 13 | 15 | 1,165,505 | 89,654 | 77,700 | 104 |
| Sonnet, heavier lines (C3, C4, C5, Q2, Q4) | 5 | 7 | 801,981 | 160,396 | 114,569 | 663 |
| Opus (A4, B5, A7, A10, B6, B9) | 6 | 0 fully checked (A4, B5 had lemmas, count not given) | 1,010,094 | 168,349 | undefined (no checked result at the headline) | 768-1677 per seat |
| Fable (unify, BeauvoirQG) | 2 | 24 | 354,028 | 177,014 | 14,751 (but a result here is a theorem in a big file) | 56 |
| Fable robustness | 1 | 0 checked (tested) | 173,252 | 173,252 | n/a | 1730 |

Key ratios:
- Plain Sonnet one-lemma seat: about 78k tokens per checked lemma. Opus attack seat: about 168k tokens per seat and none of the six closed a checked result at the headline. Per seat the Opus is only about 1.9x as costly in tokens, but about 10x in time (median Opus about 1000 s against about 100 s).
- Fable looks cheapest per result (15k) only because it counts theorems inside a file; per seat it is the same 175k as the others. Do not read that as efficiency.
- The cost of a Sonnet seat is a floor of about 77-100k tokens (the fixed read of rules and files, consistent with the data note in `ath_prompt_method.md`). Tokens per seat barely differ between a 32 s seat (C1, 76,792) and a 156 s one (B8, 86,424).

## Does it trend with repo size?

Repo growth over the measured window (`git log` on `boards/tree.json`, 54 commits touching it):

| Point | Commit count | Checked findings (tree root) | `.lean` lines tracked |
|---|---|---|---|
| first tree.json commit, 11-24 19:37 | 556 | 11 | 543,893 |
| 11-24 21:31 | 599 | 30 | 547,918 |
| 11-25 00:19 | 703 | 43 | 551,776 |
| 11-25 02:05 | 849 | 68 | 556,956 |
| now | 868 | 70 | n/a |

Commits +56% and checked findings x6.4 across about 6.5 hours. Lean lines only +2.4%, because about 544k of them are a vendored baseline (my guess; I did not check what), so lines are a poor size proxy and I use commit count.

Sonnet tokens per checked result against seat order (6 seats each):

| Block | Seats | Tokens / seat | Tokens / result |
|---|---|---|---|
| first six (A6..B8) | 6 | 90,686 | 68,014 |
| middle six (A16..C5) | 6 | 125,384 | 125,384 |
| last six (Q2..P4) | 6 | 111,845 | 83,884 |

Linear fit over all 18 in order: slope +1,523 tokens per seat, r = 0.22. That is weak and not distinguishable from noise at n = 18. The bump in the middle is the heavier jobs (C3 172,838 and C4 163,243 tokens, 1634 s and 606 s; Q4 at 198,002 is in the last block), not a growth with the repo. The last block of plain lemmas (Q3, P2, P3, P4: 78k-91k) is as cheap as the first (84k-100k), even though about 300 commits later.

## Honest reading

- M1/T1 (flat in R) is not refuted: plain narrow seats cost the same ~80-100k tokens at commit ~600 and at commit ~850. It is not confirmed either: 18 seats, one fixed boilerplate floor, and job size varies far more than repo size does.
- What the data does show is that cost per seat tracks the job (one lemma ~90k; a multi-lemma or weak-form line 130-200k), not the clock.
- T2 (roaming agents grow with R) is untested: the only roaming-style data are the early Opus/Fable seats, and they are a different, bigger job, not the same lemma at two repo sizes. The controlled test described in `ath_prompt_method.md` (same goal, two repo sizes) is still needed.
- Confounds: the order of seats is assumed; seat difficulty is not controlled; "checked" for C1 is a wrapper and C4 a weak form; token counts include the fixed read; the tree counts all seats, not only these 27, so tokens over the whole tree-checked delta cannot be computed (the listed seats are not all the seats).

Script: ad hoc, `git show <commit>:boards/tree.json` for `counts.checked` at each commit touching it, and `git grep -c '' <commit> -- '*.lean'`; numbers above reproduce from the seat list in the task line.
