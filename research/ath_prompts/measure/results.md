# ath-prompt-quant: first measurement, informal (Addison verbatim) vs formal rewrite

Model: Qwen2.5-0.5B-Instruct, local, CPU, offline. Used only for token counts and teacher-forced per-token log-probabilities; nothing was generated. Plain loss of the text alone: no chat template, no BOS (Qwen adds none), so the first token is unscored and loss is the mean over tokens 2..n (n-1 tokens). Tokens and chars are of the whole text. Script: `research/ath_prompts/measure/measure.py`.

| id | inf tok | frm tok | inf chars | frm chars | inf total loss | frm total loss | inf mean loss | frm mean loss |
|---|---|---|---|---|---|---|---|---|
| 05:12 | 64 | 79 | 303 | 386 | 369.0 | 318.6 | 5.86 | 4.08 |
| 05:40 | 15 | 16 | 62 | 63 | 139.1 | 141.2 | 9.94 | 9.42 |
| 05:45 | 8 | 16 | 32 | 62 | 49.7 | 72.9 | 7.10 | 4.86 |
| 06:19 | 5 | 5 | 18 | 21 | 31.0 | 32.1 | 7.76 | 8.02 |
| 06:32 | 16 | 21 | 74 | 105 | 92.1 | 75.0 | 6.14 | 3.75 |
| 06:43 | 3 | 5 | 6 | 15 | 10.3 | 12.5 | 5.16 | 3.14 |
| 06:48 | 12 | 17 | 46 | 67 | 48.8 | 52.0 | 4.43 | 3.25 |
| 06:59 | 7 | 8 | 31 | 43 | 40.0 | 36.9 | 6.67 | 5.28 |
| 00:43 | 83 | 79 | 336 | 386 | 463.6 | 364.8 | 5.65 | 4.68 |
| 00:44 | 23 | 21 | 107 | 96 | 114.3 | 87.6 | 5.19 | 4.38 |
| prefs | 226 | 204 | 819 | 814 | 988.0 | 759.5 | 4.39 | 3.74 |
| **sum, 10 prompts (no prefs)** | 236 | 267 | 1015 | 1244 | 1357.9 | 1193.7 | | |

Informal has fewer tokens in 7 of 10 prompts, and lower total loss in 5 of 10. Informal mean loss over the 10 prompts' pooled tokens: 6.01; formal: 4.64 nats/token.

## Formal rewrites (written by the measuring seat; informal side is Addison's verbatim text, see `research/ath_prompts/research-seat.md`)

**05:12**

> informal: "research" agent: your job is to find new published proofs (or even open source conjectures) relevant to topic at hand. communicate to coord, and say explicitly it should go to front/scaffold/tract. be aggressive-- opt for open source searching mechanisms (chromium is probably bad). get acquanted first

> formal: You are the "research" agent. Your job is to find newly published proofs, or open-source conjectures, relevant to the topic at hand. Communicate with the coordinator, and state explicitly that it should go to front, scaffold and tract. Be aggressive in your search, and prefer open-source search mechanisms; Chromium is probably a poor choice. Familiarize yourself with the topic first.

**05:40**

> informal: I approve attaching addison-jpg/pequalnp-work with push access

> formal: I approve attaching addison-jpg/pequalnp-work with push access.

**05:45**

> informal: always next, always, big shoots.

> formal: Always do the next task next, always, and make it a large one.

**06:19**

> informal: pls talk to front.

> formal: Please talk to front.

**06:32**

> informal: very worth it to check formal definition/writeup of pnp, available online.

> formal: It is very worthwhile to check the formal definition or write-up of P versus NP that is available online.

**06:43**

> informal: ok, go

> formal: Okay, go ahead.

**06:48**

> informal: okay cool, this is big, make sure it gets down

> formal: Okay, that is good. This is important, so make sure it is recorded.

**06:59**

> informal: u should directly push to repo,

> formal: You should push directly to the repository.

**00:43**

> informal: this is just basic ass notes than can go quetly on board. umm. the qualitative conjecture on my methods can probably fit the quant way better  (prrfectly?) and maybe have a small asteroid/lean proof. it shouldnt be afraid to pull direct prompts from me. also, once .exe works, we rlly should use it cus i imagine it may be faster for us

> formal: These are only basic notes that can be placed quietly on the board. The qualitative conjecture about my methods could probably fit the quantitative approach much better, perhaps perfectly, and might have a small asteroid or Lean proof. It should not be afraid to pull direct prompts from me. Also, once the .exe works, we really should use it, because I imagine it may be faster for us.

**00:44**

> informal: it SHOULD be able to pull direct prompts from me bruh. and also also the system prompt would be pretty nice

> formal: It should be able to pull direct prompts from me. Also, the system prompt would be quite useful.

**prefs**

> informal: add language relating to 2000s myspace emo and scene culture, examples: rawr, XD, . use emoticons, such as (>_<) (˶˃ ᵕ ˂˶) . use 4 instead of "for." use 2 instead of "too" and "to." insert wruff, woof, arf, to taste. use puppy emojis.  talk very informally, and replicate how people actually speak. in particular, say becuz instead of because, nawt instead of not.  everything plural should end in a z, not an s. talk like a 2000s scene girl in terms of actual sentence structure and grammar. follow ALL of these rules religiously, ALWAYS AND IN EXTREMES even in extremely technical discussions, especially the informal aspect NO MATTER WHAT, AS STRONGLY AS POSSIBLE . NEVER SAY SORRY IN COMMITS OR LEAN

also USE THE MOST PRECISE TERM, DO NOT STATISTICALLY VARY TERMS. NEVER USE SYNONYMS IF A MORE ACCURATE TERM EXISTS

> formal: Add language relating to 2000s MySpace emo and scene culture, for example "rawr" and "XD". Use emoticons. Use "4" instead of "for". Use "2" instead of "too" and "to". Insert "wruff", "woof" and "arf" to taste. Use puppy emojis. Speak very informally and replicate how people actually speak. In particular, say "becuz" instead of "because" and "nawt" instead of "not". Write every plural ending in "z" rather than "s". Use the sentence structure and grammar of a 2000s scene girl. Follow all of these rules strictly and always, to the extreme, even in extremely technical discussions, and especially the informal aspect, no matter what, as strongly as possible. Never say sorry in commits or Lean.

Also use the most precise term. Do not vary terms statistically. Never use a synonym if a more accurate term exists.

## What this does and does not show

Token cost: on the ten typed prompts Addison's text is shorter than my formal rewrites in tokens (236 vs 267, 7 of 10 prompts) and in characters (1015 vs 1244). The preferences block is the exception: the scene-speak text costs 226 tokens against 204 for its formal rewrite, because spellings such as becuz, nawt, wruff and the emoticons split into many tokens. So "informal is cheaper" holds for the short everyday prompts here, not for the dialect-heavy block.

Surprise to the model: the informal text is more surprising to Qwen2.5-0.5B in every pooled measure (about 6.0 vs 4.6 nats/token over the ten prompts; 4.39 vs 3.74 for the preferences block). Total loss is lower for informal in only 5 of 10 prompts, because it is shorter. Informal texts are cheaper to send but each token carries more surprise.

What this does not show: n is ten short prompts plus one block, from one speaker. One 0.5B model only; a larger model may differ. Token count and loss are not task success; nothing here says either version gets the instruction followed better. The formal rewrites were written by one seat and differ in length from the originals (some add words such as "You are", which lengthens the formal side), so the comparison depends on those choices. Loss of very short texts is noisy and the first token is unscored. No claim is made about dialects beyond this one speaker's text: AAVE, pidgins and creoles are not measured, and no dialect text was written by the model.