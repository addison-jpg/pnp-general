# invisible

How much of a seat's work leaves no checked line? Run `python3 -I workshop/ath_prompts/invisible/invisible.py` (well under a second).

## The data

Only the seat table under "Data so far" in `ath_prompt_method.md`: 11 seats (6 Sonnet, 4 Opus, 1 Fable), tokens as the tools reported them, 1,429,022 in all. The script parses that table; nothing is typed in by hand.

## What is measured, what is a proxy, what is not measured

| quantity | value | label |
|---|---|---|
| tokens in seats whose result has no checked line (A7, A10 obstacles; the Fable robustness seat, tested) | 469,254 of 1,429,022, **32.8%** | checked-finite over the 11 recorded rows (the rows themselves are tool reports, not re-measured) |
| the cheapest seat (A8, 84,399) as the fixed read of rules and files, paid by every seat | about **65%** of all tokens | proxy: an assumption, not a measurement. A8 also wrote a lemma, so this over-counts reading |
| per seat, min(floor, tokens) / tokens | 0.85 to 1.00 for the Sonnet seats (A8 is the floor itself), 0.40 to 0.58 for Opus and Fable | proxy, same assumption |
| tokens per committed line; coordination tokens; tokens spent by the coordinating seat | not measured | open: the table has no such columns |

So the honest answer is: about a third of the recorded tokens left no checked line at all, and by a rough proxy most of every narrow seat's tokens were reading. An obstacle is not wasted: it is written down and it shapes the next line. It is invisible only in the results table.

## Reading (analogy)

Susan Leigh Star and Anselm Strauss, "Layers of silence, arenas of voice: the ecology of visible and invisible work", *Computer Supported Cooperative Work* 8 (1999) (cited from memory): work becomes invisible when only its outputs are counted, and the work of reading, articulating and coordinating disappears from the record. Here the record is the results table and the findings tree. The reading of rules, the failed attempts and the coordination between seats do not appear in it.

`core/ontology/WORKFLOW.md` reads the repository through Kim Unertl's information-ecology frame, where a keystone species is the one whose removal splits the map. The essential worker is the human version of the keystone: the person whose work holds the system together and is the least seen. The reading seat and the coordinating seat are this repository's keystone work. That is analogy; the 32.8% is the only number here.

## Open

- Record, per seat, the lines it committed and the files it read, so the reading share is measured, not proxied.
- Record the coordinating seat's own tokens. It is absent from every table so far.
