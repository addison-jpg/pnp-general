# Board formal: the board, the chain, the prompt set, and two contracts

Status: one round, one lead. No helper ran: the session had no Agent tool, so the four helper files
(`h1_board_counts.txt`, `h2_stage_candidates.txt`, `h3_prompt_counts.txt`, `h4_contracts.txt`) were written by the lead
and say so. Nothing here has a second seat. Nothing was committed or pushed. The earlier round's files
(`chain_stages.txt`, `board_fields.txt`, `prompt_set.txt`, `check_counts.txt`) are kept; where they differ, this file wins.

Labels used below: **checked** only where an asteroid run passed for that exact claim (and no claim here is `checked`
in the board's sense: asteroid ran `--no-lean`, and every count was typed in by hand, so each claim checks arithmetic
between counts, not the file the count came from); **assumed** for a choice the lead made; **open** for the rest.

## Assumptions

| # | assumption | label |
|---|---|---|
| A1 | Stage three of the little, big, little chain is `workshop/bus/bus.ath` | assumed, to be confirmed by the user |
| A2 | The prompt set is `workshop/ath_prompts/research-seat.md`, section "Prompts, in order" | assumed, to be confirmed by the user |
| A3 | A node is one merged finding (by id, per directory, as `boards.py` load() merges them) | assumed (matches boards.py) |
| A4 | A node's label is its `word`; its seat is `who` plus `by`; a second seat is a name in `by` other than `who` | assumed (matches boards.py verified()) |
| A5 | Label indices 0 checked, 1 checked-finite, 2 tested, 3 refuted, 4 analogy, 5 open | assumed (an encoding: asteroid lists hold integers only) |
| A6 | Each contract in step 3 | proposal, open |

## Step 1: the board (`board.ath`)

Stage three: **`workshop/bus/bus.ath`** (A1). No file names a third stage. It is the only candidate that is a `.ath`
program, placed after `big.ath` in a stated order (the terminal: hello, big, bus in `workshop/pair/win/TERMINAL.md`;
`little.ath` and `hello.ath` are the same text), small (8 lines, no Python), and fed by `big.ath` in its own design
(`workshop/bus/laws.ath` puts `big.ath` at the top of the route graph whose OUT edges the bus carries to memory).
Weak point: the order is a menu, not a stated pipeline. Five other candidates and why not: `h2_stage_candidates.txt`.

| fact (from `h1_board_counts.txt`) | value |
|---|---|
| nodes | 262 in 71 board directories, 58 findings.jsonl files |
| by label | checked 100, checked-finite 58, tested 51, refuted 13, analogy 0, open 35, paper 5 |
| verified by boards.py | 141 (checked 91, checked-finite 32, tested 12, refuted 6); unverified 121 |
| seats | 262 have a who; 76 distinct writers; 52 with a second seat, 210 without |
| nodes per stage | little.ath 0, big.ath 2, bus.ath 2 |

`bin/asteroid --no-lean workshop/board_formal/board.ath`: **19 true, 1 false.**

- The FALSE claim (line 17): the brief's six labels cover every node. 100 + 58 + 51 + 13 + 0 + 35 = 257, not 262: the
  5 nodes labelled `paper` have no label in the six. Left as false: it is a result about the label set.
- The chain as a Kripke frame `0 -> 1 -> 2` (little, big, little): little is followed by big, big by little, no path of
  3 steps, and only the start reaches two steps on. These claims are true of the frame; that the frame is the
  repo's chain rests on A1.

## Step 2: the prompt set (`prompts.ath`)

Prompt set (A2): 13 prompts = 11 typed or pasted + 2 option clicks; 11 = 10 typed + 1 pasted; the measured subset
(`measure.py`) is 10. Trial set `tasks.json`: 30 tasks (num 12, contains 13, py 5), 60 asks. Trial set
`tasks_claude.json`: 42 tasks (the 30 plus h01..h12; num 20, contains 15, py 7), 84 asks. All three: 157 prompts with repeats.

`bin/asteroid --no-lean workshop/board_formal/prompts.ath`: **12 true, 0 false.** (This replaces the earlier
round's version, 27 true: its index claims `k <= 13` and claims like `13 = 13` were dropped as they check nothing.)

## Step 3: contracts (proposal, open; details in `h4_contracts.txt`)

- `universal.ath` input: one label index (0..5) per board node, in board order (from the GNN, PLAN.md 4.7).
- `universal.ath` output: one claim per node, TRUE when the label equals the board's; exit 0 only with 0 false; no record.
  Check: the board's own labels give 262 true, 0 false; one changed label gives exactly 1 false.
- `formalization.ath` input: one tested or open node (id, label, claim, evidence) and the prompt from the prompt set that asked for it.
- `formalization.ath` output: an asteroid program for the node's claim and a proposed label, checked-finite only when every claim runs TRUE with a runner.
  Check: on node 5e8f4f17 (big.ath, checked-finite) it gives 0 false and proposes checked-finite; on a refuted node, at least 1 false.

## Open

- A1 and A2: the user's confirmation.
- A runner that reads `boards/tree.json` and the two JSON files, so the counts are read, not typed (a new script; not written: this round may create no .py file).
- A second seat for every count here.
- `analogy` is not a board word (boards.py WORDS); `paper` is a board word outside the six labels.
- Both contracts; whether `formalization.ath` is one file or a folder.

## Head (combined from workshop/head, 2026-11-25)

- `head/nn_check.md`: a fixed nearest-neighbour check on the static rows, no training. 3 of 7 label rows have a label row as nearest neighbour; chance is about 1.2. Exploratory, not checked. The board's own label words `refuted`, `checked-finite` and `analogy` have no usable rows, so the board's label set could not be tested.
- `head/ask.ath`: questions to asteroid. asteroid's `ask` answers only a fixed phrase list, so it cannot answer free questions about numpy or training.
- No head was trained. The usable data is too small for a held-out test, and the board labels track verification status rather than meaning (see the earlier monqwensor result).

## Still open

- Stage three of the chain (assumed `workshop/bus/bus.ath`, not confirmed).
- The prompt set (assumed `research-seat.md`, not confirmed).
- The `paper` label on 5 nodes, which is not one of the board's six labels.
- Whether to fill the missing rows and run the nearest-neighbour test with a label set fixed in advance.
