# The small board

A small copy of the top board. It works on one program: little.ath at the repo root.

## Format

Each card is one `record` line in `board.ath`. A card has:

- one statement;
- a status: OPEN, TAKEN or DONE;
- an owner;
- a "done when" line.

The label is `open` for a card that is not done. It is `checked-finite` only when a claim in the file backs it.

## The collaborator

little.ath is the program the cards refer to. It has 4 claims. The cards say what must hold of it: a pure claim set, and the same verdicts from the native ast checker and the full asteroid.

## Run

    bin/asteroid --no-lean workshop/board/board.ath
    bin/asteroid --no-lean little.ath

The last line of each must show 0 false. The run writes the records to `findings.jsonl`, and they move up the findings tree.
