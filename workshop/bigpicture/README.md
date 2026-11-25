# Big picture: what is formalized, and how far it can be trusted

Status: an assessment from files and counts. Asteroid and Lean were not re-run for this page. Each figure is quoted from the file that gives it.

## 1. Size

- 91 `.ath` files, 1,909 `.lean` files (`INVENTORY_ATH.md`).
- Lean is concentrated in `lean/` (1,669) and `one-not/` (219). `one-not/` has Lean and no `.ath`.
- Biology has no `.ath` and no `.lean`. Physics has 3 `.ath` files, philosophy 3, math 4, culture 8, core 12, and the root 20.

## 2. What is verified, by the repo's own figures

- RESULTS.md totals: 91 checked, 32 checked-finite, 12 tested, 6 refuted. The row sums match these totals (`STATUS_CHECKS.md`).
- Board: 262 nodes; 141 verified by `boards.py`; 210 with no second seat (`board_formal/BOARD_FORMAL.md`).
- Mobius twist: 10 true, 0 false (`workshop/mobius/checks/twist.ath`). Pipeline: 5 false lines, kept as run.
- Bus: `laws.ath` 17 true, 0 false under Python asteroid, after the converse and sort primitives were added.

Only the figures from those runs are verified. The rest are counts or plans.

## 3. Where the files disagree

Five disagreements, from `STATUS_CHECKS.md`:
1. Bus laws L3 and L4: one file says "checked in code", another says "nothing here is checked", and the GNN plan says L1, L3, L4 are checked on one slice. The bus README needs one status line.
2. Windows binary: BOARD.md says native `asteroid.exe` is "Done" at 4.2 MB. README.md says the Windows binary is open. These cannot both be right.
3. Full bundle size: 47 MB in README.md, 45 MB in BOARD.md.
4. Linux native binary: 4.4 MB in one BOARD.md section, 4.3 MB in another.
5. Windows binary name: `asteroid.exe` in one section, `ast.exe` in another (the board's task table says it was renamed).

These are stale-text disagreements, not verification failures. They should be fixed by editing the files, not by changing claims.

## 4. Native versus Python

Run on the same files this session:
- `workshop/orchestra/rule.ath`: both 3 true, 0 false. Agree.
- `workshop/bus/laws.ath`: Python 17 true, 0 false. Native skips all 28 lines ("not in the Lean version yet"), giving 0 true, 0 false. Disagree: the native binary lacks the new primitives.
- `little.ath`: native ran past the timeout and was terminated. No verdict.
- Asks: native answers none of them. Python answers all seven (`workshop/asks/ASKS.md`).

So the native `ast` is not yet a second checker for the new language. It is a subset.

## 5. What this means

- The formalized core that is trustworthy is small: the finite checks listed in section 2, each re-runnable with `bin/asteroid --no-lean`.
- Most of the 91 `.ath` files have not been run in this assessment, so their status is unknown here.
- Lean is large (1,909 files) but was not built in this session, so its status is also unknown here.
- Biology is empty in the formal layer.
- The board's labels track verification, not meaning, so they cannot say which claims matter.

## 6. Next, in order

1. Run every `.ath` file with Python asteroid and record the true and false counts per file. Put the counts in one table.
2. Fix the five stale-text disagreements in place.
3. Bring the native `ast` up to the Python checks, starting with the converse and sort primitives, so the two can be compared file by file.
4. Decide whether biology gets a formal layer, and what it would claim.

## Not claimed

- That the repo is formally correct overall.
- That any single formal result means more than its own check.
