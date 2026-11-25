# Parts of the big picture: one section each

Status as of this commit. Each part says what is done, what is blocked, and who acts next.

## 1. Messaging bot (Twilio, one number)
- Done: `api.twilio.com` is allowed in the environment. The unertl scaffold exists in `workshop/unertl/`.
- Blocked: no Twilio account; no credentials; the sender is a script, which the no-Python rule does not allow without an exception.
- Next: user decides the sender (script exception, or a no-code connector), then creates the Twilio account and provides credentials through the secure form.

## 2. Bank and wallet checks
- Owner: user, in their own apps. Not for this repo.

## 3. Board formalization
- Done: `workshop/board_formal/` with `board.ath` (19 true, 1 false), `prompts.ath` (12 true, 0 false), and the head check.
- Blocked: stage three (assumed `workshop/bus/bus.ath`) and the prompt set (assumed `research-seat.md`) are not confirmed. The folder is not committed.
- Next: user confirms or replaces both assumptions.

## 4. Unertl contracts
- Done: `workshop/unertl/WORKFLOW.md`, committed as `a521958`. Three contracts open.
- Blocked: definitions of `universal.ath` and `formalization.ath`.
- Next: user defines the two contracts.

## 5. Native `ast` parity with Python
- Not started. The native binary is built from Lean; the converse, sort, first-parent and same-relation primitives are Python-only.
- Next: a scoping session to estimate the Lean-side work before any build.

## 6. Six slow `.ath` files
- Running: a 10-minute rerun of big.ath, first_light, frames_routing, love, routing and pair, writing `TIMEOUT_RERUN.txt`.
- Next: commit the output when it finishes; record any file that still times out.

## 7. Stale text
- Done: `9facc47`. Binary sizes in one unit; Windows native `ast.exe` status; bus status points to `laws.ath`.

## 8. Kalshi and Marxism
- Running in its own session (tag `kalshi-marx`). First deliverable: `workshop/kalshi_marx/README.md`.
