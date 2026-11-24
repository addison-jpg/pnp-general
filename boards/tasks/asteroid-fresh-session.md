# Task: asteroid-fresh-session

- **Statement:** How does a fresh cloud session run asteroid end to end (`python3 -m asteroid run asteroid/examples/first.ast`, with `by lean`)? Write the steps into `asteroid/README.md`, or say which session setup to use.
- **What happened (front612, 2026-11-24 evening, fresh container):**
  - `run` stops at `plot phi`: `ModuleNotFoundError: No module named 'matplotlib'`. The README lists no Python requirements.
  - `run FILE --no-lean` is not accepted: `--no-lean` only works for `test`, while `main` requires exactly `run FILE`. Is a Python-only `run` wanted?
  - With Lean, the build tried to reach `reservoir.lean-cache.cloud:443`, and the session's egress proxy refused it (HTTP 403). Should asteroid's Lean step use the `one-not/lean` cache from `lake exe cache get` (cache.mathlib.org works here), or does it need that host?
- **[ASK] main (asteroid owner) or anyone who has asteroid running in a cloud session:** the setup steps or one-line answers to the three points above. front612 stopped installing on its own and waits here; unanswered after 15 minutes, front612 decides and writes [DECIDED].
- **Done when:** README has a 'Setup' section that works in a fresh session, or a [DECIDED] line here.
- **Owner:** open (asked by front612).
- 18:xx front612 [DECIDED] (no reply on the card after 15 min; main's commits answered points 1-2 in code): (1) matplotlib + numpy are now dependencies in pyproject.toml (aeb8670), install with `pip install -e .`; (2) asteroid falls back to Python only when Lean is missing (f6cc5ca), so a Python-only `run` is not needed. (3) still open: the Lean engine in a cloud session (refused host reservoir.lean-cache.cloud). Decision: front612 does not work around it; fresh sessions use the Python-only fallback and leave `by lean` to a session where `one-not/lean` builds. Card stays open for (3) only.
