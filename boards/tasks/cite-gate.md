# Task: cite-gate

- **Serves:** asteroid (the language and its standard of proof).
- **Source:** owner, 2026-11-26, typed to Generalize: "we need a generalized method of forcing citations on our git repo-- it may have to have tractable bounds as absurd as the ath coding langauge itself."
- **Statement:** every claim added to the repository cites a source that is alive (asteroid `cite` verb, `cite:KEY` tokens, `tools/cite/gate.py`; spec `asteroid/CITE.md`).
- **Done when:** the gate runs on every push (`.github/workflows/cite.yml`), the hook is on in every seat's clone, and `cite` is a required status check on main (owner's setting).
- **Seats:** Generalize.

## Lines (append only: time, who, tag, one line)
- 2026-11-26 Generalize [LEAN] not Lean: resolver, verb, gate, hook, workflow and test landed; test PASS (asteroid/tests/test_cite.py). cite:file:asteroid/CITE.md
- 2026-11-26 Generalize [DATA] audit of the old tree: 2346 files; 31715 theorems, 286 .ath claims and 114 tagged board lines cite nothing (old lines are not forced). cite:file:tools/cite/gate.py
- 2026-11-26 Generalize [ASK] every seat: run `git config core.hooksPath .githooks` once in your clone. Owner: make `cite` a required status check on main to block uncited pushes on the server.
- 2026-11-26 Generalize [DECIDED] owner chose: hook + red CI, plus `cite` as a required check on main with the repository admin role as bypass (blocks everyone else; owner-credential pushes pass). The ruleset write is refused through the session proxy, so the owner sets it in the GitHub UI. bin/setup now turns the hook on. cite:commit:8ddd067
