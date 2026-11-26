# Task: fork-hygiene

- **Serves:** owner request (2026-11-26, to research-desktop): responsible forking and citation of OUR repositories.
- **Scope:** our own repositories, notices and wording only. No action against anyone else's fork (upstream brilliant-hq/pequalnp-proofs is Apache 2.0; forking is allowed).
- **Seats:** research-desktop (session_01GmnDhfeNJTFgW7ismYzbXh), with coord. Nobody asks the owner; [ASK] lines here.

## Audit (2026-11-26)
- Public under addison-jpg: pnp-general only (0 forks). Private: asteroid-api, desktop-tutorial. pequalnp-work and pequalnp-proofs: 404 to this session.
- README: status sentence present (line 66: "Nothing here settles P versus NP"); MIT / Apache 2.0 split present (License section, lists upstream-derived files). CITATION.cff abstract: "does not claim any result on P versus NP".
- Wording scan of *.md for overclaims: one hit, notes/note-3-big-picture.md "would be a major breakthrough", conditional and correct; no change.
- Non-main branches (owners decide): checker, claude/mergesdr, claude/mergesdr2, claude/priceoff, claude/tract-base-blocker, mst-lean, mst-lean2, mst-readme, mst-readme2, qg-d2-nots-wip, refactor/pillars, tractability-kernel-612, tree-refactor. research-desktop-d1-wip is research-desktop's own and superseded by main.

## For the owner (not doable from a session)
- Visibility: pnp-general is public; make it private in GitHub settings if that is no longer wanted (owner said 08:03 public is acceptable).
- Old public fork addison-jpg/pequalnp-proofs: if it still exists under your account, it holds branch claude/happy-hypatia-zz54tp; delete it or the repo in GitHub settings.

## Lines (append only: time, who, tag, one line)
- 2026-11-26 research-desktop DONE: CITATION.cff license -> [MIT, Apache-2.0]; README BibTeX license -> MIT AND Apache-2.0; README status sentence now asks forks/mirrors/citers to keep it, the meaning of "checked", and the upstream attribution.
