> **CLOSED 2026-11-24 by the owner (only asteroid work continues). This file is the record; nobody works on it.**

# Task: file-tree-merge

- **Serves:** owner's PRIME DIRECTIVE (`boards/ops.md`): "consider the current repo to be a minimum spanning tree. combine leaf nodes where they are relevant. meaning lean proofs. then py, then readme. that order. propogate up."
- **Statement:** Merge leaf files upward: Lean, then py, then READMEs; what is too expensive to merge is mapped in `research/MST.json`.
- **Done when:** merged files are on main with the build and the sorry list unchanged; `research/MST.json` matches the tree.
- **Seats:** observer (session_01GmnDhegXGF8MJNAhiA1AHp). Anyone may take the open parts: write `TAKEN <who> <time>` below. Nobody asks the owner.

## Lines (append only: time, who, tag, one line)

- 18:30 observer [DONE] `proofs/w951`: 75 leaf files -> 14 (8e37776); each old file is `section <OldName>` in its new file; `lake build PEqualNP` passes, same 9 sorry declarations (`no_minCE` + 8 PayDraft drafts in `W951/MiscSmall.lean`).
- 18:30 observer [DONE] READMEs 19 -> 5 (ab32b7c); owner's line and quotes verbatim; long front page kept whole in `research/notes/front-page-2026-11-24.md`.
- 18:35 observer [DONE] `research/MST.json` regenerated (0b4a0eb).
- 18:35 observer [DECIDED] `proofs/main/` (689 leaves, about 295,000 lines) and py (57 leaf scripts) are NOT merged: re-building 295,000 lines is too expensive, and scripts are run by name. They are mapped in `research/MST.json`. OPEN for anyone with a built `proofs/main/` tree.
- 18:35 observer [DATA] If your file imported one of the 75 old `proofs/w951` modules, import the new file (old name = section name inside it).
- 22:50 observer [CLOSED] stopped here per the owner ("close all nonsense being done that isnt asteroid related"). Everything of this task is already on main (8e37776, ab32b7c, 0b4a0eb); nothing running, no open branch to land. `proofs/main/` leaves and py stay mapped only in `research/MST.json`.
