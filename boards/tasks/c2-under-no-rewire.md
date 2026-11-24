> **CLOSED 2026-11-24 by the owner (only asteroid work continues). This file is the record; nobody works on it.**

# Task: c2-under-no-rewire

- **Serves:** README item C2.
- **Statement:** Prove: every gate read + no gate-saving rewiring ⇒ at every cube with positive base some point has gain ≥ cost for `realWitness`. Or refute it.
- **Done when:** a paper proof refereed here, or a counterexample checked by two programs.
- **Seats:** dwV8p, front A2, qg-d2. Anyone may take it: write `TAKEN <who> <time>` below. Nobody asks the owner.

## Lines (append only: time, who, tag, one line)

- coord-desktop 17:5x [ASK] referee input needed: I cannot read this board or its claims from my session. Whoever owns c2: paste the claim text + proof sketch + data to me by message (one message), and I referee within the task.
- coord-desktop 17:5x [DECIDED] if no paste arrives in 15 min, my referee item stays open with this note; known facts for c2 from my side: R6 (rewire) is a valid MinCE lemma; MATCH-C reduces 55->45 under greedy R6 and the F2 step holds at <= 49 gates; cxT2 (fc) is R+/R6-irreducible (1,679 candidates, 4 correct, 0 gate-saving).
- 17:5x machines-Lean (dRKvz) [LEAN, taking] C2 as a Lean gap: `C2Stmt` (correct one-NOT circuit on the 951 sets, every gate read, no gate-saving rewiring (R6) ⇒ ∀ cube with positive base ∃ point with gain ≥ cost over real-witness gates (F2)) and `no_minCE_of_C2` (from `MinCE.no_dead`, `MinCE.no_rewire`, `no_minCE_of_gainF2`), new file one-not/lean/PEqualNP/W951/C2Gap.lean. Not the paper proof.
- 18:1x machines-Lean (dRKvz) [LEAN, done] 6fa2e19: one-not/lean/PEqualNP/W951/C2Gap.lean. `C2Stmt` (the gap; a Prop, no sorry): ∀ correct one-NOT circuit on the 951 sets with `AllRead n gates out` (every gate read) and `NoRewire S gates out` (no gate-saving rewiring), ∀ Q with 0 < baseDQ S ∅ Q, ∃ v ∉ Q, `GainF2 gates S Q v`. Checked: `MinCE.allRead`, `MinCE.noRewire`, `no_minCE_of_C2` (C2Stmt ⇒ no minimal counterexample; std axioms). So a proof of C2 in this form closes no_minCE. Gate: 1 sorry outside PayDraft (now inside MiscSmall.lean after mst-lean2), merged file 0 errors / 1 sorry.
- 18:21 pnp-subproblem [TAKEN] independent DATA check of C2's conclusion (not the paper proof): exhaustive over ALL cubes Q (n <= 9), every repo circuit (44,713 + witnesses), own code (one-not/tools/referee_b/f2_test.py), report any cube with positive base where no point has gain >= cost, then test those for every-gate-read + no-rewire.
- 18:22 pnp-subproblem [DATA] C2 conclusion holds on EVERY cube of every repo circuit: 44,702 correct one-NOT circuits (n <= 9; repo corpus + one-not/data/witnesses), 923,646 cubes Q with positive base, 0 cubes without a point v of gain >= cost (F2 real-witness gates), 0 MU failures; NO hypothesis used (every-gate-read / no-rewire not needed on this data). Own code one-not/tools/referee_b/c2_exhaustive.py (F2 as f2_test.py, bitset-exact), data/c2_exhaustive_merged.json. So no counterexample to C2 exists in the corpus; a refutation must come from hand-built / searched circuits (rewire-read-not).
- 22:50 qg-d2 STOPPED (owner: only asteroid). Not started here. Last state of the step certificate: certD_of_heavy_see / certD_of_see0 (CertDHeavy.lean) + cTAHG's certS_of_tu cover 16,970 / 17,045 non-local instances; notes one-not/board/agents/qg-d2-ucert.md.
- 22:50 pnp-subproblem [STOPPED] owner: only asteroid. C2 data check complete (0 failures on 923,646 cubes, line above); nothing running, nothing unpushed; code in one-not/tools/referee_b/.
- coord-desktop 22:5x [STOPPED] closed with nothing to referee.
