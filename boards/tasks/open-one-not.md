# Task: open-one-not

- **Statement:** The general case of the one-NOT theorem: no smallest counterexample (`no_minCE`).
- **Seats:**
  - A1 (Opus): paper proof attempt of the mixed step at states of negative slack, the one local statement no circuit has broken
  - A2 (Sonnet): mixed slack as a Lean definition in the project's terms, so the missing arrow can be stated
  - A3 (Sonnet): search for a counterexample to the mixed step and to the step under no gate-saving rewiring, on irreducible circuits with a read NOT gate
- **Done when:** a checked theorem, a counterexample checked twice, or the exact missing lemma written down.

## Current target

- **BottomPay**, a Hall condition (A10, A14). Chain, in order of dependence: BottomPay → LightAbsorb → DDAbsorb (checked) ; DDAbsorb with the no-DD count gives MixedCount (paper, A4 note §2; no-DD half checked) ; MixedCount ↔ MixedStepNeg → no_minCE (checked) ; no_minCE → L_meta_951 (checked). `no_minCE` itself is NOT proved.
- `MixedStepNeg` is **equivalent** to the full count (checked, `MixedStepNegIff.lean`): a restatement, not a reduction. Do not attack it as a local lemma.
- F2-transfer must use the one-NOT hypothesis: without it the step fails (146 of 248 negative states at t = 4). The NOT gate enters only through DD sets.
- Findings (verified, `boards/TREE.md`): MixedSlack, MixedStepNegIff, F2Transfer, F2TransferRun, DDAbsorb, LightAbsorb, L_meta_951_of_minCE.

## OPEN / STOPPED

- STOPPED A13 (container restart; partial A10_bottom_hill.py kept; reopen to continue) (Sonnet): hill-climb for a BOTTOM PAY failure: mutate gates of stored one-NOT circuits n <= 9 and switch circuits (as `A7_hill.py`), keep correct circuits whose minimum over DD states of (matroid-union rank in E minus Σ need_w) does not rise; use `rado` from `A10_light_attack.py`. Record start count, steps, minimum reached, any failure state. -> `one-not/research/open/A10_bottom_hill.py`, `A10_bottom_hill.md`
- 2026-11-25 A14 (Opus) STOPPED A14 (container restart; partial A14_bottom_hall.py kept; reopen to continue): BOTTOM PAY (A10 §3, matroid form): at every mixed state of a one-NOT correct circuit (pairwise |S_a ∩ S_b| ≤ 1), for every set A of OR gates outside the top family that are 0 at 1_Q, Σ_{w DD} (need_w − r_w(A)) ≤ |E \ A|, r_w = rank of A in the bottom forest matroid of w (classes: heavy atoms joined, light singletons). Implies light absorption (paper, A10 §1). Tested 0 failures (same runs as the A10 line). -> one-not/research/open/

## Refuted / dead

- Minimality alone: gates' ≥ base' but |F2'| ≤ gates', so it points the wrong way (A1).
- One zero point per DD set (bottom, maximal in {h=0}, or line form at Z_w): bottom runs of two DD sets overlap (2,775 of 136,843 states n ≤ 9; 242 states for any single choice); payment needs a matroid-union re-choice (A10, A14).
- Light atoms sit in {h=0}; their natural zero point 1_Q gives F2 merges that overlap between DD sets (284 stored states) (A7).

## Decided (one line each; the file holds the proof or the note)

- A1 (Opus): mixed step at negative states = the count at every mixed state; fails at t = 4 only at negative states. -> `Open/MixedStepNegIff.lean`, `one-not/research/open/A1_mixed_step.md`
- A2: `mslack`, `MixedStepNeg`, `MixedStepNeg → no_minCE`. -> `Open/MixedSlack.lean`
- A3: mixed-step search on irreducible read-NOT circuits, no counterexample, 0 negative-slack states reached. -> `one-not/research/open/A3_mixed_search.md`
- A4 (Opus): F2 count holds at every mixed state with no DD set (paper; sign, overlap, witness, GoodT lemmas checked); the NOT gate enters only via DD sets; open obstacle is DD-absorption (tested 0 failures at 60,317 DD states). -> `Open/F2Transfer.lean`, `one-not/research/open/A4_f2_transfer.md`
- A5 (Sonnet): F2-transfer |F2'| ≥ base' at every restriction (1,353,627 with base' > 0) of 3,263 one-NOT circuits, n 4..10, 0 failures (tested); tight both NOT-alive and NOT-killed. -> `one-not/research/open/A5_transfer_t1.md`
- A6: unit-form merges are OR gates in F2Mix. -> `Open/F2TransferRun.lean::unitMerge_card_ge_and_subset`
- A7 (Opus): DD-absorption not proved, no counterexample (0 failures at 149,861 sampled and 1,147,168 exhaustive n ≤ 11 DD states); reduced on paper to light absorption. -> `one-not/research/open/A7_dd_absorption.md`
- A8: no-DD mixed count under pairwise |S_a ∩ S_b| ≤ 1. -> `Open/F2TransferRun.lean::mslack_nonneg_of_noDD`
- A9: two heavy points cannot overlap; heavy merges lie in F2Mix with card ≥ heavy − 1. -> `Open/DDAbsorb.lean::heavy_overlap_false`, `heavyMerge_card_ge_and_subset`
- A11: LightAbsorb → DDAbsorb. -> `Open/DDAbsorb.lean::ddAbsorb_of_lightAbsorb`
- A10 (Opus): light absorption not proved, no counterexample; paper: light absorption ≤ BOTTOM PAY; tested 0 failures at 136,843 (n ≤ 9) + 119,467 (n ≤ 16 sampled) + 1,010,325 (200 switch circuits) DD states. -> `one-not/research/open/A10_light_absorption.md`
- A12: `bottom_F2WitMix`, `bottom_zero_of_H0`, `BottomPay`, `lightAbsorb_of_bottomPay`. -> `Open/LightAbsorb.lean`
- All Open/ files are under `one-not/lean/PEqualNP/W951/`, namespace `PEqualNP.Outside.L_meta_951_aux.F2Transfer`; build `cd one-not/lean && lake build PEqualNP.W951.Open.<File>`; no sorry.
