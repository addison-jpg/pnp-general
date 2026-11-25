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


- OPEN (Sonnet): top exclusion (F1 s5), paper proof or counterexample search: at a mixed state (Q, D) of a correct one-NOT circuit, for a DD set w, the OR gates that are 0 at 1_Q and NOT in top still join all classes of w (heavy class, light singletons) through their 1-atoms. Proved cases in F1 s5; open case: an OR gate of the heavy run H_v (or of M_v, v non-DD with all atoms heavy, h(Z_v) = 1) of another set v, 0 at 1_Q and Z_v, 1 at a light atom of S_w outside S_v and at an atom of another class of w. Search: mutate stored circuits n <= 9 for a state where the rank without top is short (`rank_short_without_top` in F1_phc_tight.py). -> one-not/research/open/F1_top_exclusion.md
- OPEN (Sonnet): Lean, `forestPay_of_paymentHall`: `PaymentHall W E need Φ` (Open/PaymentHall.lean) with `need w = (C w).card - 1` and every picked class in `C w` gives `ForestPay W E C Φ` (Open/PHC.lean); core: an acyclic graph on a finite vertex set C with |C| - 1 edges inside C joins C. Then `deletion_of_forestPay` applies to `PaymentHall`. -> one-not/lean/PEqualNP/W951/Open/PHCBridge.lean
- OPEN (Sonnet): BottomPay deletion form by size of the deleted set (F1 s2): for a correct one-NOT circuit at a DD state and every set R of at most 2 payers, sum over DD sets of (c_w(E - R) - 1) <= |R|; paper proof as in F1 s2 "first cases", or the smallest R on stored circuits where the argument needs more than the output gates. -> one-not/research/open/F1_bottom_small_R.md

## Refuted / dead

- Peeling (put payers back one at a time, each step costing at most 1 component in total): false at 63 BottomPay instances n <= 9 (slack 2) (F1 s4).

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
- F1 (Fable): BottomPay not proved. BottomPay at (Q, D) iff for every set J of payers Σ_{w DD} (c_w(J) − 1) ≤ |E ∖ J| (Lemma D, paper; necessity checked `Open/PHC.lean::deletion_of_forestPay`, `card_ge_of_forestPay`). Tested n ≤ 9 every state: 0 failures, every tight block splits one DD set; gates of top useful for a DD set exist at 4,444 states, rank without top never short. -> `one-not/research/open/F1_phc.md`, `F1_phc_tight.py`
- All Open/ files are under `one-not/lean/PEqualNP/W951/`, namespace `PEqualNP.Outside.L_meta_951_aux.F2Transfer`; build `cd one-not/lean && lake build PEqualNP.W951.Open.<File>`; no sorry.
- DONE A15 (was OPEN): `mixedCount_of_ddAbsorb`. The missing Lean link, which BOARD.md marks paper-only. From `DDAbsorb` (Open/DDAbsorb.lean) and the no-DD count `mslack_nonneg_of_noDD` (Open/F2TransferRun.lean), prove `0 ≤ MixedSlack.mslack gates S Q D` at every mixed state, under the same hypotheses (one-NOT correct circuit, pairwise |S a ∩ S b| ≤ 1, `Disjoint Q D`, an `out` wire per set). Then connect it to `MixedStepNeg` via `mixedStepNeg_iff` (Open/MixedStepNegIff.lean), and from there to `no_minCE_of_MixedStepNeg`. Paper: A7_dd_absorption.md, A4_f2_transfer.md. If the hypotheses do not match (for example the per-set `out` wire, which `MinCE` may not supply), state exactly which bridge is missing. -> one-not/lean/PEqualNP/W951/Open/MixedCount.lean
- A15: `mixedCount_of_ddAbsorb` (DDAbsorb at (Q,D) -> 0 <= mslack), `mixedStepNeg_of_ddAbsorb`, `no_minCE_of_ddAbsorb`; MinCE supplies hS, hg, hU and per-set hev, so hypotheses match. Axioms: propext, Classical.choice, Quot.sound. Bridge still missing: the no-NOT-gate case (DDAt needs an index p). -> `Open/MixedCount.lean`
- DECIDED A16 (provenance: the file one-not/lean/PEqualNP/W951/Open/MixedCountMono.lean landed inside commit 3eb9384, titled "philosophy: ..."): `mixedCount_mono` (MinCE with no NOT gate gives `MixedCount gates S`; exactly the `hmono` of `mixedStepNeg_of_ddAbsorb`) and `no_minCE_of_ddAbsorb_mono` (no_minCE from DDAbsorb alone). Monotone overlap is impossible by `mono_val`, so no DD set. Axioms: propext, Classical.choice, Quot.sound. -> `Open/MixedCountMono.lean`
- OPEN (Sonnet): `DDAbsorb gates p S Q D` for every `MinCE S gates out`, NOT gate p, disjoint Q D (i.e. hypothesis `hD` of `mixedStepNeg_of_ddAbsorb`; reduces to LightAbsorb via `ddAbsorb_of_lightAbsorb`) -> one-not/lean/PEqualNP/W951/Open/DDAbsorbMinCE.lean
- DECIDED S1: `PaymentHall` (disjoint per-set forests of size need_w, picked pairs acyclic), `card_ge_of_paymentHall` (sum need <= |E|), `bottomPay_of_paymentHall` (BottomPay as the instance at 1_Q: heavy atoms joined as class none, light singletons). States PHC only; not proved. Axioms: propext, Classical.choice, Quot.sound. -> `Open/PaymentHall.lean`
