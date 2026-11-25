# Task: open-one-not

- **Statement:** The general case of the one-NOT theorem: no smallest counterexample (`no_minCE`).
- **Seats:**
  - A1 (Opus): paper proof attempt of the mixed step at states of negative slack, the one local statement no circuit has broken
  - A2 (Sonnet): mixed slack as a Lean definition in the project's terms, so the missing arrow can be stated
  - A3 (Sonnet): search for a counterexample to the mixed step and to the step under no gate-saving rewiring, on irreducible circuits with a read NOT gate
- **Done when:** a checked theorem, a counterexample checked twice, or the exact missing lemma written down.

## Current target

- **F2-transfer** (from A1): in a minimal counterexample, for each restriction (Q, D) the witness count |F2'| is at least base'. Minimality only gives gates' ≥ base', and |F2'| ≤ gates', so it points the wrong way. The proof must use the one-NOT hypothesis: without it the step fails (146 of 248 negative states at t = 4).
- `MixedStepNeg` is **equivalent** to the full count (checked, `MixedStepNegIff.lean`). It is a restatement, not a reduction. Do not attack it as a local lemma.
- Seats now: A3 (Sonnet, search, running), A4 (Opus): F2-transfer under one NOT gate, A5 (Sonnet): test F2-transfer at t = 1 on every stored instance and find where the NOT gate is used.

## Lines (TAKEN / DECIDED only)

- A2 DONE: Open/MixedSlack.lean defines mslack and MixedStepNeg (Prop) and proves MixedStepNeg -> no_minCE; the arrow itself is unproved.
- 2026-11-25 A1 (Opus) DECIDED: mixed step at negative states = the count at every mixed state (checked, Open/MixedStepNegIff.lean); fails at t=4 only at negative states; obstacle = F2-transfer (minimality gives gates' >= base', step needs |F2'| >= base'). Note: one-not/research/open/A1_mixed_step.md
- 2026-11-25 A4 (Opus) TAKEN: F2-transfer under one NOT gate (where the NOT gate enters under restriction; attack on stored instances first). Note will be one-not/research/open/A4_f2_transfer.md
- 2026-11-25 A5 (Sonnet) TAKEN: test F2-transfer at t = 1 on every stored one-NOT instance and random irreducible one-NOT circuits; record NOT alive/killed vs gates' - |F2'|. Files: one-not/research/open/A5_transfer_t1.py, A5_transfer_t1.md
- 2026-11-25 A5 (Sonnet) DECIDED: F2-transfer |F2'| >= base' holds at every restriction (1,353,627 with base' > 0) of 3,263 one-NOT circuits, n 4..10, 0 failures (tested, checked twice); tight in both NOT-alive and NOT-killed states, so no NOT-use shows up in the data. Note: one-not/research/open/A5_transfer_t1.md
- A3 (2026-11-25): mixed-step search on irreducible read-NOT circuits, no counterexample, 0 negative-slack states reached; see one-not/research/open/A3_mixed_search.md
- 2026-11-25 A4 (Opus) DECIDED: F2 count holds at every mixed state with no DD set (paper; sign/overlap/witness/GoodT lemmas checked in Open/F2Transfer.lean); NOT gate enters only via DD sets (h=1 at Zof(S_w u D), h=0 at some unit atom); F2-transfer at (empty,empty) is no_minCE itself and MinCE always has a DD set there, so the open obstacle is DD-absorption (tested: 0 failures at 60,317 DD states). Note one-not/research/open/A4_f2_transfer.md
- OPEN (Sonnet): unit-form merges are OR gates in F2Mix. In `one-not/lean/PEqualNP/W951/Open/F2Transfer.lean` (namespace `…L_meta_951_aux.F2Transfer`), state and prove: for a one-NOT gate list (hg, hU, hN at p), a set `w` alive at `Q` (`Disjoint Q (S w ∪ D)`) with `¬ DDAt gates p S Q D w`, the merge set of the `merge_runT` run on the test system `(Zof (S w ∪ D), fun u => upPt (canonPt Q) u, S w \ D)` has card ≥ `(S w \ D).card - 1` and is a subset of `MixedSlack.F2Mix gates S Q D`. Model on `mergeSet_or` / `mergeSet_card_ge` / `mergeSet_subset_F2` (MergeFrac.lean, F2Desc.lean), using `goodT_of_noDD`, `unit_testSystem`, `F2WitMix_of_unit_noDD`. -> one-not/lean/PEqualNP/W951/Open/F2TransferRun.lean
- OPEN (Sonnet): no-DD mixed count. Using the line above and `overlap_needs_DD` (merge sets of two non-DD sets are disjoint), prove: one-NOT correct circuit with pairwise |S a ∩ S b| ≤ 1, `Disjoint Q D`, and `∀ w ∈ aliveSets S Q, ¬ DDAt gates p S Q D w` ⇒ `0 ≤ MixedSlack.mslack gates S Q D` (sets with `(S w \ D).card ≤ 1` contribute 0 to `baseDQ`). Paper proof: one-not/research/open/A4_f2_transfer.md §2. -> one-not/lean/PEqualNP/W951/Open/F2TransferRun.lean
- OPEN (Opus, not Sonnet): DD-absorption. At every mixed state (Q, D) of a one-NOT correct circuit, |F2Mix(Q,D) \ ∪_{w alive, not DDAt} M_w| ≥ Σ_{w DDAt} (|S_w \ D| − 1), M_w = unit-form merge set. Tested 0 failures at 60,317 DD states (A4_unit_merges.py --all). This plus the no-DD count is MixedCount, hence no_minCE. -> one-not/research/open/
