# scaffold findings, 2026-11-24 (paused 14:20 per owner)

All runs stopped. Data and scripts are in scaffold's scratchpad (f15/), listed at the end. Nothing in this list is a proof
unless marked; "tested" means exhaustive or sampled computation as stated.

## PureSDR / MergeSDR (morning target)
- MergeSDR and PureSDR: 0 failures on 75,619 corpus records (62,463 distinct one-NOT circuits, n <= 12) + 2,224 ladder circuits.
- L-avoid PROVED (fableA/PROOF.md; Lean avoidOpt_zero / disjoint_univMergeSet).
- LAugment_2 / L-descent2 FALSE in general: selector-path counterexample, k* = min(c, L-c); essential clean instance n=5, s=50, k*=3
  (fableB/PROOF.md). Needs a size hypothesis.
- Lemma K (class count) refereed CORRECT; Lean coord-951 19601c9.

## Size ladder (PG(2,3) v=13, AG(2,4) v=16)
- 2,159 + 65 essential circuits, slack 4..8. PureSDR 100%, k* <= 1, heavy-star CLASS/MERGE hold. No growth of k* with v.
- 12 certificates kernel-checked by machines-Lean (W951/PureSDRWitnessLadder.lean, ca16c38); 10 Fano essential circuits landed
  (951/tools/sdrcert/fano_ess_ladder.json).
- Unique pure SDR on 173/2,159 PG(2,3) and 4/65 AG(2,4); forcing depth <= 1 (unit propagation suffices on all 177).
- I1 class per set unique on 28,066/28,067 sets; the exception (pg13:603) comes from a 2-point minterm in top_w.
- CANON (choice-free type-A rule) FALSE as Q1: type-A sets whose I1 and I0 classes differ (smallest essential: named.jsonl:12, n=5).
- Big-picture page: mu/SYNTHESIS_ladder.md (landed as SYNTHESIS §7 by coord).

## MU (pure classes) and point deletion
- MU = |U_pure| - base >= 0 on all 62,463 + 2,224 circuits; ladder MU in {0,1,2} while slack 4..8 (slack = NOT gadget outside U).
- Deletion x_v := 0: MU = MU'_v + (lost - new - deg) exactly; every PG(2,3) circuit has >= 11/13 good points; all 60 bad points are
  non-hub; deleting a heavy point is always good.
- MU (pure) is FALSE in general: cxMU_dd family (MU_pure = -1) — front's barrier.

## MUL / LiftSDR (lifted classes, official target since 12:27)
- Pure classes and real merge sets are lifted classes (checked on 400 random circuits, 0 exceptions), so MUL >= MU >= 0 and LiftSDR
  holds on the whole corpus + ladder.
- EXACT liftMenu (liftmenu.py) on the barriers: cxMU_dd +14, cxMU_clean2 +10, cxMU_clean2_DD +12, cx44_1_junk +17, pasch_s14 +3,
  tri_all_5593 +3, STAR4 +8, JUNK n=5 +2, clean selector path +12; LiftSDR exists on all.
- Hunt (1 NOT): margin 0 reached only with an INESSENTIAL NOT (s=90, slack 84); best with essential NOT = +4. No counterexample.
- Rung 2 (2 NOTs, exact 4-world menus): 2-selector path +54, Fano 2-hub circuits +49/+51; 2-NOT hunt best +24 (weak search: walk
  only grows). Lifted menus grow with worlds; nothing threatens MUL.

## F2 count and STEP (coord / owner)
- Fano corpus: 80,198 distinct correct one-NOT circuits (15,542 essential, slack 2..26), reproducible by fano_corpus.py
  (sha256 of sorted [gates,outs] keys 64ca2c15...923d). F2 MU and STEP at EVERY Q (128 each, 10,265,344 cases): 0 failures.
- SAT Fano (lgen, exact size): essential at s=18 (10) and s=19 (14) = slack 4-5; plain at s=17 (42); none found at s=15,16 in 10 min.
  All 66: F2 at every Q, 0 failures.
- Ladder: PG(2,3)/AG(2,4) at Q = ∅ + 3 random Q: 0 failures, >= 7 good points.
- FANO-FORMULA tight at every Q with equality at every point; clean selector path, JUNK n=5, STAR4: all Q pass.

## Global count k=3 (real merge sets)
- S(K) = Σ_w min_z |M_z(w) ∩ K| <= 3 for every tested triple: 4,000 corpus circuits (504k triples), 540 PG(2,3) (1.62M sampled),
  2,005 Fano (915k). Max ratio exactly 1.

## R1-R6 normal form (desktop Coord c1, partial)
- selector43: R2, R3, R4, R5, R6; selector50 (clean): R2, R3, R6; cxMU_dd: R6 only; FANO-FORMULA: R4 (unread NOT), R5.
  PAPPUS-JUNK, hard4@Q={1}: not run (no JSON).

## Files (scaffold scratchpad, f15/)
- lift/liftmenu.py, lift/lift_hunt.py, fanoc/fano_corpus.py, fanoc/f2check.py (all four sent inline, byte-identical).
- fanoc/corpus_rw.jsonl (47 MB), fanoc/sat_ess.jsonl, fanoc/sat_plain.jsonl; mu/ (ladder MU, per-point deletion); canon/ (CANON,
  EXT, MU full pass); gc/ (k=3 count); ladder/ (pg13, ag16 corpora, certs); lift/barriers.json, star4.json.
