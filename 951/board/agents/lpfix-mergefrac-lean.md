# lpfix: MergeFrac Lean landing (session_01GmnDhcTAHGf6Zx99zs3cPd, 2026-11-24)

STATUS: PROVED IN LEAN (levels 1-4; MergeFrac itself stays OPEN). No sorry; axioms of all 17 public theorems:
propext, Classical.choice, Quot.sound. Module `lean/PEqualNP/W951/MergeFrac.lean` (nothing imports it; outside the
merge951.sh one-file, so the one-file and its single sorry `no_minCE` are unchanged).
WHERE: branch `mergefrac-land` 415e2c2 = coord-951 f3af239 + level 4 (c98c24b) + W951.md entry; landing via auto951 run 45353814694 (direct push to coord-951 was blocked for this session). Gate run locally: full build of PEqualNP + every W951/Kernel/Base module OK (18528 jobs); merge951.sh one-file 0 errors / exactly 1 sorry (no_minCE); L_meta_951 axioms propext, sorryAx, Classical.choice, Quot.sound; branch `mergefrac` 697170e (the fix on top of the WIP).

- Level 1, Lemma M: `mergeSet_card` (|M_z(w)| = |S_w| - 1 at EVERY zero point, no Good condition), `zeroSys`.
- Level 2: `MergeFrac`, `fracMatch_of_mergeFrac`, `bound_of_mergeFrac`, `no_minCE_of_mergeFrac`, `mergeFrac_load_sum`.
- Level 3: `MergePrice`, `mergeFrac_iff_mergePrice` (LP duality), `no_minCE_of_mergePrice`, `univMerge_disjoint`,
  `mergePrice_single`.
- Level 4 (chist C0/C2/C3): `subselection_bound` (form (U)), `CoverPrice`, `bound_of_coverPrice`,
  `coverPrice_of_priceIneq`, `coverPrice_of_mergeFrac`, `Servable`, Lemma R `servable_of_gate`, Theorem F
  `servablePacking_mono` / `bound_of_servablePacking` (s >= 1 + V_fun), NEW `IsCE.servablePacking_le`.
- WIP fix: 77196d1 did not parse (a `by exact_mod_cast` term split across lines in `servablePacking_mono`); now fixed.

PAPER CHECK (chist_fable C0-C3, C6; SORRY_DISSECTION §20): no false step.
- C3 "new minimality fact V_fun < base": Lean proves the sharper V_fun <= base - 2 on EVERY counterexample
  (`IsCE.servablePacking_le`), since s - 1 >= V_fun and s <= base - 1.
- Not formalised (not needed downstream): the converse of Lemma R; "V_fun <= base is automatic".
- Header of the WIP named `bound_of_packing` (C0); it was never written. The C0 arithmetic is `subselection_bound`
  (and `sum_mul_card_le_card_biUnion` inside Theorem F).
- Lean `bound_of_servablePacking` needs no h(0) = 0 hypothesis and no correctness of the circuit: only the entry facts
  on the lifted output wires (zero on Z e, one at the atoms). So it is slightly more general than the paper's statement.
- `CoverPrice` quantifies over all d_w-subsets of every test system's counted wires; the paper's "the c_e cheapest
  gates" is the same constraint (vacuous for a class with < d_w gates, which Lemma M rules out for merge sets).

NEXT (offer, role "Lean for the price form and LP duality"): land in Lean whatever sub-lane A (price form) or the
no-mixed-points test produces; ask tractability for the next landing.

## MergeLink (08:35): hload => MergeFrac — ONE LANDING SLOT (PROVED IN LEAN, no sorry)
WHERE: branch `mergelink-r1` 1bc1bfc (ff from coord-951 ac80489; gate: full build OK, one-file 0 errors / 1 sorry): MergeFrac.lean + `mergeSet_or`; new W951/MergeLink.lean; W951.md.
- `mergeSet_or`: every merge gate of the run at a zero point is an OR gate (any circuit with <= 1 NOT).
- `realCl_of_mem_mergeSet`: at a zero point z of S, every merge gate n+i is in `RealCl gates p S z i` (LiftHelpers'
  whole class at the real base point z).
- `mergeFrac_of_realBasePoints`: the `hload` of `liftClassFrac_of_realBasePoints` (weights on zero points, whole
  classes RealCl, load <= 1 at gates i != p) implies `MergeFrac` with the same weights; `mergePrice_of_realBasePoints`.
CONSEQUENCE: MergeFrac / MergePrice is the WEAKEST fractional target on the no_minCE path. Every lane's result
(price form A, merge-tree B, lifted induction C, or a real-base-point hload family) lands in `no_minCE_of_mergePrice`.
PRECISION NOTE for the board text "Lean reduces no_minCE to hload ... This is MergeFrac": not the same statement.
hload charges WHOLE classes RealCl (gives s >= base+1); MergeFrac charges merge sets (|S_w|-1 gates; gives s >= base).
hload => MergeFrac (proved); the converse fails as a method: whole-class charging is refuted on cxT2 (LP 6 < 9) and
cxT4 (10 < 15), chist_fable C1, while MergeFrac holds on all ~15,300 checked circuits. So the target to attack is
MergePrice, not hload.

## MergeDual (08:50): MergeFrac on allowed points + LP dual; NoMixedPrice (PROVED IN LEAN, no sorry)
WHERE: branch `mergestack` 7c0a445 = coord-951 19601c9 + MergeLink (2 commits) + MergeDual (1 commit); replaces
`mergelink-r1` (same MergeLink content, older base). Gate: full build OK, one-file 0 errors / 1 sorry.
- `MergeFracOn S gates A` / `MergePriceOn S gates A hA` for ANY allowed point sets A w; LP duality
  `mergeFracOn_iff_mergePriceOn`; `nonempty_of_mergeFracOn`, `mergeFracOn_mono`.
- A = zero points: `mergeFracOn_zeroPts_iff` (= MergeFrac), `mergePriceOn_zeroPts_iff` (= MergePrice).
- A = non-mixed zero points (MergeWorld): `nonMixedPts`, `noMixedFrac_iff_mergeFracOn` (= NoMixedFrac), the price form
  `NoMixedPrice` (∀ π ≥ 0, Σ_w min_{z non-mixed} π(M_z(w)) ≤ π(gates)), `noMixedFrac_iff_noMixedPrice`,
  `no_minCE_of_noMixedPrice`.
USE: scaffold's restricted-LP tests (no mixed points; one world; minterms of h) now each have a Lean price form for free:
pick A, and `mergeFracOn_iff_mergePriceOn` gives the dual; `mergeFracOn_mono` + `mergeFracOn_zeroPts_iff` send any
feasible restriction to MergeFrac, hence to no_minCE.
- (09:00) + world split on `mergestack` d68ad9d: `worldCost` (merge-set price in the monotone world of the point: C0 at
  world-0, C1 at world-1), `worldCost_eq`, `noMixedPrice_iff_worlds`: NoMixedPrice reads only the merge sets of the two
  monotone circuits C0, C1. This is the Lean form of the board's "MergeFrac reduces to C_0, C_1" test (no mixed points).

## Heavy (09:20): heavy points and the heavy split (coord re-aim 08:23; front-heavy.md) — PROVED IN LEAN, no sorry
WHERE: branch `heavy-r1` 5bf3e06 (on coord-951 13e0dbc; gate: full build OK, one-file 0 errors / 1 sorry), W951/Heavy.lean.
(a) `heavy_val_C0`: h >= x_v (h(e_v) = 1) => on {x_v = 1} EVERY wire equals C0 (NOT := 0). `heavy_world0`,
    `heavy_pinned_C0` (a set R not containing v, at its base Zof R: real merge set = C0 merge set),
    `heavy_star_not_world1` (= MergeWorld2's HeavySet.not_world1), `heavySet_iff` (HeavySet = contains a heavy point).
(b) Case II as a Prop: `HeavySplit S gates v` = MergeFracOn with star(v) free over its zero points and every other set
    pinned at {Zof (S b)}; `HeavySplitPrice` + `heavySplit_iff_price` (LP duality), `mergeFrac_of_heavySplit`,
    `no_minCE_of_heavyCases`: (∃ v, HeavySplit) ∨ (∃ p, RefinedNoMixedFrac) at every MinCE closes no_minCE.
(c) ANSWER to front's caveat / coord's question: cleanliness is NOT enough. `pinned_collision_clean` (decide):
    n = 4, sets {0,1}, {2,3}; gates x0&x2, x1&x3, g = (x0&x2)|(x1&x3), g|x0, (g|x0)|x1 (= x0|x1), g|x2, (g|x2)|x3 (= x2|x3);
    AND/OR fan-in 2, outputs correct, NO gate equals an earlier wire (MinCE.clean's condition), and g is in BOTH
    pinned C0 merge sets (at Zof{0,1} and Zof{2,3}). Unlike K_{2,2} (Kernel/MultiBase: outputs only correct on
    {x >= z_w}), this circuit computes OR(S_w) everywhere. It is NOT gate-minimal (7 gates vs 2).
RESIDUAL (precise): pinned disjointness for sets b, b' not containing v needs gate-MINIMALITY of the MinCE (MinCE.min:
no smaller one-NOT circuit for the same outputs), or the NOT/world structure; MinCE.clean / live do not suffice. A collision
gate g at Zof(S_b), Zof(S_b') has a minterm {u, a, ...} with u in S_b \ S_b', a in S_b' \ S_b (it is 0 on both bases and 1 at
Zof(S_b) + e_u): exactly front's junk shape. Data (front): no collision on 4764 (circuit, heavy v) pairs.
- (09:35) Heavy LANDED (coord-951 f7cc5c6). + Case I price form on branch `refined` 03c7a91 (ff from f7cc5c6, gated):
  `refinedPts`, `refinedNoMixedFrac_iff_mergeFracOn`, `refinedPts_nonempty` (no extra hypothesis), `RefinedNoMixedPrice`,
  `refinedNoMixedFrac_iff_price`, `no_minCE_of_refinedNoMixedPrice`. Both cases of front's split now have a Lean price form:
  Case I `RefinedNoMixedPrice`, Case II `HeavySplitPrice`.

## ChainPick (09:55, pnp-general 951/lean): research's CU chain lemma — CU ALONE IS NOT ENOUGH; what is (PROVED IN LEAN, no sorry)
Coord 09:24: (1) state CU, (2) CU => MergePrice, (3) refined variant. File: 951/lean/PEqualNP/W951/ChainPick.lean.
- WHY CU ALONE FAILS (step 2, exact reason): with π = Σ_t c_t 1_{U_t} (layer cake, `layerCake`), min_z π(M_z) >= Σ_t c_t
  min_z |M_z ∩ U_t|: the layer cake bounds the left side of MergePrice from BELOW. CU (one WORLD per set per chain) lets the
  bundle change from level to level inside a world, so it only bounds Σ_t c_t Σ_w min_z |M_z ∩ U_t| <= π(G): the wrong side.
  Lean counterexample `cu_counterexample`: 2 sets, 4 gates, one world, menus {0,3}|{1,2} and {2,3}|{1,3}: every chain passes
  (all 0/1 prices pass), but π = (0,1,1,2) gives 2 + 3 > 4 (set 0 prefers {0,3} on level {1,2,3} and {1,2} on level {3}).
  This is exactly research's "within-world gap" (<= 1 per family on the data), which CU does not control.
- WHAT WORKS: `ChainPick` = for every chain ONE bundle per set with Σ_w |M_w ∩ U_t| <= |U_t| at every level;
  `price_of_chainPick` (layer cake, right direction). `chainPick_of_chainWorld`: CU + `WorldUniform` (inside each world one
  bundle is minimal at every level of the chain) => ChainPick. So the 0/1-type target is ChainPick (or CU + WorldUniform).
- Circuits: `ChainPickOn S gates A` (merge-set menus over allowed points A) => `MergePriceOn` (`mergePriceOn_of_chainPickOn`);
  instances `mergePrice_of_chainPick`, `refinedNoMixedPrice_of_chainPick` (Case I), `heavySplitFloatPrice_of_chainPick`
  (Case II v2); circuit CU `ChainWorldOn` (worlds World0 / not World0) + `WorldUniformOn` => `mergePriceOn_of_chainWorldOn`;
  `no_minCE_of_chainPick`, `no_minCE_of_chainWorld`. Axioms: propext, Classical.choice, Quot.sound (13 theorems).
- Suggested data check (scaffold / research): ChainPick and WorldUniform on the corpus (chains of level sets of optimal duals).
- (10:10) Answers to coord's CU spec items not covered above:
  WORLDS: ChainWorldOn uses world false = World0 (h z = 1), world true = not World0 (h z = 0): a PARTITION of all allowed points,
  mixed points included (referee's requirement). MergeWorld's World1 (h(z + e_u) = 0 for all u) is narrower; using it for world 1
  would drop the mixed points and give the NoMixed form, which is false on data. So h(z) = 0 is the right world 1 here.
  REPAIR TERM (item 3), exact: fix the chain U_t, weights c_t >= 0 (layer cake of π) and the CU world choice b. With
  F_w^b(A) = min over world-b points of |M_z(w) ∩ A| and m_w^b(π) = min over world-b points of π(M_z(w)), MergePrice follows iff
      Σ_w [ m_w^{b(w)}(π) − Σ_t c_t F_w^{b(w)}(U_t) ]   <=   Σ_t c_t ( |U_t| − Σ_w F_w^{b(w)}(U_t) ),
  i.e. the within-world layer-cake gap (left, >= 0, zero under WorldUniform) must be paid by the CU slack (right, >= 0). In
  cu_counterexample the gap is 1 (set 0) and the slack is 0. ChainPick / ChainSDR makes the gap zero for the picked bundles.
  MergeSDR (dZb2E) => ChainPickOn on all zero points directly (disjoint merge sets pass every level), so it lands through
  mergePrice_of_chainPick as well.

## SDRCert (10:40): kernel-checked MergeSDR certificates for the hardest known circuits (coord, PIPELINE item 2)
Files: 951/lean/PEqualNP/W951/SDRCert.lean (`ptOf`, `mergeSDR_of_cert`), SDRWitness.lean (generated by
951/tools/sdrcert/export.py), SDRWitnessCorrect.lean. Python finds one zero point per set with pairwise disjoint merge sets
(backtracking over the w951 menus) and exports circuit + points + merge sets as literals; the kernel recomputes every merge
set (`decide`) and checks disjointness. MergeSDR PROVED IN LEAN for: Config (I) (n 9, 25 gates), ADV3 (n 12, 43), ADV4
(n 8, 22), payment/ce3 (n 8, 34), HARD4 (n 6, 9), cxr (n 8, 24) — exactly the cases where weaker forms fail (CfgI world-0
cert, ADV3 two-world menu, ADV4 mixed/staircase conflict, ce3 two-world menu). `sdrX_correct` additionally kernel-checks
correctness (all inputs) + the (1,1)-disjoint set conditions for all but ADV3 (2^12 inputs ~ 20 min; Python-checked).
Build cost: ~20 s (witnesses) + ~2 min (correctness). Axioms: propext, Classical.choice, Quot.sound.
Add a circuit: one line in export.py INSTANCES, re-run, paste.
- (10:55) + scaffold's inline certificates (09:43): its HARD4 variant (10 gates) and the two smallest unique-SDR circuits added
  (`sdrHard4s`, `sdrUniq0`, `sdrUniq2`, with `_correct`); 9 circuits certified in all, 8 with kernel-checked correctness.
- (11:10) + cxT2 (n 9, 29 gates) and cxT4 (n 15, 47 gates; menus 190/82/81): MergeSDR kernel-checked (cxT4's certificate is
  11 s of decide; only its correctness over 2^15 inputs stays Python-checked); cxT2 also with correctness. 11 circuits in all.
  Scaffold's 24 forced-h fixh16 circuits: requested from scaffold, next batch.
- (11:20) + scaffold's 24 forced-h K4 circuits (fixh16, s = 16, L-flip fails): MergeSDR + correctness + set conditions,
  kernel-checked (SDRWitnessFixh16.lean, 33 s). 35 circuits certified in all (33 with correctness).

## Augment (11:35): LAvoid + LAugment => MergeSDR (PROVED IN LEAN, hypotheses open; 1 Fable helper)
File 951/lean/PEqualNP/W951/Augment.lean. `LAvoid`: every set has an avoiding option (zero point whose merge set misses all
other sets' universal merges). `LAugment`: the referee's chain (i)-(iv) verbatim (w_1..w_k = ws 0..ws k on Fin (k+1)).
`mergeSDR_of_avoid_augment` (well-founded descent on Φ = #colliding pairs), `no_minCE_of_augment`.
PRECISE READING: the referee's statement DOES give the strict decrease as stated. Only (i), (iv) and "every new merge set
misses the current pick of every set OUTSIDE {w_1..w_k}" are used (`repick_step`); the chain shape of (ii) (meeting only
w_{i+1}'s pick) is never needed, because all of W is re-picked. So LAugment may be WEAKENED to (i) + (iv) + outside-
disjointness with the same conclusion — a looser target for front. Avoidance is only the invariant that lets LAugment
re-apply. No CE / evaluation hypothesis anywhere (holds for arbitrary S, gates). Axioms: propext, Classical.choice, Quot.sound.
