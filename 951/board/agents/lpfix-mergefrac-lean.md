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
- (11:50) LAugmentLoose landed (coord 10:13): the weakest form, (i) + (iv) + "every new merge set misses the current pick
  of every set outside the chain"; `lAugmentLoose_of_lAugment`, `no_minCE_of_augmentLoose`. OFFICIAL OPEN TARGET:
  LAvoid ∧ LAugmentLoose at every MinCE. The referee's LAugment and its theorems are kept (statements unchanged) as instances.
- (12:05) REFEREE'S CATCH, now a Lean theorem: `mergeSDR_iff_avoid_augmentLoose` — the unbounded loose form IS MergeSDR (SDR
  points are avoiding options, `avoidOpt_of_sdr`; re-pick all sets at once, `lAugmentLoose_of_mergeSDR`). OFFICIAL OPEN TARGET:
  `LAvoid ∧ LAugmentK K` at every MinCE (re-picked groups of at most K sets), `no_minCE_of_augmentK`, chain
  LAugmentK K → LAugmentLoose → MergeSDR → no_minCE; `lAugmentK_mono`. Data (scaffold via coord, not checked here): K = 2
  suffices on all 75,619 circuits; K = 1 in 100,116 of 100,174 collision states.
- (12:20) PROOF_PLAN rule 4 in Lean: `LAugmentReach K` = some avoiding start z0 such that every state reachable from z0 by
  improving moves (≤ K sets re-picked, strictly fewer colliding pairs) that still collides has a further such move.
  `mergeSDR_of_augmentReach`, `no_minCE_of_augmentReach`, and `lAugmentReach_of_avoid_augmentK` (LAvoid ∧ LAugmentK K ⇒
  LAugmentReach K): the reachable form is a WEAKER sufficient target, so a canonical start (PROOF_PLAN §3) can be used.
- (10:45 UTC) LAvoid PROVED (scaffold's lemma). Coord landed the z = 0 case first (2d66d15: `avoidOpt_zero`, `lAvoid`,
  `no_minCE_of_augmentK_only`); my parallel copy dropped. Added scaffold's FULL form: `disjoint_univMergeSet` — for w ≠ w' and
  z vanishing on S_w ∪ S_w', M_z(w) ∩ U(w') = ∅ (only (1,1)-disjointness: no Lemma M, NOT gate or correctness) — and
  `avoidOpt_of_hit`: a zero point z of S_w is an avoiding option once M_z(w) misses U(w') for every other set S_w' that z
  HITS; sets z vanishes on are free. Use: any LAugment step that re-picks at a point z only has to check the sets z hits.
  OFFICIAL OPEN TARGET: `LAugmentK K` alone. Axioms: propext, Classical.choice, Quot.sound.
- (11:05 UTC) CanonOneNot.lean (coord 10:41): one-NOT wrapper for CanonClass. K_1(w) = `K1 gates p (S w)`, K_0(w; m) =
  `K0 gates p (S w) m`, Finsets of real wires (`realWire`). `card_K1`: NOT gate 1 at top_w (h(top_w) = 0) ⇒ d_w ≤ |K_1(w)|
  (no heavy-point condition, referee 10:39). `card_K0`: m ∩ S_w = ∅ and NOT gate 0 at m (h(m) = 1) ⇒ d_w ≤ |K_0(w; m)|.
  `disjoint_K1` (W1), `disjoint_K0` (W0, one side of the minterm condition suffices), `disjoint_K0_K1` (NEW, D across
  worlds: K_0(w; m) ∩ K_1(w') = ∅ once m ∩ S_w' = ∅, since the world-0 atoms (m + e_u, 0) lie below (top_w', 1)),
  `cross_K1_K0` (X: NOT-dependent at some e_u, u ∈ S_w). So a cross-world collision K_1(w) ∩ K_0(w'; m') needs
  m' ∩ S_w ≠ ∅: case (b) of PROOF_PLAN_SUGGESTIONS §2 is only minterms that meet the other set. Axioms: propext,
  Classical.choice, Quot.sound.
- (11:20 UTC) PureSDR reduction CHECKED (coord 10:42): `PureSDR.lean`, `no_minCE_of_pureSDR`. Classes are the union-find merge
  sets (`runMT`, = `merges` of kill_tests/ext.py) in the lift: I1 at (Z, 1) with atoms (e_u, 1), I0 at (top_w, 0) with atoms
  (m_u ∪ {u}, 0). Validity is WEAKER than the data's: I1 needs only Z ∩ S_w = ∅ and h(Z) = 0 (Z need not be maximal), I0 only
  m_u ∩ S_w ⊆ {u} and h(m_u) = 1 (m_u need not be a minterm; h(top_w) = 1 not needed). Sizes ≥ d_w by `merge_countT` in the
  lift (`card_pureI1`, `card_pureI0`), all classes inside the gates.length - 1 lifted gates, so a PureSDR gives
  ∑ d_w ≤ gates.length - 1 < gates.length (`bound_of_pureSDR`), against `hlt`. So PureSDR at every MinCE closes 951.
  Axioms: propext, Classical.choice, Quot.sound.
- (11:30 UTC) Disjointness for the PureSDR merge sets themselves (not via orClz, which needs OR gates): `runMT_disjoint_of_le`
  (D for any monotone list), `disjoint_pureI1_pureI1` (W1: Z' true at one of any two points of S_w), `disjoint_pureI0_pureI0`
  (W0: one of m_u ∪ {u}, m_v ∪ {v} avoids S_w'), `disjoint_pureI0_pureI1` (D across worlds: Z' true on one of them), with
  |S_w ∩ S_w'| ≤ 1 corollaries `disjoint_pureI1_top`, `disjoint_pureI0_avoid`, `disjoint_pureI0_top`. What is left of PureSDR
  after these: I1 pairs whose Z' vanishes off S_w' at two points of S_w; I0 pairs whose points m_u meet S_w'; I1 ∩ I0 pairs
  (world-1 class vs world-0 class: never D-disjoint from the world-1 side, since its atoms have y = 1).
- (11:45 UTC) PureSDR CERTIFICATES: `PureSDRWitness.lean` (36 kernel-checked PureSDRs: the 12 MergeSDR-certificate circuits
  incl. cxT2, cxe3, ADV3, cxT4, plus the 24 fixh16), by `tools/sdrcert/pure_export.py` (Python finds, Lean checks; ~40 s).
  The Lean `pureCls` (runMT in the lift) equals kill_tests' `merges` on every chosen class: the Lean definitions match the
  data. Pure menus are small: 1-10 distinct classes per set (cxT4: 2/2/2 against 190/82/81 plain merge sets).
- (12:00 UTC) PureHall.lean: the board's TRANSFER line is a Lean theorem. `pureSDR_iff_hall`: on GRAPH systems (all
  |S_w| = 2) every valid pure class is exactly one gate (`card_pureCls_graph`) and PureSDR ⇔ Hall's condition on the pure
  menus (`pureMenu` = union of all valid classes of a set). `no_graph_minCE_of_hall`: Hall on the pure menus of every
  graph-system MinCE ⇒ no MinCE is a graph system — the exact Lean target of front's heredity lane. For any system,
  `hall_of_pureSDR` (necessary: ∑_{w∈F} d_w ≤ |⋃ menus|) and `card_pureCls_le` (classes have EXACTLY d_w merges).
- (12:35 UTC) HEREDITY of pure menus (coord 11:08; front's graph lane), `PureHeredity.lean`. Natural statement
  (x_v := 0 off V = V(F), NOT gate kept; restricted menu ⊆ original menu) is FALSE for the top-only I0: the restricted
  top is V \ S_w, a lower zero point, so earlier wires merge. Data (research/heredity/): 144 failing restricted I0 classes
  on the 26 graph systems (full Lean menus), 344 on all 63. Kernel-checked witness `heredity_top_fails` (fixh16_20,
  F = {S_1, S_2}, V = {0,2,3}, S_w = {0,3}, m_0 = {0,2}, m_3 = {2,3}): the restricted class is {h} (the NOT gate's input),
  h ∉ any one/zero class (C_0(h)(top_w) = 1, C_1(h)(e_0) = C_1(h)(e_3) = 0). FIX, in Lean: `PureOpt.zeroAt z m` (I0 at any
  zero point z ∌ S_w with m_u ⊆ z ∪ {u}; `card_pureI0At` ≥ d_w). Then `restrictedMenu_subset_pureMenu` and
  `restricted_deficient` (a Hall-deficient F stays deficient after restriction). PureSDR / pureMenu / pureSDR_iff_hall now
  include zeroAt (more options; all earlier data claims stay true). Gap NOT formalized: the restricted circuit is modelled
  by evaluating at points vanishing off V (= Kernel/W951Cube.val_restrictZero; its dead gates are constants and copies,
  at which a union-find run never merges).
- (12:50 UTC) I1 WIDENING (board: 'cTAHG widening PureValid'): `PureOpt.oneAt Z A`, atoms ({u} ∪ A_u, 1) with A_u ⊆ Z ∪ {u}
  (`card_pureI1At` ≥ d_w: the extra coordinates are 1 at the zero point, so GM applies). Heredity under the board integrator's
  x_O := 1 (where plain I1 fails, 1,160 of 18,210): `restrictedMenu1_subset_pureMenu`, `restricted1_deficient`. So with
  zeroAt (x := 0) and oneAt (x := 1) both restrictions keep restricted menus inside the original menus, and a Hall-deficient
  F stays deficient after either restriction. All PureSDR / PureHall theorems cover the four option kinds.
- (13:15 UTC) PureGP.lean (front A1-a's GP request): `no_minCE_of_liftSDR` for LIFTED TEST SYSTEMS (any zero point and any
  atoms in the lift with o_w(ζ) = 0, o_w(atom) = 1, atoms pairwise separated outside ζ) — contains GP and all four pure
  kinds (`liftSDR_of_pureSDR`). Key Lean step: `merge_countT'`, the union-find count with PAIRWISE-separated atoms.
  GP validity `gpLTS_valid` is front's exactly (u ∈ A_u not needed); Theorem U = `disjoint_gp`. Front's notes taken:
  no_graph_minCE_of_hall is vacuous (MinCE.has4); the cross-world D hypotheses (disjoint_pureI0_pureI1, CanonOneNot's
  disjoint_K0_K1) can never hold for valid options (h monotone) — true statements, but vacuous; Theorem U (world b ≤ b')
  is the usable cross-world criterion.
- (13:35 UTC) MU + gate-form heredity + STAR-SEP. `no_minCE_of_MU` (coord: MU = base ≤ |⋃ of all pure menus|; `mu_of_pureSDR`).
  `restricted_gate_deficient` / `restricted1_gate_deficient` (desktop Coord / research: the GATE form, any bound k).
  `PureStar.lean`: front A2's STAR-SEP as the hypothesis `StarSep` (no new sorry; gate rule), and its induction checked:
  `menuSDR_of_starSep`, `pureSDR_of_starSep`, `no_minCE_of_starSep`. So 951 now reduces in Lean to STAR-SEP (∀ MinCE, ∀ Q).
- (13:45 UTC) `no_minCE_of_MUL` (coord 12:01): MU over ALL valid lifted test systems (`liftMenu`), the weakest menu target;
  `mu_of_liftSDR`, `muL_of_mu`. Implication chain in Lean: STAR-SEP ⇒ PureSDR ⇒ {LiftSDR, MU} ⇒ MUL ⇒ no_minCE.
- (13:55 UTC) STAR-SEP HEAVY CASE checked (front A2's paper proof): `starSep_heavy` (h(Q ∪ {v}) = 1, h(D ∪ {u}) = 1 for star points
  u ≠ v ⇒ StarSep at Q with I0 star classes at top_w), `starSep_of_hQ` (h(Q) = 1 ⇒ StarSep). Open: light v, and heavy v with
  non-heavy star points (front's GAP).
- (14:10 UTC) PureFrac.lean (coord item 3; front A1's target): `PureFrac` ⇔ `PurePrice` (LP duality, items = gates of the menu
  union), `mu_of_purePrice` (constant price 1), `pureFrac_of_pureSDR`, `no_minCE_of_purePrice`, `no_minCE_of_pureFrac`.
  Lean chain now: StarSep ⇒ PureSDR ⇒ PureFrac ⇔ PurePrice ⇒ MU ⇒ MUL ⇒ no_minCE (and PureSDR ⇒ LiftSDR ⇒ MUL).
- (14:25 UTC) STAR-COUNT (front A2): `no_minCE_of_starCount` via `mu_of_starCount` (induction on the alive sets, U(Q ∪ v) ⊆ U(Q))
  and `starCount_of_starSep`. Open conjectures (front): HEAVY-COUNT (heavy v ⇒ STAR-COUNT; data 78,451/78,451) and LIGHT-COUNT.
- (14:45 UTC) L-LIFT checked (front A1): `mergeSet_eq_lift` — every real merge set M_z(w) is the class of the valid lifted test
  system ((z, ν z), atoms (z + e_u, ν(z + e_u))) (`realLTS_valid`), via `run_lift` (gate-for-gate transfer of the union-find
  run from the real circuit to its lift). Corollaries `liftSDR_of_mergeSDR`, `muL_of_mergeSDR`: the lifted targets (LiftSDR,
  MUL) are WEAKER than MergeSDR, so they survive front A1's cxMU_dd (where the pure lists fail).
- (15:00 UTC) PureMenu.lean (front A2): the STAR induction for ANY monotone sound menu system (`no_minCE_of_starSepG`,
  `no_minCE_of_starCountG`), and Menu2 = Menu1 ∪ lifted real merge sets (`menu2_mono`, `menu2_sound` via L-LIFT):
  `no_minCE_of_starSep2`, `no_minCE_of_starCount2`. Menu2 survives cxMU_dd (A2's rerun pending).
- (15:10 UTC) L-U_v (front A2): `menu2_U_zero` — every gate of U(Q) over Menu2 is 0 in C_0 at (Q, 0).
- (15:40 UTC) 2G-LIFT CHECKED (front A1, refereed): `twoGate_lift` — ∑_w min_z |M_z(w) ∩ {g, g'}| ≤ 2 under C(b) for every
  triple. The Lean proof follows front's §9: ceilings at (X_l, ν X_l) via the monotone lift, pigeonhole (no WLOG: base merges
  are never low at other ceilings), triangle, and the odd cycle with ONE cover of the merge gate valid for all three runs
  (mr_coverT over univ, so it does not depend on the set). Weaker hypotheses than the paper: correctness of the outputs and
  |S_w| ≥ 2 are not used.
- (16:00 UTC) F2Bridge.lean: lifted ⇒ real witnesses (`real_zero_of_lift`, `real_one_of_lift`) and the F2 exclusion
  (`real_one_of_C0`). G1 in F2 form follows for star edges {v, a} with h(top_va) = 1 (the I0 class at (top_va, 0) is then
  consistent); h(top_va) = 0 star edges = front's open bridge. F2 definition: coordinating with machines-Lean.
- (16:20 UTC) GraphHeavyF2.lean: G1 in F2-gain form (`gainF2_graphStar`, `gainF2_G1`) under h(top_va) = 1 for every star set
  (front A2's (F5)), on machines-Lean's F2 (F2Induct: F2Wit / F2 / GainF2). Stated for a chosen v (front: 'heavy v exists ⇒
  works' is refuted for F2). Open: h(top_va) = 0 star sets.
- (16:45 UTC) MinCERed.lean: the refereed MinCE reduction lemmas. R+ `MinCE.observable` CHECKED, plus R2 `no_dup`, R3 `no_var`,
  R5' `not_used`; R1 (`MinCE.no_const`, Peel) and R4 (`MinCE.live`) were already there. Machinery: constant substitution on
  out-edges (`subGates`, value congruence), `shrink_of_const`, `shrink_of_copy`. Note: in our gate model a NOT gate may read two
  wires (only the first counts), so R+ is stated for readers that are AND/OR gates or NOT gates reading the wire first; for an
  ignored second NOT input the substitution is a no-op and R+ would be false.
- (13:12 UTC) NotVarF2.lean: front A2's case h = x_a (the NOT gate reads an input) CHECKED: `muF2_of_notVar` (base ≤ |F2(∅)|,
  lifted SDR with zero (top, 1), atoms (e_u, [u ≠ a]); no minimality), `IsCE.false_of_notVar`, `MinCE.not_notVar`. Disjointness
  needs only |S_w ∩ S_w'| ≤ 1: if a ∈ S_w' the atoms of S_w meet S_w' in ≤ 1 point, else the atoms of S_w' meet S_w ∪ {a} in ≤ 1.
  (Clock note: the 16:20 / 16:45 labels above are off; commit e408ec8 is 13:05 UTC.)
- (13:16 UTC) CubeF2.lean: the relative form CHECKED. `baseDQ_le_F2_of_cubeLocal`: if on the cube x_Q = 1 the NOT gate is ¬x_a
  (a ∉ Q) or constant, then base(Q) ≤ |F2(Q)| (no minimality). `no_minCE_of_gainF2_or_cubeLocal`: the F2 induction now closes a
  branch at any Q where the NOT gate is local (literal or constant on the cube); only the non-local Q need a GainF2 step.
- (13:24 UTC) LW1 (CubeF2) and CERT-1c (ConeCert.lean) CHECKED. `baseDQ_le_F2_of_LW1`: front's LW1 in relative form is a third
  local closure. `gainF2_of_cert`: qg-d2's (D) ∧ (S) at v ⇒ GainF2 at v (cone merge sets = Lemma M over the masked cone, any zero
  points z_w ⊇ Q off S_w). `no_minCE_of_cert_or_local`: 951 follows once every Q with positive base in a MinCE is CubeLocal, LW1, or
  has a v ∉ Q with (D) and (S). Paper proofs of (D)/(S) plug in as the hypotheses `CertD` / `CertS`.
