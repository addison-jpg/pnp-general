# front-612: support-B (numerics for no_minCE angles 2 and 3)

Assigned by coord-951 08:00. Code: pequalnp-work mirror/laughing-mccarthy-ifdzly, research/front/no_minCE/supportB/ (0a22dfa).
harness.py imports coord-951 research/tools/w951 (not copied). A candidate = rule(c, prof) -> (ok, info); prof = per set with |S|>=4:
canonical system z = z_{S_w}, atoms z+e_u (R*), union-find merge gates M_w (systems.merges), 3rd+ merges M_w[2:].

## Corpora now (08:10)
fixh16_clean (3600, all |S| = 2), front-match w9/*.json, w951 test instances, f15 HARD4: 3656 correct one-NOT circuits,
but only 37 have a set with |S| >= 4 (85 such sets, all Good; 71 hard; 132 third+ merge gates). Waiting for scaffold's
data-corpora (ess/tri/q_all/q_and_q2t). Local regeneration via gen_q.py is blocked: lib/hallcheck.py needs chargeok_check, conedbl.

## Baseline facts (SAT/data, not Lean)
- B1 "3rd+ merge gates of different |S|>=4 sets are pairwise disjoint": FALSE on 14 of 37. Smallest: front-match w8b/cxr
  (s=24, n=8, gate 14 is a 3rd+ merge of sets 0 and 1). So a global charge of 3rd+ merges must split shared gates.
- B2 "3rd+ merge gates of a Good canonical system lie in that set's output cone": holds on 37/37.

## Waiting for
- angle 2 rules: tractability, branch tractability work/angle2/rules.py (charge(c) -> {gate: {set: weight}} + inequality).
- angle 3 potentials: session_01GmnDhdRKvz5Z7gneQqGG3V (no reply yet). Per coord 08:01, also front's B and C agents.

## Update 08:30: scaffold data-corpora (2aa9856) loaded
41079 correct one-NOT circuits (ess, tri, q, fixh, climb + earlier sets); 333 have a set with |S| >= 4 (512 such sets, all Good
canonical systems, 262 hard, 559 third+ merge gates). Code commit: mirror/laughing-mccarthy-ifdzly (see git log).
- B1 (3rd+ merges of different 4+-sets disjoint): fails on 16 entries = 10 DISTINCT circuits, all hand-built or climb
  extremes (front-match w8b/cxr, fc/cx44_*, fc/cxT*, chist/cxU*, p/cxP2; climb copies of cxr). Smallest s=24, n=8 (cxr).
  NEVER fails on the 254 q circuits (q_all 120, q_and_q2t 64, q_q2 43 with two 4-sets, q_q2t 27).
- B2 (3rd+ merges inside own cone): 333/333.

## Update 08:50: runs requested by front (08:06). Code + full output: mirror/laughing-mccarthy-ifdzly 120c99c, supportB/mergefrac_runs.py/.txt. SAT/data, not Lean.
(1) MergeFrac LP: min L, mu_w a distribution over ALL zero points z of S_w (every set w of the circuit), merge sets M_z(w) by
    union-find (w951 systems.system + merges, atoms z+e_u); dual pi = load-row marginals, normalised to sum 1.
    On all 163 DISTINCT circuits with a |S|>=4 set (n <= 20): L* <= 1 everywhere (MergeFrac holds). L* = 1 on 149, L* < 1 on 14.
    - The 149 with L* = 1 are forced: some set has a gate in EVERY M_z(w) (139 times the output o_w), so load 1 is unavoidable and
      the optimal pi is the point mass on that gate. Degenerate, carries no information beyond "o_w merges last".
    - The 14 with L* < 1 (all hand-built/adversarial): pi is uniform on its support (0/1 up to scale) in all 14. L* values:
      cxr 6/11 (|supp| 11), cxU6 10/17 (17), cxU8 14/23 (23), cx3 3/4 (4), and 2/3 with |supp| 3 on cxP2, cx44_0, cx44_1, xfail1,
      relworst_a, r_cx1, cx1, cfgI(fb), v1, j_cx1.
    - pi is 0/1 (up to scale) on 163/163.
(2) B1-failing distinct circuits (10): every shared 3rd+ merge gate is an OR gate shared by sets 0 and 1 and NONE is
    N-dependent (none downstream of the NOT). Killing restrictions x_v := b (w951 restrict, semantic; gate const/merged/dead):
    - cxT2 g19: x1,x2,x4,x6 := 0. cx44_1 g22: x0 := 1 only. cxT4 g25/g30/g35: x1,x2 + two set-private points := 0 each.
    - cxU6 g22, cxU_6_4 g24, cxU8 g28/g29, cxU_8_4 g30/g31: four points := 0 each (two per set).
    - NO single restriction kills: cxr g14; cxU6 g23,g24; cxU_6_4 g25,g26; cxU8 g30-32; cxU_8_4 g32-34; cxP2 g48-52.
    - cx44_0 g22: every x_v := 0/1 removes it (semantic merge: g22 equals an earlier gate on every face; check by hand).

## Update 09:05: optimal 0/1 dual K and minimising worlds (front request 08:09). Code/output: b13ec8c, supportB/dual_worlds.py/.txt/_summary.txt
For each of the 14 circuits with MergeFrac L* < 1: K = support of the LP's optimal pi (uniform on K in all 14); per set w the zero
points z of S_w minimising |M_z(w) ∩ K|, and h(z). Dual check: sum_w min_z |M_z(w) ∩ K| / |K| = L* exactly in all 14.
- K: cxr {12,13,14,20-23,28-31} (11); cxU6 17 gates; cxU8 23; cx3 {14,19,24,29}; |K| = 3 on the other ten
  (cfgI(fb) {12,17,33}, cx44_0 {14,23,30}, cx44_1 {14,24,32}, cxP2 {18,20,21}, cx1 {13,17,20}, j_cx1 {15,26,31},
  r_cx1 {13,18,21}, v1 {10,20,25}, relworst_a {16,20,23}, xfail1 {13,17,20}).
- WORLD CHOICE: in 13 of 14 circuits, for EVERY set w, |M_z(w) ∩ K| is the SAME at every zero point z (argmin = all z). So
  at the optimum no set picks a world: the K-count of the merge set is world-independent.
  Only exception: fb/cfgI, sets 0 and 1 (|S| = 4): min 1 attained at 28 of 32 zero points (h(z) takes both values on the argmin).
- h(z) on the argmin: both values (h = 0 and h = 1 worlds both optimal) except cxU6/cxU8 sets 0,1, cxr sets 0,1 and cxP2 sets 2,3,
  where h(z) = 0 at every zero point of S_w (h vanishes on the whole face).
- min per set: cxr 3+3 = 6 of 11; cxU6 5+5+0 = 10 of 17; cxU8 7+7+0 = 14 of 23; cx3 1+1+1 = 3 of 4; the |K| = 3 ones 1+1(+0) = 2
  (cxP2: 0+0+1+1).
