# scaffold-duals: optimal MergeFrac dual prices (coord request 08:06, for front angle A). SAT/LP data, not Lean.
Code/data: scaffold-951 512f4b1 work/notes951/scripts/scaffold_runs/duals/ (scaffold_duals.py/.txt/.jsonl).
It imports support-B's harness.corpora() and w951 systems.system/merges, so M_z(w) is identical to mergefrac_runs.py.
Earlier corpus-wide pass (mdual.py, ~40k circuits incl. |S|<=3): scaffold-951 6fe4f77 f15/logs/md.

## Method
Per circuit (163 distinct one-NOT circuits with a |S| >= 4 set):
- L* = max_pi sum_w min_z pi(M_z(w)) with pi >= 0 and pi(gates) = 1; pi0 = the HiGHS extreme optimal pi.
- On the OPTIMAL FACE (sum_w min_z pi(M_z(w)) >= L* - 1e-7): the max total price on each of
  - Ndep = gates downstream of N
  - third = 3rd+ merges (union-find order) of a |S| >= 4 set at some zero point
  - cross = N-dependent gates that merge for a at a world-0 point (h(z)=1) and for b != a at a world-1 point (h(z|S_b)=0)
- Tight pairs = sets a, b whose minimising merge sets under pi0 share priced gates (with the shared price).

## Summary (163 circuits)
- L* > 1: 0. L* < 1: 14. L* = 1: 149, forced by a gate in every M_z(w).
- pi0 is 0/1 up to scale (K-Rado form) on 163/163.
- The optimal face can carry price on N-dependent gates: 120/163 (110 of the L*=1 ones reach 1.0).
- The optimal face can carry price on 3rd+ merges of 4+-sets: 152/163 (147 reach 1.0).
- CROSS-WORLD gates (the board's 'missing piece') do not occur in ANY of the 163 circuits. In the ~40k all-size corpus they
  occur in 26 circuits (K4, K4-e, C5, rand, atlas, bad_k4), and there the max price on them over the optimal face is 0.
  So no tight dual ever loads a cross-world gate in the data. Either that piece is slack in practice, or the corpora never stress it:
  a TARGETED generator for circuits with cross-world gates and L* near 1 is the next useful data.
- Tight pairs: almost always the two big sets (0,1). The shared price is L*/2 (cxr 0.27, cxU6 0.29, cxU8 0.30, the 2/3 family 0.33).

## The 14 circuits with L* < 1
| circuit | n | s | base | L* | supp pi0 | maxNdep | maxThird | maxCross | tight pairs (pi0) |
|---|---|---|---|---|---|---|---|---|---|
| front-match__w8b__cxr.json:0 | 8 | 24 | 6 | 0.5455 | 11 | 0.727 | 0.455 | 0.000 | [(0, 1, 0.273)] |
| chist__cxU6.json:0 | 14 | 41 | 11 | 0.5882 | 17 | 0.706 | 0.882 | 0.000 | [(0, 1, 0.294)] |
| chist__cxU8.json:0 | 18 | 53 | 15 | 0.6087 | 23 | 0.696 | 0.913 | 0.000 | [(0, 1, 0.304)] |
| fb__cfgI.json:0 | 9 | 25 | 7 | 0.6667 | 3 | 0.667 | 1.000 | 0.000 | [(0, 1, 0.333)] |
| fc__cx44_0.json:0 | 7 | 30 | 6 | 0.6667 | 3 | 0.000 | 1.000 | 0.000 | [(0, 1, 0.333)] |
| fc__cx44_1.json:0 | 7 | 32 | 6 | 0.6667 | 3 | 0.000 | 1.000 | 0.000 | [(0, 1, 0.333)] |
| p__cxP2.json:0 | 16 | 73 | 16 | 0.6667 | 3 | 0.000 | 0.000 | 0.000 | [(2, 3, 0.333)] |
| front-match__w8__cx1.json:0 | 9 | 22 | 7 | 0.6667 | 3 | 0.667 | 1.000 | 0.000 | [(0, 1, 0.333)] |
| scaffold-951__fable_attack__j_cx1.json:0 | 9 | 37 | 7 | 0.6667 | 3 | 0.667 | 1.000 | 0.000 | [(0, 1, 0.333)] |
| scaffold-951__fable_attack__r_cx1.json:0 | 9 | 23 | 7 | 0.6667 | 3 | 0.667 | 1.000 | 0.000 | [(0, 1, 0.333)] |
| scaffold-951__fable_attack__v1.json:0 | 8 | 26 | 6 | 0.6667 | 3 | 0.000 | 0.667 | 0.000 | [(0, 1, 0.333)] |
| tractability__inst__relworst_a.json:0 | 9 | 25 | 7 | 0.6667 | 3 | 0.667 | 1.000 | 0.000 | [(0, 1, 0.333)] |
| tractability__inst__xfail1.json:0 | 9 | 23 | 7 | 0.6667 | 3 | 0.667 | 1.000 | 0.000 | [(0, 1, 0.333)] |
| front-match__w8__cx3.json:0 | 10 | 24 | 9 | 0.7500 | 4 | 0.750 | 0.750 | 0.000 | [(0, 1, 0.25), (0, 2, 0.25), (1, 2, 0.25)] |

pi0 supports, gate wires, for the hardest ones:
- inst:front-match__w8b__cxr.json:0: [12, 13, 14, 20, 21, 22, 23, 28, 29, 30, 31]
- w9:chist__cxU6.json:0: [20, 21, 22, 23, 24, 32, 33, 34, 35, 36, 37, 44, 45, 46, 47, 48, 49]
- w9:chist__cxU8.json:0: [26, 27, 28, 29, 30, 31, 32, 42, 43, 44, 45, 46, 47, 48, 49, 58, 59, 60, 61, 62, 63, 64, 65]
- w9:fb__cfgI.json:0: [13, 17, 33]
Full rows, including the maximising pi for each class, are in the jsonl.

## 08:35 front's cross-world slack tests (xtest.py, scaffold scratchpad f15; on the 26 all-size circuits that HAVE cross-world gates X)
- (a) Restricting pi to K ⊆ G \ X loses nothing: L*_noX = L* on 26/26.
- (b) For every 0/1 K: sum_w min_z |M_z(w) ∩ K| <= |K \ X| + |X ∩ K|/2. Exact MILP max of LHS - RHS: <= 0 on 26/26.
- (c) min pi(X) over the optimal face is 0 on 26/26, so some optimal price always vanishes on X.
Caveat: these 26 are small pair/edge systems (K4, K4-e, C5, atlas). They are weak evidence for 4-set bottleneck cases.
## 08:40 coord GO: targeted cross-world generator (xgen.py), running
SAT enumeration with blocking, w = a HARD 4-set, sizes base+1..base+4.
Systems: {0123} plus a star of pairs; {0123},{04},{45},{15},{25}; {0123},{04},{15},{45}; {0123},{045},{146}; q; and the star with an essential NOT.
Every circuit with cross-world gates is analysed: L*, min pi(X) on the optimal face, the |X|/2 inequality.
First pass: {0123},{045} at s = 9, 10 gave 600 circuits and none had cross-world gates.

## 08:55 CORRECTION (world-1 definition) and re-run
My tools used world-1 := h(z|S_b) = 0. The board's definition is h(z+e_u) = 0 for all u in S_b, which is weaker since h is monotone,
so there are more world-1 points. The qg-d2 helper caught the mismatch. Everything above has been re-run with the board definition
(scaffold-951 after d31a0da: f15/logs/md2, duals/scaffold_duals_v2.*).
- Circuits with cross-world gates X: 116 (was 26), over all data-corpora + named circuits. fixh16_clean alone contributes 87.
- (a) L*_noX = L* on 116/116. (b) The |X|/2 inequality holds for every 0/1 K (exact MILP) on 116/116.
  (c) min pi(X) on the optimal face = 0 on 116/116.
- 163 |S|>=4 circuits (support-B set): still NO cross-world gates. The other numbers are unchanged
  (L* <= 1, 14 below 1, pi0 0/1 on all, Ndep 120, third 152).
- The targeted generator was restarted at 08:55 with the board definition. The earlier xgen run (old definition) was discarded.
