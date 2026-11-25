# research / Fable W: which input weights must a proof of 951 use?

Code: research scratchpad `fableW/plane2.py`, `fableW/scan.py` (to be copied to branch `workspace`, research/tools/research951/fableW/).
Status words: proved (paper) / checked (computer) / conjecture / refuted.

## Entry 1 (headline): the weight <= 2 relaxation of 951 is FALSE, already MONOTONE, already at n = 625
- **Claim W2 (checked, exhaustive).** Affine plane AG(2,25): n = 625 points, m = 650 lines of size 25 ((1,1)-disjoint),
  base = 650 * 24 = 15600. There is a MONOTONE fan-in-2 AND/OR circuit with **12370** gates (no NOT) whose outputs equal
  OR(line) on EVERY input of Hamming weight <= 2 (all 195626 rows checked bit-parallel, 0 wrong outputs).
  It is wrong on weight 3 (about 5% of output bits on random weight-3 inputs), as it must be.
  For AG(2,49): n = 2401, base 117600, circuit 47474 gates (weight <= 2 checked on 20000 random rows; proof below covers all).
  `python3 plane2.py 5 --verify` (T = 5, 14970 gates, proved version), `scan.py` (T = 4, 12370 gates, checked version).
- Not a counterexample to 951 (the circuit is wrong on weight >= 3); it is a counterexample to every proof strategy that
  only uses correctness on inputs of weight <= 2 (in particular: 'unit vectors + pairs' test systems cannot prove 951 at scale).
- **Equivalent form (proved, trivial).** For a monotone circuit, 'correct on all inputs of weight <= k' <=> each output h_w
  satisfies o_w <= h_w <= o_w OR T_{k+1} (T = threshold). So the relaxation is the monotone complexity of the INTERVAL
  [o_w, o_w v T_{k+1}]: junk prime implicants of size >= k+1 inside the complement of S_w are allowed, and they help.

### Construction (proved on paper for weight <= 2; general k below)
Points V = F_p^2 with p = q^r (so V = F_q^{2r}); direction a has coordinate pi_a(x,y) = y - a x (pi_inf = x), F_q-linear.
1. Pick a hub direction h and S = 3 spoke directions j1, j2, j3. Their 4p lines are computed by plain ORs: 4(n - p) gates.
2. Cylinder rails C[i,f,d] = OR of the lines (i,c) with f(c) = d, f a functional F_p -> F_q: cheap ORs of line rails.
3. For another slope a and a functional psi_t on F_p, the hyperplane {psi_t(pi_a(u)) = d} of F_q^{2r} is, in the coordinates
   (pi_h, pi_j), {f1(pi_h u) + f2(pi_j u) = d}. 'Sloppy rail' H_j[a,t,d] = OR_{d1} C[h,f1,d1] AND C[j,f2,d-d1]: 2q - 1 gates.
   On an input X it is 1 iff some PHANTOM point P_j(w,w') (pi_h of w, pi_j of w'; w, w' in X) lies on the hyperplane.
4. Output(line a,b) = AND over t < T and j of H_j[a,t,psi_t(b)], with psi_0..psi_{T-1} Reed-Solomon functionals
   (every nonzero c in F_p is killed by at most r - 1 of them), T = 4(r-1) + 1.
Correctness on |X| <= 2 (proof): outputs are >= OR(L) by monotonicity. Let X = {u,v} miss L. A phantom of spoke j on L is a
point z of L with (dir(zu), dir(zv)) = (h, j) or (j, h). At most one z in L has dir(zu) = h and at most one has dir(zv) = h,
and the three spokes need three different z: so some spoke j has both phantoms off L. For that j the four points
u, v, P_j(u,v), P_j(v,u) are off L, each lies on at most r - 1 of the T hyperplanes through L, and T > 4(r-1): some rail is 0. QED
Size (r = 2, hash-consed, measured): q = 5: 14970 (T = 5) / 12370 (T = 4, checked only); q = 7: 57470 / 47474; base 15600 / 117600.
Asymptotically (q >= 4r - 3, n = q^{2r}): 4n + O(r n) = O(n log n / log log n) gates versus base ~ n^{3/2}.

## Entry 2: every fixed k fails; growth of the weight a proof needs (proved on paper, not machine-checked)
- **Weight <= k, direct generalisation (proved, paper).** Same circuit with S = k(k-1) + 1 spokes and T = k^2 (r-1) + 1 <= q:
  X has k^2 phantom points per spoke, at most k(k-1) spokes are blocked, each off-line point kills <= r - 1 functionals.
  Size O(k^2 n r + k^4 r q^2 p) versus base ~ n p. With r = 2, q ~ 2k^2: savings for all k <= c n^{1/8}.
- **Colour-coding amplification (proved, paper, probabilistic existence).** Let B be a monotone circuit correct on weight <= j.
  Take P = O(k log n) random partitions of the points into c = k^{1+1/j} classes; output_L = AND_partitions OR_classes B_L(X ∩ class).
  Always >= o_L; equal as soon as one partition puts <= j points of X in every class. Size ~ P c |B| = k^{2+1/j} n polylog.
  Hence the monotone weight <= k relaxation is false at scale for every k <= n^{1/4 - o(1)}.
- **Upper bound (proved, trivial).** A monotone function that equals o_w on the unit vectors and on the single input
  comp(S_w) (weight n - |S_w|) equals o_w everywhere. So the n + m inputs {e_v} ∪ {comp(S_w)} are a complete test set for the
  monotone theorem, and a test family R forces monotone exactness iff it contains them. Between n^{1/4} and n - |S|: OPEN.
- One NOT: the monotone circuits above are legal one-NOT circuits, so the one-NOT weight <= k relaxation fails for the same k.
  (Independent cheaper route for k = 2: (1-slice circuit AND NOT T_2) OR (monotone 2-slice circuit), O(n) gates.)

## Entry 3: guidance for the proof attempts
- What every saving circuit above exploits: an AND gate g = s ∧ t feeding only ORs of one output j, where s and t have junk
  minterms a, b inside comp(S_j) of weight <= k but a ∨ b has weight > k. Wegener's step 'c = a ∨ b' is exactly what kills this.
  So the zero-side test set of each output must be JOIN-CLOSED (equivalently contain its top comp(S_w), cf. `vanish_iff_sup`);
  any truncation of the zero set by weight is unsound for large systems.
- Weight-bounded test systems (unit vectors, pairs) remain valid certificates for SMALL systems (base below ~ c n log n).

## Entry 4 (research session, 07:50): INDEPENDENT VERIFICATION of Entry 1 — CONFIRMED
- Own checker (research/tools/research951/verifyW/check.py on branch workspace; shares nothing with plane2.verify_w2, only takes
  plane2.build's gate list): set system = AG(2,25) (650 lines of size 25, every point pair on exactly one line),
  all gates fan-in-2 AND/OR on earlier wires (no NOT), every output compared with OR(line) on ALL 195626 inputs of weight <= 2
  (big-int bitmasks): T=4: 12370 gates, 0 wrong outputs, base 15600 (saving 3230); T=5: 14970 gates, 0 wrong (saving 630).
- Sanity (w3.py): on 4000 random weight-3 inputs the T=4 circuit is wrong on 227273 of 2.6M output bits, never below OR(line)
  (as the monotone theorem demands).
- Status: Entry 1 CHECKED (independently). Entry 2 (every fixed k, colour coding up to n^{1/4-o(1)}) proved on paper by the Fable,
  not re-checked. Fable W stopped at 07:2x by the account's spend limit (resets 11:30 UTC); Q3 (smallest system where weight<=1
  beats base) not done.
