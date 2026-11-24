# kgate notes (lane (a); rescoped to: (1) open 2-gate "light type-A" configuration, (2) k=3). Wrapped up early.
[Coord-desktop addendum: STAR4 re-verified by me; F2 count/step and exact lifted MUL (+8, scaffold) SURVIVE STAR4; its NOT is inessential (R5').]

Notation: U = union of the chosen sets, b ⊆ complement(U), X_j = b ∪ (U\S_j), D = {z : h(z)=0} (down-set; real = C_1 on D, real = C_0 off D). "light"/"heavy" = in D / not in D. K = set of gates, m_w = min_z |M_z(w) ∩ K|.

## CHECKED-BY-COMPUTATION (main finding): the real-merge 2-gate inequality FAILS outside C(b)
Script verify.py (builds an actual one-NOT circuit, asserts outputs correct, asserts Lemma M at every (w,z), computes all M_z(w)).
STAR4: n=4, S_1={0,1}, S_2={0,2}, S_3={0,3} (common point 0), h = MAJ(x1,x2,x3) = x1x2|x1x3|x2x3, N = ¬h.
  g' = s' ∨ t',  t' = x0 (as a function),  s' = (N ∧ (x1|x2|x3)) | x1x2x3      [circuit order: g' BEFORE g]
  g  = s ∨ t,    t = h,                    s  = (N ∧ x0) | x1x2x3 | (x0 ∧ h)
  outputs o_w = x0 ∨ x_w afterwards.
  Result: K={g,g'}: m = [1,1,1], Σ_w m_w = 3 > 2 = |K|. Moreover the union of ALL real merge sets of all three sets is {g,g'} (2 gates < base 3). Mechanism for S_u={0,u}, other leaves v,w:
    z=∅ (light): g'(∅)=0, g'(e_0)=1 (t'), g'(e_u)=1 (s') -> g' merges
    z={v} or {w} (light): g' = 1 there; g(z)=0, g(z+e_0)=1 via N∧x0 (light), g(z+e_u)=1 via h (heavy) -> g merges
    z={v,w} (heavy): g(z)=1 (h); g'(z)=0 (exactly two leaves, N=0), g'(z+e_0)=1 (x0), g'(z+e_u)=1 (x1x2x3) -> g' merges
  i.e. g' is 1 at the light point e_v and RETURNS TO 0 at the heavy point {v,w} above it ("crossing").
  This is in the open configuration: b=∅ forced, h(X_u)=1 (X_u={v,w}), foreign light point v (h(e_v)=0); C(b) fails for all three sets.
  With order g before g' the cheat disappears: m=[0,0,0]; so ORDER matters.
  Not a counterexample to no_minCE (47 gates) nor to MUL; it IS a counterexample to "Σ_w m_w ≤ |K| for real merge sets, |K|=2" and to "union of real merge sets ≥ base" => real MergePrice is FALSE in general; only the lifted version can be true.

## CHECKED: function-level condition N1
N1(K): every zero point z of every chosen set w has G=s∨t ∈ K with real G(z)=0, B_z(s)∩S_w ≠ ∅ ≠ B_z(t)∩S_w, disjoint. (Necessary for m_w ≥ 1 ∀w. Real functions = arbitrary functions monotone on D and on D^c separately: r = (r_1∧N)∨r_0.)
SAT search n1sat.py / scan2.py, |K|=2, three sets:
 - triangle of 4-sets, n=9, h=x0|x1|x2; also n=6 and n=4 variants: UNSAT (case B holds at FUNCTION level; UNSAT certificate only).
 - monotone (D = everything): UNSAT for all families tried.
 - exhaustive over ALL monotone h, n=4,5: triangle of 2-sets: all UNSAT; mix5, mix5b: all UNSAT; SAT for star4/star5 (h=MAJ of leaves), path4 {01,12,23} with h = x0x1|x0x3|x2x3, path5, tri4 {013,12,02}, tri5.
 - random h: tri6 {013,124,025} SAT with h = x0|x4|x1x2x3|x2x3x5; tri7 SAT with h = x0|x4 (circuits not realised except star4).
So: triangles are NOT safe in general, only with special h. The obstruction is the crossing, not a cycle parity.

## PROVED (general k, function level)
L1 (ceiling vanishing, under C(b) for set j): real g(X_j)=0 ⇒ g(b+A)=0 for all ∅≠A⊆U\S_j. [h(X_j)=0: Tool D; else pick u∈A, h(b+e_u)=1, real = C_0 monotone on [b+e_u,1].]
L2 (transversal): T(g):={j: g(X_j)=0}. If g ∈ M_{b+A}(w_i), A⊆U\S_i, then A∩S_j≠∅ for all j∈T(g)\{i}. Cor: a gate merging w_i at b has T(g)⊆{i}: free (T=∅) / private (|T|=1) / dead (|T|≥2); with k+1 forced sets there is a dead gate.
L3 (staircase, monotone window): order the sets so that Q_j := S_j ∩ (S_{j+1}∪…∪S_r) has |Q_j| ≤ 1 (exists iff the family is a Berge-acyclic hyperforest), z_j := b + (S_1∪…∪S_{j-1}) \ (S_j∪…∪S_r), and the real circuit monotone on the chain (h(z_j+e_u)=1 or h(z_j')=0 for j<j'). Then M_{z_j}(w_j) are PAIRWISE DISJOINT. Proof: g∈M_{z_j}(w_j) has two B-points in S_j, one u∉Q_j, so z_j+e_u ≤ z_{j'} and g(z_{j'})=1 for j'>j. ∎ Consequence: Σ_w π(M_{z_w}(w)) ≤ π(all) for EVERY price π, any k. Obstructions: (i) Berge cycles (odd AND even), (ii) crossing of the h-threshold.

## OPEN
 - k=3: not done (L3 under monotone window + hyperforest; false for real merge sets in general).
 - Right replacement for S1 in the open configuration: none exists for real merge sets (star4).
