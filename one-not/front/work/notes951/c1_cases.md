# L-meta-951 structural cases (report)

Notation: s = total gates incl. NOT; #OR = OR gates among the s-1 non-NOT gates. z_T := indicator of complement of T. Easy S: h(Z_S)=0. D = {S : h(e_u)=1 for all u in S}.

Facts. (F1) g1 = f on {h=0}, g1 >= f everywhere (on h=1: g1 >= g0 = f). So C1 satisfies w1_S(Z)=0 at every point Z with h(Z)=0 and Z zero on S; and w1_S(e_u)=1 for all u in S ALWAYS.
(F2) g0 <= f, g0 = f on {h=1}. C0 gives w0_S(Z_S)=0 always, w0_S(e_u)=1 iff (suffices) h(e_u)=1.
(F3) Easy S => C1 computes o_S exactly everywhere. S in D => C0 computes o_S exactly.

## Theorem X (pairwise-extension lemma)
Assume for each S a set T_S ⊇ S with h(z_{T_S}) = 0 (T_S is a hitting set of the 1-points of h; T_S = S if S easy), such that for all S != S':  |S ∩ T_S'| <= 1  or  |S' ∩ T_S| <= 1.  Then #OR(C1) >= base, so s >= base+1.
Proof. Test point for S is z_{T_S}; by F1 w1_S(z_{T_S}) = o_S(z_{T_S}) = 0 and w1_S(e_u) = 1 (u in S). For wire g: A(g) = {S : g1(z_{T_S})=0}, B(g) = {u : g1(e_u)=1}. If S in A(g): e_u <= z_{T_S} for u notin T_S, so B(g) ⊆ T_S. OR gate in A(S) has both inputs in A(S); AND gate has at least one input in A(S). Run, per S, union-find on the atoms S (start singletons); invariant: for every processed wire g with S in A(g), B(g)∩S lies in one block. Leaves: {v}∩S. OR: merge the (<=2) blocks of B(a)∩S, B(b)∩S (one merge, charged to g). AND: B(g) ⊆ B(a) for the input a in A(S). At the end B(w_S) ⊇ S, so >= |S|-1 merges for S. Collision: if g=a∨b is charged by S != S', then a,b in A(S)∩A(S'), B(a),B(b) ⊆ T_S∩T_S'; S-merge gives distinct p,q in S∩T_S'; S'-merge gives distinct p',q' in S'∩T_S; contradicts the hypothesis. So distinct charges, #OR >= sum(|S|-1). ∎
With T_S = S for all S this is the zero-point/unit-point argument of the monotone case; AND gates are never charged.
Mixed version: also allow S in D to be handled in C0 (atoms e_u, test point Z_S). C0-C0 pairs: no condition. C1(S,T_S)-C0(S'): need |S' ∩ T_S| <= 1 (uses B0 ⊆ B1 ⊆ T_S). Same conclusion.

Corollary Y. Let X = union of hard sets. If h(1_X)=0 then s >= base+1. (T_S = S ∪ ([n]\X) for hard S, T_S=S for easy; hard-hard: |S ∩ T_S'| = |S∩S'| <= 1.)
Key observation: any pair with an easy set satisfies the hypothesis (|S ∩ T_easy| = |S ∩ S'| <= 1). Only hard-hard pairs matter.

## Cases
(c) all easy: X empty, h(0)=0. T_S=S. s-1 >= #OR >= base; s >= base+1. (Z) holds at Z_S because h(Z_S)=0; (U) always.
(a) h=x_v: hard = sets not containing v; X ∌ v; h(1_X)=0. Corollary Y: s >= base+1. (Take T_S = S ∪ {v} for S not containing v: test point has x_v=0, where C1 is exact. Hard-hard pair: |S ∩ (S'∪v)| = |S∩S'|.)
(d) exactly one hard set S0: only hard-hard pairs matter, none exist. T_{S0} = [n] (z = 0, h(0)=0). s >= base+1. Holds for ARBITRARY monotone h.
(e) h = x_a x_b: hard iff S ∩ {a,b} = ∅; X avoids a,b; h(1_X)=0; T_S = S∪{a}. s >= base+1.
(Generalization: any h with h(1_X)=0; in particular any h that vanishes on the union of hard sets, or any h with at most one hard set.)

## From base+1 to base+2
If N feeds an output (live) and #OR >= base: with no AND gate every wire is an OR of leaves, so an output reached by N would be >= N, giving o_S(0) = N(0) = 1 (h(0)=0), contradiction. So an AND gate exists, s >= base+2. If N is dead, delete it and the monotone bound gives s-1 >= base.

## (b) all |S|=2
Not fully proven. Theorem X + D-handling reduces it to a finite pair-choice problem. Brute force (n=4, all 166 nonconstant monotone h, all graphs; 10458 cases) : the sufficient condition (choose per edge a minimal hitting superset T_e or C0-type if in D) fails in 967 cases (9%), e.g. h with minterms {0,2},{1,2},{0,3},{1,3},{2,3}, edges K4 minus an edge. So b needs more than Theorem X.

## Obstruction in general
Two hard sets S,S' each forced to absorb the other (T_S ⊇ S', T_S' ⊇ S, e.g. h >= x_u ∨ ... on S'∪S) so one gate can be charged by both. Then the test points z_{T_S} are too low to force B(g) ⊆ S∩S'. Needed: either an AND-aware argument (two different zero points for one S, which breaks the 'AND has an input vanishing at the point' step) or a hybrid C0/C1 charging with atoms y_u = e_u + extra coordinates.
