# research: DRAFT of the Hall / deficiency induction for PureSDR on the SAME circuit (no heredity), with tight test cases
(desktop Coord's ask via scaffold, 11:44. Status: DRAFT for front lanes A2/B and the referee; nothing here is proved
beyond what is marked. Templates: Halmos-Vaughan, Ore (research-heredity-lit.md §1); route: §6 there.)

## Setting
Correct one-NOT circuit, sets S_w, d_w = |S_w| - 1. Pure menu P(w): the distinct pure classes of w (I1 at a maximal zero point
Z off S_w = top_w minus a minimal transversal of Min_w, research-typeA-menus.md (a); I0 at top_w with minterm atoms). Each class
has exactly d_w gates (GM; Lean card_pureCls_le). PureSDR: one class per set, pairwise disjoint. Restricted menu for a family F:
classes at embedded points (0 off ∪S(F)); I1 embeds as is; I0 needs the generalized pureI0 hypothesis (research-heredity-lit.md §6).

## Induction skeleton (Halmos-Vaughan on menus of d_w-sets)
Assume PureSDR fails for a MinCE. Take a CRITICAL family F: no pure SDR of F, but every F - w (w ∈ F) has one (minimal
blocked subfamily; exists since singletons have SDRs). Then for every w ∈ F and every SDR P_w of F - w, every class of w meets
∪P_w. Two cases as in Halmos-Vaughan:
 (T) some proper G ⊂ F is TIGHT: |∪ of all classes of G| = base(G) (the menus of G live in exactly base(G) gates, so every SDR of
     G uses ALL of them). Remove those gates from the menus of F - G and recurse on F - G (restricted menus shrink).
 (S) no proper subfamily is tight (surplus >= 1 everywhere): pick any class of some w, delete its gates from the others' menus;
     need: every other set keeps a class. For d_w = 1 (graph systems) surplus >= 1 gives this (classical); for d_w >= 2 it does
     NOT follow from cardinalities alone (one class deletes d_w gates). THIS IS THE MISSING LEMMA for general systems:
     (M) in a MinCE, if no proper subfamily of F is tight, there is a class C of some w ∈ F whose deletion leaves every
         v ∈ F - w with a class disjoint from C.
 The contradiction with s < base must enter through (M) (data: PureSDR holds on all corpus circuits, which all have s >= base,
 so a proof using only menu combinatorics would prove too much unless it uses minimality).

## Tight test case (CHECKED by research, tools/research951/induct/menus.py, from scaffold's message)
pg13_slack4_I0min0_k1_1 (PG(2,3): 13 lines of size 4 on 13 points; s = 43, base = 39, h = x10, heavy point 10):
every set has EXACTLY ONE pure class, the 13 classes are pairwise disjoint, unique pure SDR; unit propagation fixes all 13 in one
round. Type B (10 ∈ S): w0 {18,23,24}, w7 {13,41,42}, w8 {43,44,45}, w9 {15,17,46} (I1 at top_w). Type A: I1 at Z = top_w - {10}
coincides with I0 (all minterms {10}): w1 {25,26,27}, w2 {28,29,30}, w3 {31,32,33}, w4 {22,34,35}, w5 {36,37,38}, w6 {19,39,40},
w10 {47,48,49}, w11 {50,51,52}, w12 {53,54,55}. So EVERY subfamily is tight (|∪ classes(G)| = base(G)): case (T) everywhere,
and any deficiency argument must be exact here (no slack to spend).
Second case pg13_slack5_I0min1_k0_4 (minterms {1}, {4}; one forcing step: w3's single class {20,22,33} meets w6's I1 class
{20,38,40} in gate 20, so w6 takes its I0 class {38,39,40}): NOT re-checked: the gate list as transmitted is not a correct
circuit (output of [2,6,7,11] missing; an index is off by one around gates 37-39). Awaiting the corpus path from scaffold.
