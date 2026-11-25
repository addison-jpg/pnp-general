> **OFF THE ROUTE (main, 2026-11-24 14:45): Hall / deficiency induction for PureSDR; PureSDR over pure classes is false for general correct circuits (cxMU_dd). Kept for the record; do not build on it.**

# research: DRAFT of the Hall / deficiency induction for PureSDR on the SAME circuit (no heredity), with tight test cases
(desktop Coord's ask via scaffold, 11:44. Status: DRAFT for front lanes A2/B and the referee; nothing here is proved
beyond what is marked. Templates: Halmos-Vaughan, Ore (research-heredity-lit.md §1); route: §6 there.)

## Setting
Correct one-NOT circuit, sets S_w, d_w = |S_w| - 1. Pure menu P(w): the distinct pure classes of w (I1 at a maximal zero point
Z off S_w = top_w minus a minimal transversal of Min_w, research-typeA-menus.md (a); I0 at top_w with minterm atoms). Each class
has exactly d_w gates (GM; Lean card_pureCls_le). PureSDR: one class per set, pairwise disjoint. Restricted menu for a family F:
classes at embedded points (0 off ∪S(F)); I1 embeds as is; I0 embeds via PureOpt.zeroAt (LEAN, PureHeredity.lean; research-heredity-lit.md §6 status 12:15).

## Induction skeleton (Halmos-Vaughan on menus of d_w-sets)
Assume PureSDR fails for a MinCE. Take a CRITICAL family F: no pure SDR of F, but every F - w (w ∈ F) has one (minimal
blocked subfamily; exists since singletons have SDRs). Then for every w ∈ F and every SDR P_w of F - w, every class of w meets
∪P_w. Two cases as in Halmos-Vaughan:
 (T) some proper G ⊂ F is TIGHT: |∪ of all classes of G| = base(G) (the menus of G live in exactly base(G) gates, so every SDR of
     G uses ALL of them). Remove those gates from the menus of F - G and recurse on F - G (restricted menus shrink).
     [12:00: for d_w >= 2 this step needs its own lemma (T'), see Referee answers 3.]
 (S) no proper subfamily is tight (surplus >= 1 everywhere): pick any class of some w, delete its gates from the others' menus;
     need: every other set keeps a class. For d_w = 1 (graph systems) surplus >= 1 gives this (classical); for d_w >= 2 it does
     NOT follow from cardinalities alone (one class deletes d_w gates). THIS IS THE MISSING LEMMA for general systems:
     (M) in a MinCE, if no proper subfamily of F is tight, there is a class C of some w ∈ F whose deletion leaves every
         v ∈ F - w with a class disjoint from C.
 [CORRECTED 12:00, see Referee answers: s < base enters only as |U(all)| <= s < base(all); (M) and (T') follow from PureSDR
 on the same circuit, so the corpus cannot falsify them; a menu proof of PureSDR for ALL correct circuits does not prove too
 much, but a proof from menu CARDINALITIES alone does (cardinality Hall gives no SDR of d-sets).]

## Tight test case (CHECKED by research, research/tools/research951/induct/menus.py, from scaffold's message)
pg13_slack4_I0min0_k1_1 (PG(2,3): 13 lines of size 4 on 13 points; s = 43, base = 39, h = x10, heavy point 10):
every set has EXACTLY ONE pure class, the 13 classes are pairwise disjoint, unique pure SDR; unit propagation fixes all 13 in one
round. Type B (10 ∈ S): w0 {18,23,24}, w7 {13,41,42}, w8 {43,44,45}, w9 {15,17,46} (I1 at top_w). Type A: I1 at Z = top_w - {10}
coincides with I0 (all minterms {10}): w1 {25,26,27}, w2 {28,29,30}, w3 {31,32,33}, w4 {22,34,35}, w5 {36,37,38}, w6 {19,39,40},
w10 {47,48,49}, w11 {50,51,52}, w12 {53,54,55}. So EVERY subfamily is tight (|∪ classes(G)| = base(G)): case (T) everywhere,
and any deficiency argument must be exact here (no slack to spend).
Second case pg13_slack5_I0min1_k0_4 (s = 44, base 39, minterms {1}, {4}; gate list corrected by scaffold 11:44: gates 39, 40 =
or(51,7), or(52,11)) CHECKED by research (induct/pg2.json): unique pure SDR. w0 type B {13,23,24}; every other set type A with a single
class (I1 = I0), except w6 [1,5,8,11]: I1 {20,38,40}, I0 {38,39,40} (the two classes differ in ONE gate). w3's single class
{20,22,33} meets w6's I1 class in gate 20, so w6 is forced to I0: unit propagation fixes all 13 in 2 rounds. Note for (M): a
set's alternative classes can overlap in d_w - 1 gates, so deleting one class may delete all but one gate of another.

Third case pg13 line 603 (scaffold 11:50, gates 28, 29 corrected 11:50; induct/pg3.json) CHECKED by research (own evaluation on all
8,192 inputs: correct, s = 44, base 39, one NOT): the only set among 28,067 with TWO I1 classes, so 'one I1 class per set' is
FALSE as a lemma. w0 [1,4,7,10] (type A: top_w contains the minterm {6,12}): I1 at Z1 = top_w − {12} gives {17,23,24} (= its I0
class), I1 at Z2 = top_w − {6} gives {17,22,24} (I1 only). w11 [2,6,7,11]: I1 {22,52,53}, I0 {16,52,53}. Exactly 3 pure SDRs
(w0, w11) = (Z2, I0), (Z1, I1), (Z1, I0); every class lies in some SDR. Alternatives again differ in ONE gate (as in pg2); not so in
general: pairs of distinct classes of one set by |C − C'| on 27 circuits: 1: 53, 2: 7, 3: 27 (e.g. cfgI set [0,1,2,3]:
{12,13,15} vs {30,31,33}).

## Referee answers (desktop Coord, 11:50) [research 12:00; CHECKED = computed, scripts research/tools/research951/induct/]
1. (M) CANNOT FAIL ON THE CORPUS, in either form. The unconditional form (M'): "for every family F with no tight proper subfamily,
   some class C of some w ∈ F leaves every v ∈ F − w a class disjoint from C" FOLLOWS from a pure SDR of F (any w, C = its class in
   the SDR). PureSDR has 0 failures on 75,619 corpus circuits (pnp-subproblem-puresdr-check.md; DEAD_ENDS), so (M') holds
   wherever it is tested. CHECKED anyway (mtest.py; 26 instances + pg1 + pg2, n <= 13, |F| <= 6): 8,350 families, 170 with no
   tight proper subfamily, (M') holds on 170 / 170. The same goes for (T') (item 3) and for MU (item 3): every lemma of this
   skeleton is a consequence of PureSDR on the same circuit. Cardinalities alone do not suffice for d_w >= 2:
   P(1) = {{a,b}}, P(2) = {{a,c},{b,d}} has |U(G)| >= base(G) for every subfamily G and no SDR.
   A NON-VACUOUS test is a CHOICE RULE: which class does (M) delete first? (E) "is every class of kind K in some pure SDR of the
   whole system?" (extend.py; only sets with >= 2 distinct classes, a single class is forced): I0 81 / 82, I1 77 / 78. Failures:
   cxT2 set 1 [0,1,5,6], I0 class {9,22,24}; pg2 w6 [1,5,8,11], I1 class {20,38,40}. So no WORLD rule picks the first class
   (agrees with DEAD_ENDS 'World 1 only' and 'World 0 for type A' refuted); a rule for (M) has to look at the other sets.
   Ask to scaffold: run extend.py on the full corpus, list the non-extendable classes; then test rules that use the other
   sets, e.g. "the class of w meeting the fewest classes of other sets" [proposed, untested].
   [12:05 scaffold: own EXT reimplementation reproduces both failures exactly (cxT2 set 1: I0 {9,22,24} no, I1 {9,32,33} yes;
   pg2 w6: I1 {20,38,40} no, I0 {38,39,40} yes); smoke test 230 circuits: 2 of 264 classes non-extendable, both I0, both in
   essential circuits; MU min 0. Full pass (62,463 distinct corpus + 2,224 ladder circuits; EXT, MU, CANON) running.]
2. GRAPH CASE: vacuous, already in DEAD_ENDS (front 11:38): m distinct output gates + the NOT give s >= m + 1 > base, and Lean
   MinCE.has4 (small3_bound) already excludes every MinCE whose sets all have size <= 3. So the graph case closes by OUTPUT
   COUNTING, not by Hall, and shows nothing about how a deficiency meets s < base; for the menu lane it is a model problem only.
   Output counting does not lift through the menus (CHECKED, outpeel.py): the output wire o_w lies in EVERY pure class of w for
   43 of 107 sets and in SOME class for 50 of 107 (cfgI set [7,8]: menu {25}, {22}, output wire 26), and in a class of another
   set for 0 of 107. So "peel the output gate, induct on d_w" fails on the data.
3. WHERE s < base ENTERS: exactly once, at the top. Every pure class is a set of gates, so |U(all)| <= s < base(all): in a MinCE
   the FULL family is Hall-deficient. Case (T) does not use it and cannot be the contradiction: tight families occur at any slack
   (pg1: every subfamily tight, s − base = 4). CHECKED (mu.py, 27 circuits): the slack lives OUTSIDE the menus,
   |U(all)| − base ∈ [0, 6] while s − base ∈ [4, 46]; |U(all)| = base exactly on pg1, pg2 and cxr (their 4, 5, 18 extra gates lie
   in no pure class). Consequences:
   - The weakest menu statement that gives the bound is choice-free: MU: |U(all)| >= base, U(all) = all gates in some pure class
     of some set (PureSDR ⇒ MU ⇒ s >= base; MU is strictly weaker for d_w >= 2, example in item 1). It is TIGHT on real circuits,
     so a proof of MU has no surplus to spend.
   - Corroborated by research-desktop (11:49, CanonD1.lean): the repaired D1' (adds Z ∩ S_v = ∅) has 0 collisions on the corpus
     but FAILS on a hand-built n = 5 circuit with extra gates feeding no output, so no condition on h, the sets, Z, m alone
     can work; the gate budget must enter.
   - An induction on deficient families uses minimality only for a minimal deficient PROPER family F (|U(F)| < base(F), every
     proper subfamily fine): that is heredity step (a3), "a deficient F forces a smaller counterexample", 'not as stated' in
     DEAD_ENDS (restricted circuits keep live gates outside the restricted menus).
   - (T') for d_w >= 2: Hall for F plus tightness of G give |U(F) \ U(G)| >= base(F − G), but a class of v ∈ F − G that meets U(G)
     in part is lost WHOLE while its other gates still count on the left; so Hall for the restricted menus of F − G does not
     follow (same gap as (M)); (T') is again a consequence of PureSDR, so untestable on the corpus.

## Data from scaffold 11:58 (ladder corpus; scaffold's numbers, not re-run by research except where marked)
- Unique pure SDR on 177 ladder circuits (173 of 2,159 PG(2,3), 4 of 65 AG(2,4)). 171: every set has exactly ONE pure class and
  the classes are pairwise disjoint (Hall with equality, nothing to force; test case 1 is of this kind). 6: one set has 2
  classes and a single-class neighbour kills one in ONE step (test case 2's kind). 0 need more than unit propagation.
  #pure SDRs on PG(2,3): {1: 173, 2: 1747, 3: 163, 4: 63, 5: 1, 6: 11, 9: 1}.
- Desktop Coord's choice-free candidate CANON fails its Q1: type-A sets whose I1 and I0 classes never coincide (smallest
  essential: named.jsonl:12, n = 5, w0 I1 {7,8,9} vs I0 {15,16,17}, disjoint). CORROBORATED by research (kinds.py, 27 circuits):
  of 111 sets with both an I1 and an I0 class, 46 have EVERY I1 class gate-disjoint from EVERY I0 class (e.g. cfgI set
  [0,1,2,3]: I1 {12,13,15}, I0 {30,31,33}; there sets [0,1,2,3] and [0,4,5,6] even share the I1 class {12,13,15}).
  For (M): the two worlds of one set can offer gate-disjoint options, so a deletion argument cannot assume a set's options
  overlap (contrast pg2 / pg3, where alternatives differ in one gate).
