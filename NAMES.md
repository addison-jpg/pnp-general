# Names

Generated from `NAMES.json` by `tools/names_build.py`; edit the script, not this file.

## Conventions (formal proof style, Lean 4 / Mathlib)

1. Every item has ONE formal name and ONE role: Definition, Lemma, Proposition, Theorem, Conjecture, Open, Refuted, Counterexample.
2. A property or structure is `UpperCamelCase` (`MinCE`, `CubeLocal`, `UGameWon`). A function or object is `lowerCamelCase` (`notInput`, `mergeSet`, `realWitness`).
3. A theorem is `snake_case` and states its conclusion, then `_of_`, then its hypotheses: `no_minCE_of_ugame`, `liftSDR_of_ugame`, `muF2_of_notVar`.
4. A fact of a minimal counterexample lives in its namespace: `MinCE.no_dup`, `MinCE.observable`, `MinCE.no_rewire`.
5. A counterexample is `Cex.<name>` and says what it refutes; a refuted statement is `Refuted.<name>` and names its counterexample.
6. No bare letters or numbers as names in prose: write `realWitness` (F2), `MinCE.no_rewire` (R6); the old code goes in brackets once.
7. A statement keeps the word of its layer: checked (Lean), paper, tested n/N, premise. A Conjecture is never written as a Lemma.
8. Existing Lean identifiers are not renamed (a rename costs a full rebuild); new Lean follows 2 to 5.

## The tree

Every name has one parent. Read bottom up: a counterexample or a theorem is a leaf, its parent is the concept it serves.

- `L_meta_951` · Theorem (one sorry: no_minCE) · **one NOT gate saves nothing on Boolean sums** (old: 951, L-meta-951): sets of size >= 2 that pairwise share at most one point; a circuit of AND and OR gates and one NOT gate computes the OR of every set; then number of gates >= monotone optimum
  - `section Objects` · Section · **objects**: the things every statement is about
    - `SetSystem` · Definition · **set system** (old: S_w): the sets; any two share at most one point
    - `demand` · Definition · **demand of a set** (old: d_w): size of the set minus 1
    - `base` · Definition · **monotone optimum**: sum of the demands; the exact gate count without a NOT gate (Wegener, Mehlhorn)
    - `notGate` · Definition · **NOT gate** (old: N): the single NOT gate
    - `notInput` · Definition · **NOT input** (old: h): the wire the NOT gate reads; a monotone function of the inputs
    - `faceZero` · Definition · **face with the NOT gate set to 0** (old: C_0): monotone circuit; never above the real circuit
    - `faceOne` · Definition · **face with the NOT gate set to 1** (old: C_1): monotone circuit; never below the real circuit
    - `worldZero` · Definition · **world 0** (old: U, {h = 1}): inputs where the NOT gate outputs 0
    - `worldOne` · Definition · **world 1** (old: D, {h = 0}): inputs where the NOT gate outputs 1
    - `cube` · Definition · **cube** (old: Q, x_Q = 1): the inputs with every point of Q set to 1
      - `W951CubeKeep` · Module · **W951CubeKeep.lean**
    - `Alive` · Definition · **alive set**: a set that does not meet Q
    - `baseDQ` · Definition · **monotone optimum of a cube** (old: base(Q), baseDQ): sum of the demands of the alive sets
    - `CubeLocal` · Definition · **local cube**: on the cube the NOT input is one input or constant
      - `muF2_of_notVar` · Theorem · **muF2_of_notVar**: NotVarF2: the statement when the NOT gate reads an input
      - `localClosureByWeightOne` · Definition · **local closure by weight one** (old: LW1): every alive set has a zero point inside the cube, off the set, where the NOT input is 0, light points stay light there, and any two alive sets have one set with at most one point outside the other set's zero point; then base(Q) <= |F2(Q)| (baseDQ_le_F2_of_LW1)
      - `CubeF2` · Module · **CubeF2.lean**
      - `NotVarF2` · Module · **NotVarF2.lean**
    - `CubeNonlocal` · Definition · **non-local cube**: on the cube the NOT input depends on at least two inputs
    - `ZeroPoint` · Definition · **zero point of a set** (old: z, Z): an input that is 0 on the whole set
    - `topZero` · Definition · **top zero point of a set** (old: top_w): 0 on the set, 1 everywhere else
    - `atom` · Definition · **atom** (old: e_u, Z + e_u): a zero point of a set with one point of the set switched on
    - `Heavy` · Definition · **heavy point**: a point v with NOT input = 1 at Q + e_v
      - `GraphHeavy` · Module · **GraphHeavy.lean**
    - `cost` · Definition · **cost of a point** (old: cost(v)): sum of the demands of the alive sets through the point
    - `gain` · Definition · **gain of a point** (old: gain(v)): number of family gates that leave the family when the point is set to 1
    - `mergeSet` · Definition · **real merge set** (old: M_z(w)): the OR gates that join two blocks of a set in a union-find run at a zero point; always demand-many (merge count lemma, Lemma M)
      - `merge_run` · Theorem · **merge_run**: MergeRun.lean: the merge count lemma
      - `RunTransfer` · Module · **RunTransfer.lean**
      - `MergeRun` · Module · **MergeRun.lean**
    - `pureI0` · Definition · **pure class in world 0** (old: I0): a class of a set read at a zero point in world 0
    - `pureI1` · Definition · **pure class in world 1** (old: I1): a class of a set read at a zero point in world 1
      - `canon_size / canon_disjoint / canon_cross` · Theorem · **canon_size / canon_disjoint / canon_cross**: CanonClass.lean
      - `worldLemmas` · Definition · **world lemmas** (old: W0, W1): CanonClass lemmas: size and disjointness inside one world
      - `CanonClass` · Module · **CanonClass.lean**
      - `CanonOneNot` · Module · **CanonOneNot.lean**
    - `lift` · Definition · **lifted circuit** (old: lift, y): the NOT gate replaced by a fresh input y; a monotone circuit for a partial function
    - `liftClass` · Definition · **lifted class**: a class of a set read in the lifted circuit; need not sit above the zero point
    - `setOfTypeA` · Definition · **set of type A** (old: type A): a set w with h(top_w) = 1, where h is the input of the NOT gate and top_w is the point that is 1 exactly off S_w; equivalently some minterm of h avoids S_w. The other sets (h(top_w) = 0) are the FREE sets, whose world-1 classes K_1(w) at top_w are pairwise disjoint (W1). Source: research-typeA-menus.md, research-typeA-increment.md
      - `TypeA` · Module · **TypeA.lean**
    - `setOfTypeB` · Definition · **set of type B** (old: type B): the NOT input is 0 at the point with every input outside the set equal to 1 (h(top_w) = 0)
    - `outputInTwoWorldNormalForm` · Definition · **output in two-world normal form** (old: DD, DD-normal): the output equals (set OR) AND h on one face and (set OR) OR h on the other
      - `TwoWorld` · Module · **TwoWorld.lean**
    - `completeGraphOnFourPointsAsSetSystem` · Definition · **complete graph on four points as set system** (old: K4): all six pairs of four points; the standard small test system
  - `section FactsOfAMinimalCounterexample` · Section · **facts of a minimal counterexample** (old: R1 to R7, MinCERed): what a counterexample with the fewest gates must satisfy
    - `MinCE` · Definition · **minimal counterexample**: a correct circuit with fewer gates than the monotone optimum and the fewest gates among such [definition]
    - `MinCE.no_const` · Lemma · **no constant gate** (old: R1, no_const): [checked]
    - `MinCE.no_dup` · Lemma · **no two gates compute the same function** (old: R2, no_dup): [checked]
    - `MinCE.no_var` · Lemma · **no gate computes an input** (old: R3, no_var): [checked]
    - `MinCE.live` · Lemma · **every gate is read** (old: R4, live): [checked]
    - `MinCE.not_used` · Lemma · **the NOT gate is essential** (old: R5', not_used): both faces are incorrect [checked]
    - `MinCE.observable` · Lemma · **observability** (old: R+, observable): a constant put on any nonempty set of readers of a wire makes the circuit incorrect [checked]
    - `MinCE.no_rewire` · Lemma (paper) · **no gate-saving rewiring** (old: R6, no_rewire): no gate input can be moved to another wire so that the circuit stays correct and a gate goes unread [checked]
      - `MinCERewire` · Module · **MinCERewire.lean**
    - `MinCE.private_not_cone` · Lemma (reported) · **private NOT cone** (old: R7): a gate that depends on the NOT gate, whose NOT-dependent feeding gates are read only inside its cone, differs from both faces C_0 and C_1; an instance of observability with the NOT gate as the wire [paper]
  - `section TheCount` · Section · **the count** (old: MU): some named family of gates has at least monotone-optimum members; this implies the statement
    - `faceWitness` · Conjecture · **one-face witness gates** (old: F1, UC): OR gates that are 0 at a zero point of an alive set and 1 at two of its atoms, in one face
    - `realWitness` · Conjecture · **real-witness gates** (old: F2): the same with the real circuit in place of a face
    - `faceWitnessRepaired` · Conjecture · **repaired one-face witness gates** (old: F3): one-face witness gates with an extra condition on face 1 atoms
    - `faceWitnessCone` · Conjecture · **cone-restricted one-face witness gates** (old: F4): one-face witness gates inside the cone of the output of the witnessing set
    - `realWitnessCone` · Conjecture · **cone-restricted real-witness gates** (old: F5): real-witness gates inside the cone of the output of the witnessing set
    - `MergeSDR` · Refuted for all circuits; Open under MinCE · **disjoint representatives over real merge sets**: one real merge set per set, pairwise disjoint
      - `lAvoid` · Theorem · **lAvoid**: Augment.lean
    - `PureSDR` · Refuted for all circuits · **disjoint representatives over pure classes**: one pure class per set, pairwise disjoint
      - `PureHeredity` · Module · **PureHeredity.lean**
      - `PureRestrict` · Module · **PureRestrict.lean**
    - `LiftSDR` · Theorem when UGameWon; Open otherwise · **disjoint representatives over lifted classes**: one lifted class per set, pairwise disjoint
    - `LiftCount` · Theorem when UGameWon; Open otherwise · **lifted count** (old: MUL): the union of lifted classes has at least monotone-optimum gates
    - `MergeFrac` · Refuted for all circuits; Open under MinCE · **fractional merge matching** (old: MergeFrac, FracMatch): weights on zero points with load at most 1 on every gate
    - `MergePrice` · Refuted for all circuits; Open under MinCE · **price inequality**: for every price on gates, the cheapest classes together cost at most all gates
    - `separationOfTheStarOfAPoint` · Definition · **separation of the star of a point** (old: STAR-SEP, STAR-COUNT, StarCount2): the sets through one point get pairwise disjoint classes (counting form: STAR-COUNT)
    - `strongCommonUniversalPropertyAndChainPick` · Definition · **strong common-universal property and chain pick** (old: StrongCU, ChainPick, CU): supported, not refuted; CU alone does not give the price inequality
    - `pairHillClimb` · Definition · **pair hill-climb** (old: O2, O2-PAIR): search for a counterexample to disjoint representatives; none found
    - `priceFormOverPureClasses` · Definition · **price form over pure classes** (old: PureFrac, PurePrice): pureFrac_iff_purePrice: LP duality, checked
    - `dualAndLinkOfTheFractionalMergeMatching` · Definition · **dual and link of the fractional merge matching** (old: MergeDual, MergeLink): Lean modules of the MergeFrac <=> MergePrice chain
  - `section ThePointStep` · Section · **the point step** (old: STEP, GainF2, GainOne): prove the count one input at a time: setting some input to 1 removes at least cost-of-the-point gates from the family
    - `GainF2` · Refuted for all circuits; Open under MinCE.no_rewire · **point step for real-witness gates** (old: F2 STEP, GainF2): some point has gain >= cost; false for all correct circuits, open among circuits with no gate-saving rewiring
      - `no_minCE_of_gainF2_or_cubeLocal` · Theorem · **no_minCE_of_gainF2_or_cubeLocal**: CubeF2.lean:353: local cube or point step at every cube => the statement
      - `F2Induct` · Module · **F2Induct.lean**
      - `F2Desc` · Module · **F2Desc.lean**
      - `F2FirstJoin` · Module · **F2FirstJoin.lean**
    - `GainOne` · Refuted · **point step for one-face witness gates** (old: GainOne, LIGHT-COUNT, HEAVY-COUNT): the same for one-face witness gates; refuted
    - `DeleteStep` · Refuted · **point deletion** (old: x_v := 0): induction that sets a point to 0; refuted
    - `MixedStep` · Open · **mixed induction**: set a point to 0 at some cubes and to 1 at others; not refuted, two circuits tested
    - `ElimStep` · Conjecture · **gate elimination step** (old: GE, ElimStep): setting a point to 1 and simplifying removes at least cost-many gates; the inductive form of the statement
    - `seenGatesAndStarOnlyGates` · Definition · **seen gates and star-only gates** (old: SEE+K3, SEE0, K0, K3, F2SeeK3): SEE+K3: some point v has at least cost(v) gates of F2(Q) that leave it, counting the gates that are 1 at Q + e_v (SEE, minus survivors; K0 / K1 / F1* say which survive) and the gates whose witnesses all come from sets through v (K3). The reduction GainF2 <= SEE+K3 is checked in Lean (F2SeeK3.lean); the count itself fails on the twin trees, so it is not true for all correct circuits
    - `lightStarRule` · Refuted · **light-star rule** (old: LIGHT-STAR, LightStar, F2Light): the point step at a light point from the star of the point; false for all correct circuits
    - `absorbAndReroute` · Refuted · **absorb and reroute** (old: ABSORB, REROUTE, INTERNAL): ABSORB is the point step at v rewritten with the first-joining gates (bookkeeping, equivalent to the step); REROUTE and INTERNAL are stronger sufficient forms (INTERNAL also fails on star4 at Q = empty); all three fail with the step on the twin trees
    - `coneCertificate` · Open · **cone certificate** (old: CERT-1c, CERT-3c, CertStair, (D)+(S)): death (D) and disjointness (S) of cone merge sets
  - `section TheCertificateGame` · Section · **the certificate game** (old: U-game, Theorem G): a pairwise test on the lifted outputs; when it is won the statement is checked in Lean
    - `LTS` · Conjecture · **lifted test system**: a zero point and atoms chosen for a set in the lifted circuit
    - `LTSCert` · Conjecture · **pair certificate**: for two sets: at most one atom of one system is not below the zero point of the other
    - `UGameWon` · Conjecture · **certificate game won** (old: U-game won): every set has a system and every pair has a pair certificate in one direction
      - `ugame_of_G1 / ugame_of_G0 / ugame_of_allHeavy / ugame_of_typeB` · Theorem · **ugame_of_G1 / ugame_of_G0 / ugame_of_allHeavy / ugame_of_typeB**: four cases where the game is always won
    - `liftSDR_of_ugame` · Theorem · **certificate game theorem** (old: Theorem G, liftSDR_of_ugame): game won => disjoint representatives over lifted classes => the statement; no minimality [checked]
      - `no_minCE_of_ugame` · Theorem · **no_minCE_of_ugame**: UGame.lean
    - `ugame_exact_for_values` · Proposition (paper) · **exact reach of value arguments** (old: Proposition S): an argument reading only gate values at test points stops exactly at the game [paper]
    - `ugame_pure_of_normal` · Theorem (paper) · **no mixing of worlds** (old: Theorem D): with two-world normal outputs and sets of size >= 3 a winning choice stays in one world [paper]
    - `merge_gate_one_colouring` · Lemma (paper) · **one colouring per merge gate** (old: Lemma T): a merge gate splits every set it serves by one colouring; forbids odd cycles of 2-point traces only [paper]
    - `no_minCE_of_ugameLost` · Open · **lost game** (old: open part (X)): OPEN: circuits whose lifted outputs lose the game; smallest: sets {0,1,2}, {0,3,4}, NOT input x1 OR x3
    - `staircaseLemmas` · Definition · **staircase lemmas** (old: L1, L3, L4, STAIRCASE): Berge-acyclic families have a winning order
    - `liftOfTwoGateConfigurations` · Definition · **lift of two-gate configurations** (old: 2G-LIFT, 2G-b): no two gates serve as all classes of two sets in the lifted form
  - `section DeadEnds` · Section · **dead ends** (old: DEAD_ENDS.md): refuted or exhausted routes, in seven families
    - `Refuted.classChosenWithoutLookingAtTheOtherSets` · Refuted · **class chosen without looking at the other sets** (old: family A): kills: disjoint representatives over pure classes; rows in 951/DEAD_ENDS.md section A
      - `Cex.three4SetsInATriangle` · Counterexample · **three 4-sets in a triangle** (old: cxT2): n = 9; no gate-saving rewiring found in 1,679 tries; loses the certificate game; the hard core named by cTAHG
      - `Cex.adversaryAgainstTheTwoPointMenu` · Counterexample · **adversary against the two-point menu** (old: ADV3): load 1.2
      - `Refuted.threeCircuitsAgainstCanonicalMatching` · Refuted · **three circuits against canonical matching** (old: cx1, cx2, cx3): cx2: sunflower {0,1,4},{0,2,5},{0,3,6}, 18 gates, counted union 5 < demand 6
      - `Refuted.circuitAgainstTheCoinRule` · Refuted · **circuit against the coin rule** (old: cxtw3, cxtw3c): n = 9, 34 gates; outside the minimal-counterexample case
      - `Refuted.sixCircuitsAgainstTheProductRule` · Refuted · **six circuits against the product rule** (old: cxP, cxP1, cxP3, cxP4, cxP6, Π*)
      - `Refuted.circuitAgainstTheStarRule` · Refuted · **circuit against the star rule** (old: cxstar5, ★)
      - `Refuted.circuitAgainstTheRestrictedRelativeSandwich` · Refuted · **circuit against the restricted relative sandwich** (old: cxT4): also kills whole-class charging
      - `Refuted.circuitsAgainstFixedZeroPointDistributions` · Refuted · **circuits against fixed zero-point distributions** (old: cxrb, cxU_8_4): cxU_8_4: n = 20
      - `Refuted.circuitAgainstWorldPurePlainZeroPoints` · Refuted · **circuit against world-pure plain zero points** (old: cxe3): every plain choice uses mixed points for two of the three sets through the heavy point
      - `Refuted.circuitAgainstTheWorld0CanonicalStart` · Refuted · **circuit against the world-0 canonical start** (old: cx44_0)
      - `Refuted.unconfirmedWitness` · Refuted · **unconfirmed witness** (old: cxE): named as a witness once; not confirmed
    - `Refuted.ruleFixingTheWorldOfASet` · Refuted · **rule fixing the world of a set** (old: family B): kills: world 0; rows in 951/DEAD_ENDS.md section B
      - `Cex.paschConfiguration14GatesHeavyPoint` · Counterexample · **Pasch configuration, 14 gates, heavy point** (old: pasch_s14_heavy_atmostone.json): kills 'at most one world-0 set through a heavy point'
      - `Cex.fiveInputCircuitWhereOnlyALightPointWorks` · Counterexample · **five-input circuit where only a light point works** (old: ess_rand_clean_744.json): n = 5, 9 gates; violates no fact of a minimal counterexample that scaffold tested
      - `Cex.adversaryAgainstTheGeneralWorldLaws` · Counterexample · **adversary against the general world laws** (old: ADV4)
      - `Refuted.threeCounterexamplesToGateDependenceOnTheNOTGate` · Refuted · **three counterexamples to gate dependence on the NOT gate** (old: cx3_counterexample, CrossWorld, CrossWorldCex): Lean files CrossWorld.lean, CrossWorldCex.lean
      - `Refuted.crossWorldDisjointnessAtEveryWorld1Point` · Refuted · **cross-world disjointness at every world-1 point** (old: D1): refuted, 4 collisions in 31,587 circuits
      - `Refuted.heavyFirstStep` · Refuted · **heavy-first step** (old: F6): 'a heavy point exists => some heavy point satisfies the step'; refuted
      - `Refuted.noMixedZeroPoints` · Refuted · **no mixed zero points** (old: NoMixedPrice): refuted in the plain form
      - `Refuted.mergeSetLawWithoutItsTwoConditions` · Refuted · **merge-set law without its two conditions** (old: S1): false
    - `Refuted.countingOverPureClassesForAllCorrectCircuits` · Refuted · **counting over pure classes for all correct circuits** (old: family C): kills: disjoint representatives over pure classes; rows in 951/DEAD_ENDS.md section C
      - `Cex.twoTwoWorldSetsSharingOneMergeGate` · Counterexample · **two two-world sets sharing one merge gate** (old: cxMU_dd, cxMU_clean2, cxMU_clean2_DD): n = 7, 36 gates; pure classes cover 5 < 6; loses the certificate game
      - `Cex.paschConfigurationWithADoublyServedClass` · Counterexample · **Pasch configuration with a doubly served class** (old: tri_all_5593.json): kills the looseness lemma
      - `Cex.two4SetsWithJunk` · Counterexample · **two 4-sets with junk** (old: cx44_1_junk.json): loses the certificate game
      - `Refuted.firstAndSecondClassMenus` · Refuted · **first and second class menus** (old: Menu1, Menu2): two lists of allowed classes; star separation fails over both
      - `Refuted.peeling` · Refuted · **peeling** (old: PEEL, E2): remove one set at a time keeping a free class; refuted over every menu tried
      - `Refuted.incrementAvoidingAllFreePoints` · Refuted · **increment avoiding all free points** (old: INC_N): refuted, deficit 1
      - `Refuted.loosenessLemma` · Refuted · **looseness lemma** (old: LOOSENESS, A4): after fixing the free classes every arc-consistent class extends; refuted
    - `Refuted.countingOverRealMergeSetsWithoutMinimality` · Refuted · **counting over real merge sets without minimality** (old: family D): kills: disjoint representatives over real merge sets; rows in 951/DEAD_ENDS.md section D
      - `Cex.starOfFourPairsWithAThresholdNOTInput` · Counterexample · **star of four pairs with a threshold NOT input** (old: STAR4, star4.json; STAR4b, star4b_threshold.json): real merge sets cover 2 < 3 (threshold crossing)
      - `Cex.selectorPath` · Counterexample · **selector path**: kills bounded augmenting for all correct circuits
      - `Cex.innerProductJunkDesign` · Counterexample · **inner-product junk design** (old: cxr): kills 'later merge gates of different sets are disjoint'
      - `Refuted.fullChargingWithoutTheCone` · Refuted · **full charging without the cone** (old: ChargeOK): refuted, 3 counterexamples
      - `Refuted.acyclicForcingInGateOrder` · Refuted · **acyclic forcing in gate order** (old: P2): refuted
    - `Refuted.inductionOneInputAtATimeForAllCorrectCircuits` · Refuted · **induction one input at a time for all correct circuits** (old: family E): kills: the point step; rows in 951/DEAD_ENDS.md section E
      - `Cex.fanoFormulaWithAnUnusedNOTGate` · Counterexample · **Fano formula with an unused NOT gate** (old: FANO-FORMULA, fano_formula.json): 17 gates; kills point deletion
      - `Cex.pappusConfigurationWithJunkGates` · Counterexample · **Pappus configuration with junk gates** (old: PAPPUS-JUNK, pappus_junk_gain.json): n = 9, 66 gates; kills the point step for one-face witness gates
      - `Cex.twinBalancedORTreesWithLeafJunk` · Counterexample · **twin balanced OR trees with leaf junk** (old: TWIN-TREE, twin_tree_f2step.json): n = 14, 28 gates; kills the point step for real-witness gates; every cube is local
      - `Cex.twinTreesWithTheNOTGateRead` · Counterexample · **twin trees with the NOT gate read** (old: TWIN-TREE-N, twin_tree_N_f2step.json): 30 gates; the NOT gate reads one input
      - `Cex.matchedTwinTreesWithA14InputNOTInput` · Counterexample · **matched twin trees with a 14-input NOT input** (old: MATCH-C, nonlocal/match_c_k7.json): n = 16, 55 gates; kills the step at a non-local cube under R1 to R5' and R+; has a gate-saving rewiring; certificate game won
      - `Cex.junkCircuitWhereALightPointFails` · Counterexample · **junk circuit where a light point fails** (old: JUNK, junk.json)
      - `Cex.fiveInputGapForSeenGates` · Counterexample · **five-input gap for seen gates** (old: see_gap_n5.json): n = 5, sets {0,1}, {1,2,3,4}, {0,2}, h = x1 or x4, cube Q = {0}: at v = 1 only 2 of the 3 gates of F2(Q) are 1 at Q + e_v (cost 3) while the step holds; the third gate x2 or x3 dies because all its witnesses come from the one set through v (K3). Why the count needs the K3 term (dwV8p)
      - `Refuted.variantsOfTheTwinTreesWithATwoOrThreeInputNOTInput` · Refuted · **variants of the twin trees with a two- or three-input NOT input** (old: OR2, AND2, MAJ3): nonlocal/twin_tree_{or2,and2,maj3}.json; the step fails for one-face and real-witness gates only
      - `Refuted.junkCircuitAgainstTheLeastInfluenceRule` · Refuted · **junk circuit against the least-influence rule** (old: JUNK2)
    - `Refuted.localOrMemorylessArgument` · Refuted · **local or memoryless argument** (old: family F): kills: gate elimination step; rows in 951/DEAD_ENDS.md section F
      - `Refuted.memorylessPotential` · Refuted · **memoryless potential** (old: S4): increments above 1
    - `Refuted.methodFromOutsideCircuits` · Refuted · **method from outside circuits** (old: family G): kills: one NOT gate saves nothing on Boolean sums; rows in 951/DEAD_ENDS.md section G
    - `frontLanes` · Definition · **front lanes** (old: A1, A2, B8, C3, N2): labels of work lanes and of items inside other sessions' notes, not mathematical objects
  - `section WitnessCircuits` · Section · **witness circuits** (old: 951/data/witnesses): correct circuits that refute a route; none refutes the statement
  - `section CheckedInLean` · Section · **checked in Lean** (old: 951/lean/PEqualNP/W951): statements the Lean checker accepted
    - `small3_bound` · Theorem · **small3_bound**: the statement when every set has at most 3 points
    - `bound_of_noDD` · Theorem · **bound_of_noDD**: TwoWorld.lean: the bound when no output is in two-world normal form
    - `partial_bound` · Theorem · **partial_bound**: PartialBound.lean
    - `PartialBound` · Module · **PartialBound.lean**
  - `no_minCE` · Theorem · **no_minCE**: the one unproved declaration under L-meta-951
  - `section GeneralCircuitsProgram` · Section · **general circuits program** (old: L-gen, GeNeRALIZE, BoolSumNot, C4, K13, K2): the NOT gate ladder above rung 1; names live in lean/PEqualNP/General and notes/general
