# srepay_referee.md — referee report on w9/srepay_opus.md (claims marked PROVED)
Code (independent of analyze.py / bt.TT): w9/srepay_ref/ref.py (checker), adv.py (random constructed circuits), extra.py (genH5, inter,
abstract Lemma J, cut formula), whole.py (whole-class V1/V2), sat_rerun.log. All circuits verified correct by truth table; "ess" = C0 wrong and C1 wrong.

## Definitions (as used, made precise)
One-NOT circuit, s gates incl. N = ¬h; sets S_w, |S_a∩S_b| <= 1, d_w=|S_w|-1, base=Σd_w. M = lifted monotone circuit (N -> input y), s-1 gates.
Assume h(0)=0. V = wires of M with value 0 at (0,1) (i.e. C1(g)(0)=0). B(g) = {u in V' : C1(g)(e_u)=1}, V' = ∪S_w, B_w(g)=B(g)∩S_w.
Joint union-find on V' / per-set union-find on S_w, over gates of V in circuit order; an OR gate g=s∨t in V is a joint merge (g in J) if B(s),B(t)
are nonempty and in different joint blocks; a w-merge (g in M_w) likewise with B_w and the per-set blocks. k_g=#{w: g in M_w}, coll=Σ(k_g-1)^+,
X = J \ ∪M_w. H = hypergraph (V',{S_w}), c = #components, cyc(H) = base-(|V'|-c) = cyclomatic number of the incidence graph (>=0; =0 iff
Berge-acyclic = "hyperforest"; two sets with |∩|<=1 are a hyperforest). out = #gates of M outside ∪M_w.

## Verdicts
R1  §0 V1 => s-1 >= base; V2 identity out-coll = (s-1)-Σ|cl_w|.                                              CORRECT (trivial algebra).
R2  §1(a) two sets: maxflow = min(base,|U|); V1 <=> s-1 >= base for every choice.                            CORRECT. (cuts: ∅ -> base, {a} -> d_b+|cl_a| >= base,
     {a,b} -> |U|.) Consequence: V1 for two sets has NO content beyond the bound. For >= 3 sets "every choice" is NOT automatic (abstract
     example: classes {g1,g2},{g1,g2},all: def 2 > out 0 with s-1 > base); the log does not claim it.
R3  §1(b) LEMMA J: h(0)=0 => |J| >= |V'|-c, hence s-1 >= |V'|-c.                                             CORRECT. Steps checked: F_w(0,1)=C1_w(0)=o_w(0)=0 (0 in U0);
     F_w(e_u,1) >= o_w(e_u)=1; inputs x_v in V with |B|<=1, y not in V; OR in V => both children in V; AND in V => a child in V (Z is one
     point) and B(AND) ⊆ B(child); invariant "B(g) in one joint block"; each OR joins <= 2 blocks; final blocks <= c. Outputs are gates != N.
     h(0)=1 case: h ≡ 1, N ≡ 0, C0 monotone and correct: needs the classical monotone bound (Lean: NOT-dead case). Fine.
     Sharpening (referee): |J| <= |V'|-1 always, so for CONNECTED H: |J| = |V'|-1 exactly and base-|J| = cyc(H) exactly.
R4  §1(c) hyperforest => s >= base+1 (two complementary 4-sets, any h: s >= 7).                              CORRECT. Scope: circuit CONTAINS a NOT (s counts N; M has
     s-1 >= |J| >= base gates). Without NOT only s >= base (monotone). So 951 holds on Berge-acyclic systems, with +1 when a NOT is present.
     (Not new as a bound: cores are never hyperforests; R0' already covers them. New only as a direct proof.)
R5  §3 |M_w| = d_w exactly; per-set blocks refine joint blocks; description of X.                            CORRECT.
R6  §3 IDENTITY Σ(j_g-k_g) = |J|-base >= -cyc, and (CHARGE) |X| >= coll + #(∪M_w \ J) - cyc.                 CORRECT, but it is an exact REWRITE of Lemma J:
     |X| = coll + #(∪M_w\J) + (|J|-base)  (identity, verified on every circuit). No information beyond R3.
R7  §3 "hyperforest: coll <= |X| <= out. S-repay PROVED."                                                    CORRECT WITH FIXABLE GAP (statement scope).
     What is proved: for the specific selection cl_w := M_w (a d_w-subset of the type-1 class Z=↓(0,1), unit atoms), coll <= |X| <= out.
     Since out-coll = (s-1)-base for this selection, the statement is EQUIVALENT to s-1 >= base, i.e. to R4; derivation of the bound:
     s-1 = |∪M_w| + out >= (base-coll) + |X| >= base  => s >= base+1 (the +1 is N, which is not a gate of M; needs a NOT and h(0)=0, else R3's
     h(0)=1 remark / monotone bound). Fix: state it as "S-repay for the merge-set selection"; it is NOT S-repay for whole classes (V2) nor for
     "an optimal ClassFrac solution" (s_fable S5). Verified failure of the whole-class reading on a hyperforest: w9/srepay_ref/v2whole_cx.json
     (n=4, sets {0,1,2},{1,3}, s=20, correct, essential): Σ_w|cl_w| = 20 > s-1 = 19 for the same configuration (1532/2766 random forest
     circuits have Σ|cl_w| > s-1). V1 with whole classes held on all of them (not proved for >= 3 sets).
R8  §3 "951 <=> #(gates of M not in J) >= base-|J| (<= cyc)".                                                CORRECT WITH FIXABLE GAP (off by one + tautology).
     s-1 = |J| + #nonJ, so the right side is <=> s >= base+1, not s >= base. Correct forms: "s >= base+1 <=> #nonJ >= base-|J|" (per circuit,
     h(0)=0, NOT present), or "951 <=> #nonJ >= base-|J|-1". Only "<=" holds for 951 as written. It is a restatement, not a reduction: for
     connected H it reads "#(gates that are not joint merges) >= cyc(H)" with |J| = |V'|-1 forced.
R9  §3 "Structure: a double merge needs BOTH children mixed; mixedness is created only by cross merges".     WRONG as stated for intersecting sets (fixable).
     True part: g=s∨t in M_a∩M_b => B(s),B(t) each meet S_a and S_b (0 violations). False part: a child can be the INPUT x_u, u in S_a∩S_b,
     which is "mixed" with no cross merge below it. Counterexample (hyperforest, correct, essential): w9/srepay_ref/inter_input_child.json,
     S_a={0,1,2}, S_b={0,3,4}, h=Th_2, gate x0 ∨ (x1∨x3) is a double merge with child x0 (519 of the random essential forest circuits of adv.py seeds 1,2; 179 data circuits have a double merge with an input child).
     Fix: "the two children cannot both be inputs; for disjoint S_a,S_b both children are gates above a cross merge". (CHARGE is unaffected.)
R10 hand_H5: coll=3, |X|=4.                                                                                 CORRECT (re-computed).
R11 Barrier remark ("uses only weight <= 1 points, barrier applies only to per-set classes").                CORRECT but should be worded: unit-point arguments are capped at
     |J| <= |V'|-1 < base whenever cyc >= c; Lemma J is exactly the unit-vector bound and reaches base only when cyc=0. No conflict with the
     barrier; equally, NOTHING in §1/§3 can touch a cyclic system (in particular no core system): the missing cyc(H) gates must come from
     inputs of weight >= 2.

## Numerical re-runs
- chkJ.py: reproduced ({'n':2559,'has_coll':199,'cyclic':2491}, 0 J/CHARGE violations).
- ref.py (independent): 2768 circuits (data + g3/cxstar5, cxstar44 + p/cxP1-6 + hand_H1..H5 + srepay/*.jsonl incl. 120 free s=11 solutions and fix_*),
  all correct, 397 essential, 273 hyperforest (101 with coll>0): 0 violations of Lemma J, |M_w|=d_w, proof-step invariants, CHARGE identity,
  hyperforest S-repay, s >= base+1. No circuit with s <= base+1.
- adv.py seeds 1,2: 7688 constructed correct circuits (templates o_w=(P∧K∧N)∨(R∧h), (R∨(N∧P))∧(K∨h), shared mixed OR pools, h=Th_2 / Th_2∨x_v,
  random topological order; 6615 hyperforest, 7386 essential, 755 essential forest circuits with collisions, k_g up to 3): 0 violations;
  min(|X|-coll)=0 on forests (CHARGE tight).
- genH5(k,m) (k disjoint m-sets, column ORs first): coll=(k-1)(m-1), |X|=m(k-1), k_g=k; all checks pass (k,m up to (5,2),(2,6),(4,3)).
- abstract Lemma J (random monotone circuits over (x,y), random outputs vanishing at (0,1), S_w ⊆ B(F_w)): 18144 trials, 0 violations.
- SAT re-run (satgen.py via run_free.py, T2x4, h free): s=8,9,10 UNSAT for all NOT positions (see sat_rerun.log). (CHECKED claim, not refereed
  beyond re-running; the encoding itself was not audited.)
