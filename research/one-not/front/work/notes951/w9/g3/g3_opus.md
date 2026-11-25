# g3_opus.md — task G3 (strengthened hypothesis ★), restart-safe log

## G3.0 Definition fixed (functional, pointwise on ALL 2^n inputs)
A_w := OR(S_w) (truth table). Over sets with |S_w| >= 2 only, a != b:
  J^L = {gates g : ∃ a≠b, g <= A_a ∧ A_b pointwise}    (constant-0 gates included)
  J^U = {gates g : ∃ a≠b, g >= A_a ∨ A_b pointwise}    (constant-1 gates included; N counts as a gate)
★ : for every correct circuit (fan-in-2 AND/OR, <= 1 NOT, all gates counted incl. unread) for a (1,1)-disjoint family,
    s - |J^L ∪ J^U| >= base = Σ(|S_w|-1).   (Outputs are never in J: A_w <= A_b or A_w >= A_b needs containment.)

## G3.1 CHECKED: ★ on all data (w9/g3/star.py, independent truth-table evaluator; all circuits verified correct)
 cx1 slack 14, cx2 10, cx3 14, cxr 11, cfgI 17, cx44_0 12, cx44_1 14, cxT2 9, cxT4 9, cxe3 14, cxtw3 14, cxtw3c 14, cxtw4 17,
 cxtw4c 17, badT (63) min slack 2, bad (160) min 1, chk/c.jsonl (2321) min 1, /tmp/w5ess.jsonl (4083) min 1.  0 violations.
 (|J| reaches 29 in cxtw4: J soaks up most of the junk, as intended.)

## G3.2 PROVED: ★ holds whenever max|S_w| <= 3 (any AND/OR/NOT circuit with AND/OR outputs).
 FableA's sandwich classes P_a = L_a ∪ U_a (A4) are disjoint from J^L ∪ J^U:
  L_a∩J^L: g(e_u)=g(e_v)=1 for u≠v∈S_a and g <= A_c∧A_d gives u,v ∈ S_c∩S_d, |S_c∩S_d|<=1. L_a∩J^U: A_c∨A_d <= g <= A_a forces S_c,S_d ⊆ S_a.
  U_a∩J^U: g(z_{S_a})=0 but A_c(z_{S_a})=1 for the c≠a among c,d. U_a∩J^L: A_a <= g <= A_c∧A_d forces S_a ⊆ S_c and S_a ⊆ S_d.
 So s - |J| >= Σ|P_a| >= Σ min(d_a,2) = base when all |S|<=3.  Any counterexample to ★ needs a set of size >= 4.

## G3.3 PROVED: ★ for MONOTONE circuits (AND/OR only), in the stronger form Σ_a |L_a| >= base with L_a ∩ J = ∅.
 L_a := {gates g : g <= A_a pointwise, g(e_u)=1 for >= 2 u ∈ S_a}  (FableA's L_a).  Pairwise disjoint and disjoint from J (G3.2).
 Claim: in a monotone circuit computing A_a (at some gate), |L_a| >= |S_a|-1.
 Proof. Monotone: g(z_{S_a})=0  <=>  g <= A_a  (if g(x)=1 and x has no 1 on S_a then x <= z_{S_a}, so g(z_{S_a})=1).
  Union-find on S_a over the gates in topological order, for wires Z = {wires w : w(z_{S_a})=0}, block B(w)={u∈S_a : w(e_u)=1}.
  Invariant: for every w ∈ Z, B(w) lies inside one block after w is processed. Inputs in Z are x_u, u∈S_a (B={u}).
  AND gate in Z: some input is in Z, B(g) ⊆ B(that input): no merge.  OR gate in Z: both inputs in Z, B(g)=B(p)∪B(q): merges <= 2 blocks.
  The first gate computing A_a is in Z with B = S_a, so >= |S_a|-1 merging OR gates, each in Z (so <= A_a) with |B|>=2: in L_a. ∎
 Weight >= 2 information used: the high-weight point z_{S_a} (equivalence g(z_S)=0 <=> g <= A_a needs monotonicity on all inputs),
 consistent with the 1-slice constraint (no argument using only 0 and units).
 Consequence: J^L ∪ J^U gates are pure junk in monotone circuits; adversarial search for ★-violations must use the NOT gate.
 Where it breaks with one NOT: gates downstream of N with g(z_S)=0 need not be <= A_a (that is exactly why R*/canonical rules fail).

## G3.4 PROVED: easy-set merge class (any one-NOT circuit). For a set a with h(z_{S_a}) = 0 ("easy"):
  M_a := {gates g : g(z_{S_a}) = 0, g(e_u)=1 for >= 2 u ∈ S_a}  has |M_a| >= d_a.
  [Union-find of G3.3 over wires zero at z_{S_a}: N(z_{S_a}) = 1 so N is never in Z; AND/OR steps as before; no monotonicity used.]
  M_a ∩ J = ∅ (g(z_{S_a})=0 excludes J^U; two units of S_a exclude J^L), M_a ∩ L_b = ∅ and M_a ∩ U_b = ∅ for b ≠ a (L_b: both
  units would lie in S_b; U_b: A_b(z_{S_a}) = 1).  COROLLARY: ★ holds if at most one set has size >= 4 and that set is easy
  (classes M_a and P_b = L_b ∪ U_b, b ≠ a, pairwise disjoint, sizes d_a and min(d_b,2) = d_b).
  For a HARD set the same argument with atoms z_S + e_u (R*) works for the count (N = 0 at all atoms, empty block), but those
  merges can lie in J^L (they are 1 at z_S+e_u where every other A_c is already 1): exactly T, x0∨T of cxtw.
  Overlaps M_a ∩ M_a' between two easy big sets are not excluded (this is the canonical-Hall problem again).
CHECKED (SAT, w9/g3/sat.py: exists correct <=1-NOT circuit with s gates and #nonJ <= base-1?): UNSAT for
  {0123},{04}  s = 4..10;  {0123},{04},{14}  s = 5..11;  {0123},{045}  s = 5..9 (+ running).  (These are covered by G3.4 when the
  4-set is easy; the SAT run also covers the hard case.)

## G3.5 REFUTED: ★ (as defined in G3.0) is FALSE, with unbounded deficit.  (w9/g3/cxstar.py, cxstar5.json, cxstar44.json)
 Family (m >= 5): S_a = {1..m}, S_c = {0,1}, S_d = {0,2};  base = (m-1)+1+1 = m+1.  h = x0, N = ¬x0.
 Circuit (Shannon split on the shared point p=0):
   N = ¬x0;  o_c = x0∨x1;  o_d = x0∨x2;  K = o_c ∨ x2 ∨ x3 ∨ ... ∨ xm  (OR chain, m-1 gates);  M = N ∧ K;
   R = (x1∧x0) ∨ (x2∧x0) ∨ ... ∨ (xm∧x0)  (m ANDs, m-1 ORs);   o_a = M ∨ R.
 Correct: x0=0 -> M = K|_{x0=0} = OR(S_a), R = 0;  x0=1 -> M = 0, R = OR(S_a).  C0 and C1 both wrong (essential NOT).
 J^U ∋ every K-chain gate (all >= x0∨x1∨x2 = A_c∨A_d);  J^L ∋ all 2m-1 gates of R (all <= x0 <= A_c∧A_d).
 Non-J gates: N, o_c, o_d, M, o_a = 5 for every m, base = m+1:  m=5: 5 < 6 (s=18, cxstar5.json), m=8: 5 < 9.
 Two 4-sets sharing p (cxstar44.json, n=9, base 10, s=29): nonJ = 9 < 10.  Both files verified by star.py AND fa/lib.py verify().
 MECHANISM: S_a is hard (h(z_{S_a}) = 1). Its U1-side (R*) merges x_u∧x0 ∨ ... are <= x0, and x0 lies in two sums ({0,1},{0,2}),
 so they are in J^L; its U0-side (canonical, z_Q with Q = S_a∪{0}) merges are >= A_c∨A_d, so they are in J^U. All of the
 merge work is in J; only the two "glue" gates M, o_a (and the shared N) are counted.
 This is a one-NOT phenomenon only (G3.3: monotone ★ is a theorem).
 SAT (sat.py, n=6, sets {12345},{01},{02}, s=18, nonJ<=5): SAT, an independent second violating circuit found (r3.out) — the
  encoder and the hand construction agree. (s=14: not decided in 140 s.)
 Earlier SAT (all UNSAT, i.e. ★ holds there): {0123},{04} s<=10; {0123},{04},{14} s<=11; {0123},{045} s<=11;
  {0123},{04},{15},{45} s<=9; {0123},{04},{14},{24},{34} s<=8. Consistent: with one 4-set the Shannon trick only reaches slack 0.

## G3.6 CHECKED: the junk ★ was meant to exclude is of the SAME function-level type as the real work in G3.5 (w9/g3/jside.py)
 J^L gates by side of h: cxr 7 (all <= h), cxT2 11 (<= h), cxT4 23 (<= h), cxtw3c 4 <= h + 9 mixed, badT 77 <= h / 10 <= N / 15 mixed,
 bad 107 <= h / 31 <= N / 77 mixed;  J^U: mostly >= h.  cxstar5: J^L 9 (<= h), J^U 4 (>= h).
 So no refinement by "which world" separates junk (cxr, cxT*, cxtw) from the needed R*-merges of cxstar.
 Restricting witnesses to sets of size >= 3 (★_3) defeats this particular Shannon construction (PROVED on paper: the trick forces
 the J^U witnesses c,d to satisfy (S_c ∪ S_d) \ S_a ⊆ S_c ∩ S_d, hence |S_c|,|S_d| <= 2), but ★_3 is not stable under x_v := 0
 (triples become pairs), so it cannot serve as the induction hypothesis; and the restriction step of an induction necessarily
 produces pair witnesses. VERDICT: the strengthened-hypothesis route in the form ★ is dead.
 Possible weaker potential (CONJECTURE, untested beyond research/data/cxstar): nonJ + |J|/3 >= base (in the Shannon design each merge moved
 into J costs >= 3 J-gates: 2 on the J^L side, 1 on the J^U side). Not restriction-stable either as far as I can see.
