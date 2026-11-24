# twh_fableA.md — agent A (merge-record angle), restart-safe log

## A0 (note) RETARGET
Coordinator update: fixed 1/2-1/2 coin rule / TWO-WORLD HALL is REFUTED (w9/tw/cxtw3c.json). New target for this angle:
free-choice FracMatch / MatchG under the sorry's hypotheses (incl. no Theorem-X zero-set family), circuit-dependent choice.

## A1 CHECKED (independent evaluator w9/fa/lib.py, t1.py)
cxtw3c: n=9, s=34: correct on all 512 inputs, C0 wrong, C1 wrong. All units light, all 4 sets hard.
Union-find merge records (exactly d merges per system, each joins 2 blocks):
 canonical (z_Q, unit atoms): M = {m_i, o_i} private.  R* (z_S, atoms z+e_u): M_i = {27 (G = x0|T), o_i}: gate 27 is a MERGE
 for all three triples in the SAME world. So "a gate merging for >=2 systems of one world forces other single-use gates" is FALSE
 in the R* world (T, the other input of G, has a single point per set and nothing in its cone is counted).
cx1/cx2/cx3: canonical merges shared (cx2: gates h=11, g2=13 merge for all 3 triples), R* merges private.
cxr: both sets are EASY (h(z_S)=0); canonical and R* have the same z = z_S and differ only in atoms (e_u vs z+e_u).

## A2 PROVED: crossing lemma + THEOREM X+ (generalised Theorem X: fat atoms, zero points in U1, one-sided)
Notation: U0={h=0} (down-set), U1={h=1} (up-set). x<=y is CROSSING iff x in U0 and y in U1.
(A2.1) If x<=y is not crossing then every wire has w(x)<=w(y) in the real circuit. [N(x)<=N(y); induction over gates.]
       If the wire is not downstream of N this holds for all x<=y.
(A2.2) Systems s_a=(z_a; atoms p_u, u in S_a; K_a), s_b likewise (Lean TestSys: p_u∩Zero(z_a)={u}; Good: N(z_a)=1 or <=1 atom with
       N=1, K=all gates; or, for a set whose output is not downstream of N, K=gates not downstream of N ["mono"]).
       BLOCKED set P(a|b) = {u in S_a : p_u ∩ Zero(z_b) != {}  or  (p_u in U0 and z_b in U1 and neither system is mono)}.
       Then every wire g in K_a∩K_b with g(z_b)=0 has B_a(g) := {u: g(p_u)=1} ⊆ P(a|b).  [u unblocked: p_u<=z_b non-crossing.]
(A2.3) THEOREM X+: if for every pair a!=b:  |P(a|b)|<=1 or |P(b|a)|<=1, the counted sets are pairwise disjoint (GapG), so s>=base.
       Theorem X is the special case z=z_Q in U0 (or all units heavy), unit atoms: P(a|b)=S_a∩Q_b.
CHECKED (w9/fa/xplus.py, x2.py, x3.py): 734 distinct signatures (sets, truth table of h, which outputs are downstream of N) from
 chk/c.jsonl, /tmp/w5ess.jsonl, w7/bad*.jsonl, w6B/*.jsonl, cx1, cx2, cx3, cxr, cxtw3c:
   708 have a Theorem X family; of the 26 that have NONE, 25 have an X+ family (minimal atoms e_u or e_u+1_M, M a minterm of h),
   among them cx1, cx2, cx3. Applying the X+ choice to all 302 data circuits of those 25 classes: counted sets disjoint and >= d, 0 violations.
   The single class with neither: n=5, S_a={0,2,3}, S_b={1,2,4}, h=x0|x1 (w6C/cross5f, 56 circuits): two triples -> Hall by L4 (and by A4 below).
 => In all data, "no Theorem X family" + "no X+ family" + "more than 2 sets" never occurs.  The sorry's case shrinks to: no X+ family.
 Function level (x4.py, random h with <=5 minterms of size <=3, all sets N-sets): share of classes with neither X nor X+ family:
   cross {023},{124}: 386/4123; sunflower3: 4400/14204; triangle: 5165/24124.  So X+ is far from covering everything at h-level.

## A3 PROVED: pair-budget lemma for merge records
Union-find over the gates in order for one system (z; atoms): a gate g with g(z)=0 whose B(g) meets two blocks merges them.
Exactly d = |S|-1 merge gates M (each OR, joins exactly two blocks), all counted.
LEMMA: #{g in M_a : g(z_b)=0} <= (|P(a|b)|-1)^+, in particular |M_a ∩ cnt_b| <= (|P(a|b)|-1)^+ .
 [such g has B_a(g) ⊆ P(a|b) by A2.2 and joins two blocks both meeting P(a|b); the number of blocks meeting P(a|b) starts at |P|,
  never increases, drops at each such merge.]  Theorem X / X+ = the case |P|<=1.
COROLLARY (quantitative Theorem X): for any Good systems, s >= |∪ M_w| >= base - Σ_{a<b} min((|P(a|b)|-1)^+, (|P(b|a)|-1)^+).

## A4 PROVED: SANDWICH CLASSES (system-free; no test systems, no Good, no use of "one NOT" except: output gate is AND/OR)
For each set a let  L_a = {gates g : g <= o_a on ALL inputs, g(e_u)=1 for >=2 u in S_a},
                    U_a = {gates g : g >= o_a on ALL inputs, g(z_{S_a})=0},     P_a = L_a ∪ U_a   (o_a lies in both).
(1) The P_a are pairwise disjoint.  [g in L_a∩L_b: two units of S_a lie in S_b. g in U_a∩U_b: o_b(z_{S_a})=1 since S_b ⊄ S_a.
    g in L_a∩U_b: o_b <= g <= o_a gives S_b ⊆ S_a.]   Hence  s >= Σ_a |P_a|.
(2) |P_a| >= min(d_a, 2).  [|S_a|=2: o_a.  o_a = p∨q: p,q <= o_a, B(p)∪B(q)=S_a for B(x)={u in S_a: x(e_u)=1}; an input wire has
    |B|<=1, and p != N because p(0)<=o_a(0)=0 < N(0); so the input with |B|>=2 is a gate in L_a (if |S_a|>=3).
    o_a = p∧q: p,q >= o_a; one of them, l, is 0 at z_{S_a}; l is not an input (x_v >= OR(S_a) impossible); l is a gate in U_a
    (l = N is allowed: N is a gate).]
(3) COROLLARY (THEOREM T3): if all |S_w| <= 3 then s >= base, for every circuit over AND/OR(/NOT) whose output gates are AND/OR.
    In Lean-system form (circuit-dependent rule!): OR-output set -> z = 0 (Q=[n]), unit atoms; AND-output set -> z = z_S, atoms z+e_u;
    each set is matched to o_a and the input of o_a described in (2).
(4) More generally |L_a| >= (kappa-1) + q where, in the OR-closure of o_a (wires reached from o_a through OR gates only), the leaves
    have unit blocks B(leaf); kappa = number of connected components of the hypergraph of leaf blocks on S_a, q = number of leaf
    gates with |B| >= 2.  And |U_a| >= 1 + (number of gates on a zero-at-z_S AND-chain below o_a, plus its first OR gate).
    Residual demand r_a = d_a - |P_a| is positive only if |S_a| >= 4 and the lower/upper closures end in a "mixed cut"
    (an AND below ORs with >=3 unit points, or an OR below ANDs).
CHECKED (w9/fa/sand.py, truth tables of all wires): 12,126 circuits (all data files + cx1, cx2, cx3, cxr, cxtw3c): P_a pairwise
 disjoint in all; |P_a| >= d_a for every set of size 2 (54,305 sets) and 3 (4,137 sets); the ONLY short sets in all data are the
 five AND-output 4-sets of cx1 and cx3 (P_a = {o_a, k_a}, d_a = 3). cxr: both 4-sets have |L_a| = 4.
CONSEQUENCE FOR THE PROJECT: every data circuit except cx1 and cx3 is VACUOUS evidence for any Hall-type statement (the sandwich
 classes alone give a perfect matching). All real content starts at |S| >= 4. Two-world/canonical/R* statistics on triples say nothing.

## A5 PROVED: two-set Hall under small blocked sets
Systems for a,b with |P(a|b)| <= 2 and |P(b|a)| <= 2, and b's atoms meeting S_a in at most one atom (e.g. unit atoms), same for a:
 |cnt_a ∪ cnt_b| >= d_a + d_b.  [I = cnt_a∩cnt_b; every g in I has B_a(g) = P(a|b), so at most one g in I is a merge of a:
 |cnt_a| >= d_a + |I| - 1, same for b, union >= d_a+d_b+|I|-2. If |I| = 1 and the union is short, both sets are tight
 (cnt = M), then all counted gates of a lie in the pure-OR tree under o_a, hence in L_a, contradiction with A4(1).]

## STATUS / GAP (agent A)
Two-world Hall: REFUTED (cxtw3c, verified independently in A1). Not provable by merge records: in the R* world one gate can be a
merge for arbitrarily many systems with no compensating gates.
Remaining gap after A2-A5: sets of size >= 4 with positive residual r_a (A4(4)); need r_a further gates per set, pairwise
distinct and outside ∪ P_b. Known tools for the residual gates: X+ (A2.3) and pair budgets (A3). No rule proved for the residual.
