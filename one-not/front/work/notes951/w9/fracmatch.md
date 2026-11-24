# FracMatch (front, 2026-11-24)
Lean: lean/PEqualNP/W951/FracMatch.lean, no sorry, axioms propext/choice/Quot.sound only.
- def FracMatch: per set w, finitely many TestSys σ w j with weights lam ≥ 0 summing to 1 and sets
  M w j ⊆ cnt(σ w j), |M w j| ≥ |S w|-1; every wire load ∑_w ∑_j lam·[g ∈ M w j] ≤ 1.
- bound_of_fracMatch: FracMatch ⇒ base ≤ #gates.   fracMatch_of_matchG: MatchG ⇒ FracMatch.
- With one system per set, fractional = integer (bipartite b-matching polytope is integral); only mixing over
  zero points adds power. Dual: for every gate price π ≥ 0, Σ_w min_σ (sum of the |S_w|-1 cheapest π in cnt_σ) ≤ Σ π.
Data (w9/fraclp.py, LP over maximal counted sets from w8/allsys.menus; L* = min max load, need ≤ 1):
- cx1 0.41 (cone 0.55), cx2 0.55, cx3 0.50 (cone 0.53), cxr 0.55: canonical-Hall counterexamples have big fractional slack.
- badT (63 hardest, cone menus): all ok; 57 have L*=1 only because a size-2 set's sole counted gate is its own output.
- k4worst: 0.2.
- scaffold (04:00): FracMatch in its chain. Triple-heavy essential dumps (sunflower base+8..11, Pasch, two triples; 1,767):
  0 with L*>1; canonical and R* OK on all. L*=1.0 in 949 (0.4-0.6 ~240, 0.667 426, 0.75-0.857 ~135).
  Front re-checked scaffold's example (sunflower s=16): sets 0,1 each have ONE maximal counted set of exactly 2 gates
  ({15,16}, {17,19}, private), so load 1 is forced by a single set, not a conflict. L*=1 = tight-by-necessity.

## Fixed averaging rule "coin-flip NOT" (front, 04:10)
Rule: every set uses canonical (smallest Good zero set, cone, unit atoms; N=1 world for hard N-sets) with prob 1/2 and
R* (z = z_S, K=all, unit atoms; N=0 world for hard sets) with prob 1/2. For easy sets both coincide (Q=S).
mixrule.py (LP, min max load): cx1 0.667, cx2 0.75, cx3 0.75, cxr 0.667 (a=0.4/0.6 also <1).
badT 63, bad 160, c.jsonl 2321, w5ess 4083: worst 1.0 (forced private gates), no failures. k.jsonl running.
Equivalent combinatorial target ("two-world Hall", fractional = integral for bipartite b-matching):
 for all families F_c, F_r of sets:  2·|∪_{w∈F_c} Dc_w ∪ ∪_{w∈F_r} Dr_w| ≥ Σ_{F_c}(|S_w|-1) + Σ_{F_r}(|S_w|-1).
 F_c = F_r = F gives: gates counted by F in EITHER world ≥ Σ_F (|S|-1).
Why plausible: canonical loses only on merges above h (x_c∨h, h; AND-cut k ⊇ N), and those are 1 at z_S when h(z_S)=1,
 so never counted by R*; R* loses only on OR-cut junk k = N∧(...), which canonical sees. Each world covers the other's cut.

## 04:27 REFUTED (verified by front): fixed 1/2-1/2 coin rule / two-world Hall
w9/tw/cxtw3c.json (n=9, s=34, base 7; correct, clean, read, C0 and C1 wrong): mixrule a=0.5 → 1.5, a=0.3 → 2.1, a=0.7 → 1.0.
Canonical alone matches (bmatch 7 = base); free-choice FracMatch L*=1.0 (survives). Mechanism: R*-world gate G = x0 ∨ T
(T <= h, no N) is a merge for every sunflower triple. Caveat: has a Theorem X family (outside the sorry's case).
Details: w9/twoworldhall.md (T2). Open: free-choice FracMatch under the sorry's hypotheses.

## 04:40 PROVED (Fable B, checked line by line by front): T1, 951 for all |S_w| <= 3
Clean circuit (no two wires equal as functions, no constant wire), one NOT, all |S_w| <= 3 ⇒ integral free-choice MatchG with
B3 systems Σ(z) (atoms z+e_u, K = all gates) ⇒ s >= base. Proof (w9/twh_fableB.md T1): each set takes o_w; a triple needs 1 more:
OR-top o=A∨B: at z=0 one child A is 1 on 2 units of S_i, A <= OR(S_i): "dedicated", distinct across triples (|S_i∩S_j|<=1).
AND-top o=A∧B: A,B >= OR(S_i) gates; star-forest lemma: in the graph of pairs {A_i,B_i} every edge has a degree-1 endpoint
(else x = e_u ∨ e_v, u ∈ S_j\S_i, v ∈ S_k\S_i gives o_i(x)=1). Leaf L_i >= OR(S_i), non-constant ⇒ L_i(z)=0 for some z vanishing
on S_i ⇒ L_i ∈ cnt_z(i). Dedicated, leaves, outputs pairwise distinct (OR(S_j) <= g <= OR(S_i) ⇒ j=i, g ≡ o_i, unclean).
General sizes: matching saturating min(d_w, 2) per set. CHECKED on 900+ clean circuits. cx2, cxtw* are all-triple: never 951
counterexamples. Remaining gap: 3rd+ gates of sets with |S| >= 4 (G1: pair-sensitive input below a leaf; G2: AND-cut below a
dedicated gate; star forest again if h = 0 on weight <= 2).

## 04:55 Fable B continuation (T3 PROVED; |S|<=4 reduced to two configurations, open)
T3: private classes D_i (g <= OR(S_i), >=2 units) and P_i (g >= OR(S_i), g ≢ 1, not >= OR(S_j) for j≠i) are pairwise disjoint;
private-frontier lemma (AND-top: some OR gate reached via ANDs only is in P_i); matching saturating min(d_i, m_i),
m_i = max_z |Π_i ∩ cnt_z(i)| >= 2 for |S|>=3 (reproves T1). 4-set fully served if |D_i|>=3 or two P_i gates share a zero.
Open for |S|<=4: (I) OR-top with A = P∧Q ∈ D_i (>=3 units), D_i = {o_i, A}; (II') AND-top o = R∧C, R = P∨Q ∈ P_i, C shared
or zero-disjoint. Partial: relative dedicated classes D_i^v at z = e_v (rescue cx1/cx3), not function-level private;
star forest for (I) if h = 0 on weight <= 2. Facts list F1-F10 for Lean in w9/twh_fableB.md.

## 05:00 Fable A final (w9/twh_fableA.md)
- cxtw3c refutation of two-world Hall re-confirmed independently (gate G = x0 ∨ T merges all triples in the R* world).
- A4 PROVED (independent T1): sandwich classes L_a (g <= o_a, >=2 units) ∪ U_a (g >= o_a, g(z_S)=0) pairwise disjoint,
  |P_a| >= min(d_a,2). Checked 12,126 circuits: only short sets in ALL data are the five AND-output 4-sets of cx1/cx3.
  So almost all data is vacuous for Hall statements; real content is |S| >= 4 with a "mixed cut".
- A2 Theorem X+ PROVED (blocked sets P(a|b) with crossing pairs; one side suffices ⇒ GapG). A3 pair-budget lemma PROVED:
  s >= base − Σ_{a<b} min((|P(a|b)|−1)^+, (|P(b|a)|−1)^+). A5 two-set Hall PROVED under |P(·|·)| <= 2.
- Gap: residual r_a = d_a − |P_a| gates for |S| >= 4 below a mixed cut (AND under ORs with >=3 units, or OR under AND chain).

## 05:10 Fable B round 3
- (I) is REAL in a clean hard-case circuit: w9/fb/cfgI.json (cx1 variant, s=25, base 7, no Theorem X family); FracMatch L*=0.35.
- Conflict lemma (PROVED) for relative classes D_i^v (counted in Σ(e_v)): same-v disjoint; D_i^v ∩ D_k ≠ ∅ ⇒ v ∈ S_k;
  ∩ P_k only for pairs; different heavy v,v': collision ⇒ v ∈ S_k, v' ∈ S_i. (II') with shared C: admissible v = {v : C >= x_v}.
- Not enough: function-level privacy regresses one region per level; needs a GLOBAL potential / induction. x_v=1 induction dead.

## 05:20 Fable C (adversary) final, w9/twh_fableC.md
- cxE (w9/fc/cxe3.json, n=7, s=45, base 10): coin rule fails (1.5) INSIDE the sorry's case (no pairwise zero-set family,
  5 hard N-sets, DD exists). Front re-verified: correct, clean, read, C0/C1 wrong, coin 1.5, free-choice FracMatch 0.4545.
- Free-choice FracMatch: no counterexample. Exhaustive SAT pool encodings UNSAT (triangle s=7..13, Pasch s=9,10, two 4-sets s=8,9).
- Function-level two-world Theorem X (PROVED) — obstruction common in data, so proofs must read gates.
- Rules with 0 failures on all data: RULE-AC (canonical unless a canonical-counted gate is shared, then R*), RULE-3.
- Relative sandwich rule: L_rel <= 1.0 on all, no collisions; next attack: triangle of 5-sets with shared relative merge tree.

## 05:35 Fable E final (w9/twh_fableE.md) — R0' checked by front
- R0 (PROVED, front re-checked): if at most one set through v has size >= 3, x_v := 0 kills >= deg(v) gates (every reader of
  x_v dies: AND-reader → const 0, OR-reader → copy of its other input; plus the pair outputs; the extra one for the big set from the
  "x_v ∨ x_{u_j} only" contradiction). Base drops by exactly deg(v). R0': with small3, 951 holds for every system whose CORE
  (iteratively delete points in <= 1 set of size >= 3) has no 4-set. Minimal counterexample: every point in >= 2 sets of size >= 3.
  cx1, cx3, cfgI, cxr are all outside the open core. Smallest open systems: n=8 {1234},{156},{257},{367},{458},{268} (base 13); 4x3 grid.
- E0.1 conflict lemma for relative sandwich classes; heavy-point bound s >= 1 + Σ_{w∌v} d_w + Σ_{w∋v}|P_w|.
- Refuted as methods: A3 on Σ(e_v); one-variable induction without stronger hypothesis. Conjecture ★ (gates outside J^L ∪ J^U >= base).

## 05:50 Fable C follow-up (w9/twh_fableC.md C9, C10)
- cxT4 (w9/fc/cxT4.json; n=15, s=47, base 15; front re-verified correct/clean/read/C0,C1 wrong): triangle a={p,r,a1..a4},
  b={p,q,b*}, c={q,r,c*}, h=p|q|r, shared tree t. Relative sandwich rule (C's reading) FAILS: L_rel 1.333. Free-choice FracMatch
  L* = 0.44 (all-gate and cone). Not a core system (private points have degree 1), so irrelevant to 951 via R0'.
- Two 4-sets {0123},{0456}: exhaustive pool SAT UNSAT (h = x1x2|x4x5 s=9..12; maj|maj s=10..12; free h s=8,9).
- Frontier for FracMatch: >= 3 sets, mutual clash >= 3, h thin on both sides.
- CORRECTION (tractability, 05:10): under the rule as actually implemented (z = ANY point vanishing on S_w of weight <= 2,
  h plays no role; P_w = function-level private-above class), cxT4 gives L_rel = 0.706: the relative sandwich rule is NOT refuted.
  C's 1.333 refutes only the restricted reading (z = 0 or minimal 1-points of h).
