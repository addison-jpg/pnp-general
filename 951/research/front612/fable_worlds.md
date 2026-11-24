# fable_worlds: world choice for MergeFrac (L-meta-951, no_minCE)

Status: NO full proof. Result = (1) the right statement is integral (MergeSDR), not K-Rado; (2) three proved
lemmas (cut sandwich, chain-pair, pair theorem) that settle every pair of sets outside one explicit configuration
O2 (which contains config (I)); (3) two new clean/essential adversaries showing that the corpus regularities
(two canonical worlds suffice, shared merges are NOT-free, no mixed conflicts) are artifacts; (4) the smallest open
lemma and exact falsification tests. Labels: PROVED-PAPER / CHECKED-ON-DATA / CONJECTURE / FALSE.
Data = the 163 distinct circuits of supportB/mergefrac_runs.txt (+ ADV3, ADV4 below), computed with w951
systems.system + systems.merges exactly as in mergefrac_runs.merge_menu. Python only, no Lean.

Notation. S = S_w, d = |S| - 1. z a zero point of w (z = 0 on S), atoms z + e_u. B_z[i] = {u in S : wire i is 1 at
z + e_u} for wires i that are 0 at z. M_z(w) = merge gates (Lemma M). m_w(K) = min_z |M_z(w) ∩ K|.
top_w = z_{S_w} (all ones off S_w). C_b = the monotone circuit with NOT := b; g_b = function of gate g in C_b.
One-NOT facts used: h (input of the NOT) is monotone; g_0 <= g_1; g(x) = g_0(x) if h(x) = 1, g_1(x) if h(x) = 0.
Phase of a point = h(x). "N-dependent" = downstream of the NOT.

## (a) Statements and their exact logical relations

- MergeSDR (CONJECTURE; CHECKED-ON-DATA 165/165): there are zero points z_w with M_{z_w}(w) pairwise disjoint.
- MergeFrac (open) <=> weighted dual: for all pi >= 0, sum_w min_z pi(M_z(w)) <= pi(gates).   [LP duality]
- K-Rado (0/1 dual): for every gate set K, sum_w m_w(K) <= |K|.
- MergeSDR => MergeFrac => K-Rado. PROVED-PAPER (point masses; pi = indicator of K).
- K-Rado => MergeFrac is NOT available. Exactly what is needed: with K_t = {pi > t},
    min_z pi(M_z(w)) = min_z ∫ |M_z(w) ∩ K_t| dt  >=  ∫ m_w(K_t) dt,
  and K-Rado only bounds the right side (sum_w ∫ m_w(K_t) dt <= ∫ |K_t| dt = pi(gates)). So one needs the
  chain-minimiser property CMP_w: for every chain K_1 ⊂ K_2 ⊂ ... one z minimises |M_z(w) ∩ K_i| for all i at once
  (true when {M_z(w)}_z is the base family of a matroid; then Rado's theorem also gives K-Rado <=> MergeSDR).
  CHECKED-ON-DATA: {M_z(w)}_z is a matroid base family for all sets on 135/163 circuits; on the other 28 (cfgI,
  cx44, cxT2/T4, chist, P*, all "attack" circuits, HARD4) both the exchange axiom and CMP_w FAIL (exhaustive
  orderings for <= 7 gates, 300 random orderings otherwise). Example cfgI set 0: bases {12,28,33}, {12,13,15}.
  So "optimal duals are 0/1 on 163/163" is an empirical fact with no per-set explanation. Recommendation: target
  MergeSDR (integral, per-set world choice) or the weighted dual; K-Rado alone is only a necessary condition.
- NEW DATA: a disjoint integral choice exists on all 163 circuits (also where L* = 1 and where L* < 1), and
  already inside the two-world menu {0, top_w} per set on 163/163. Pure rule top_w for all w: 152/163; pure rule
  z = 0: 151/163; both fail on cxT2, cxT4 (a pair with a (0,0) and a (top,top) conflict), a mixed choice works.
  The two-world menu is FALSE in general: see ADV3 in (b4).

## (b) What is proved

### b1. Cut sandwich (PROVED-PAPER; CHECKED 107,680 (w,z) pairs on the 14 L* < 1 circuits + ADV3, 0 violations)
For any gate set K let c_z(F) = number of connected components of S under the hyperedges B_z[i], i in F.
    c_z(gates \ K) - 1  <=  |M_z(w) ∩ K|  <=  |S| - c_z(K).
Proof. Each merge gate g joins two blocks; pick x, y in B_z[g] in the two blocks. These d edges form a spanning
tree of S. Edges of merge gates outside K lie inside components of the non-K hypergraph, so there are at most
|S| - c_z(gates \ K) of them; same for K. ∎
The lower bound is tight on only 72,312 of the 107,680 pairs, so it does NOT explain world-independence (fact 2).

### b2. Fact 2 (world-independence of |M_z(w) ∩ K|) is complementary slackness (PROVED-PAPER)
If pi is an optimal dual and mu an optimal primal, mu_w(z) > 0 implies pi(M_z(w)) = min_z' pi(M_z'(w)). Hence
|M_z(w) ∩ K| is z-independent for a 0/1 optimal dual K as soon as every distinct merge set of w is used by some
optimal primal (strict complementarity: this is an iff for a suitable optimal pair). On the 13 circuits K is an
"exact transversal": every menu member of w meets K in exactly c_w gates and L* = sum_w c_w / |K| (cx44: 1+1 of 3;
cx3: 1+1+1 of 4; chist U6: 5+5 of 17). cfgI is the exception only because 4 of the 32 worlds of sets 0, 1 have
positive reduced cost for that pi. There is no structural (cut) reason; I do not see a proof route through fact 2.

### b3. Chain-pair lemma (PROVED-PAPER; CHECKED: 29,127 applicable world pairs on 157 circuits, 0 violations)
Let z be a zero point of w, z' any point with z <= z' (bitwise) and |S_w \ supp(z')| <= 1. Let g be a gate with
g(z) = 0, |B_z[g]| >= 2 (in particular any g in M_z(w)) and g(z') = 0. Then g is N-dependent and there is
u in S_w ∩ supp(z') with h(z + e_u) = 0 and h(z') = 1 (so h(z) = 0: the pair straddles the phase boundary).
Proof. Two points of B_z[g], at most one outside supp(z'): take u in B_z[g] ∩ supp(z'). Then z + e_u <= z',
g(z + e_u) = 1, g(z') = 0. If h(z + e_u) = 1 then h(z') = 1 and g_0(z') >= g_0(z + e_u) = 1, contradiction. So
h(z + e_u) = 0 and g_1(z + e_u) = 1; if h(z') = 0 then g(z') = g_1(z') = 1, contradiction. So h(z') = 1 and
g_0(z') = 0 < g_1(z'), i.e. g depends on the NOT. ∎
Corollaries (PROVED-PAPER):
- C1. z <= z', |S_w \ z'| <= 1, and (h(z) = 1 or h(z') = 0)  =>  M_z(w) ∩ M_z'(w') = ∅ for every w' with z' a zero
  point of w'. Same for counted sets (FracMatch systems with atoms z + e_u), not only merge sets.
- C2 (no mixed conflict on NOT-free gates). M_0(w) ∩ M_{top_w'}(w') contains only N-dependent gates
  (S_w \ top_w' = S_w ∩ S_w', at most one point). On the corpus it is empty for all pairs.
- C3 (staircase). If the sets can be ordered with |S_i ∩ (S_{i+1} ∪ ... ∪ S_m)| <= 1, put z_j = all ones off
  S_j ∪ ... ∪ S_m. Then z_1 <= ... <= z_m, h(z_j) is 0 for j < j0 and 1 for j >= j0, and merge sets can only meet
  for i < j0 <= j, on N-dependent gates. MergeSDR is PROVED when j0 = 1 or h(z_m) = 0.
  CHECKED: 66/164 circuits admit such an order; every such order (<= 200 per circuit) is fully disjoint there.
  Not a theorem: ADV4 below has a staircase order with a conflict.

### b4. Pair theorem and the obstruction O2 (PROVED-PAPER)
For two sets A, B say A -> B is chain-free if there is a zero point z' of B with |A \ z'| <= 1 and
(h(z') = 0 or h(z' \ A) = 1). Then (z_A, z_B) = (z' \ A, z') has M_{z_A}(A) ∩ M_{z_B}(B) = ∅ (C1).
O2(A,B) := neither A -> B nor B -> A is chain-free, i.e. for every zero point z' of B containing all but at most
one point of A: h(z') = 1 and h(z' \ A) = 0; and the same with A, B swapped.
Pair theorem: outside O2 the two sets have disjoint merge sets in explicit worlds. In O2 nothing is proved.
Equivalently: h(y) = 0 for every y off A ∪ B, and h(y ∪ (A \ p)) = 1 for every such y and every p in A with
A ∩ B ⊆ {p} (p is the common point if there is one); and the same with A, B swapped.
Config (I) is O2 (h = x1|...|x6; A \ {0} = {1,2,3} makes h = 1, points off A ∪ B give h = 0). Fact 4 is consistent:
the (0,0) conflict on h is a NOT-free gate at z = z' = 0, where |A \ z'| = 4, outside the lemma.
CHECKED: 803 set pairs in 165 circuits; 78 are O2; proved pairs: 0 conflicts. Among the 78 O2 pairs (top,top) is
disjoint on 70 and (0,0) on 69; the two pairs where both fail are cxT2 {1,2,7,8}/{0,2,3,4} and its cxT4 analogue.

### b5. Where the proof stops (precise obstruction), with three junk gadgets (all PROVED by construction, run in Python)
A proof by a canonical world rule cannot work; each rule dies to a gadget of 3 gates per killed pair:
- G(0,0): a balanced OR tree h over points of both sets; its root is in M_0(A) ∩ M_0(B) (config (I)).
- G(top,top), NOT-free: g = (x_u1 & x_v1) | (x_u2 & x_v2), u_i in A, v_i in B, placed early:
  g in M_{top_A}(A) ∩ M_{top_B}(B). Incomparable worlds, monotone gate, the lemma is silent.
- G(chain), N-dependent: g = ((x_u1 & N) | x_v1) | ((x_u2 & N) | x_v2) with u1, u2 light (h(e_u) = 0):
  g in M_0(A) ∩ M_z'(B) for every zero point z' of B with h(z') = 1. This is exactly the exception in b3.
ADV3 (correct, clean, read, NOT essential; n = 12, s = 43, base = 9; three disjoint 4-sets):
  M_0 = {18,21,27}, {14,19,21}, {15,20,21}; M_top = {25,32,47}, {25,39,50}, {32,39,53}. Every pair conflicts in
  (0,0) (h = g21) and in (top,top). No disjoint choice in the menu {0, top_w}; fractionally, with p_w = mass on 0:
  load(21) = sum p_w <= L and the three junk loads sum to 2(3 - sum p_w) <= 3L, so L >= 6/5 > 1.  [FALSE: two-world
  MergeFrac/MergeSDR.] Full MergeFrac L* = 0.75 (K = {21,47,50,53}, uniform), 2506 disjoint all-world choices,
  e.g. A at 0, B at e_11, C at e_7. FracMatch (lp.fraclp) L = 0.28125.
  {"n":12,"sets":[[0,1,2,3],[4,5,6,7],[8,9,10,11]],"gates":[["or",1,4],["or",12,8],["or",13,5],["or",14,9],["or",2,6],["or",16,10],["or",17,3],["or",18,7],["or",19,11],["or",15,20],["not",21],["and",0,4],["and",1,5],["or",23,24],["or",25,0],["or",26,1],["or",25,4],["or",28,5],["and",2,8],["and",3,9],["or",30,31],["or",32,2],["or",33,3],["or",32,8],["or",35,9],["and",6,10],["and",7,11],["or",37,38],["or",39,6],["or",40,7],["or",39,10],["or",42,11],["or",21,0],["and",27,21],["or",45,22],["or",46,34],["and",44,47],["or",29,22],["or",49,41],["and",21,50],["or",36,22],["or",52,43],["and",21,53]],"outs":[48,51,54]}
ADV4 (correct, clean, read, NOT essential; n = 8, s = 22, base = 6; A = {0,1,2,3}, B = {4,5,6,7}):
  g16 is N-dependent and g16 in M_0(A) ∩ M_{top_B}(B) = a mixed conflict and a staircase conflict.  [FALSE as general
  laws: "shared merges are never downstream of the NOT" (fact 3), "no mixed conflicts", "staircase is disjoint".]
  MergeFrac L* = 1 (forced by g8), a disjoint all-world choice exists.
  {"n":8,"sets":[[0,1,2,3],[4,5,6,7]],"gates":[["or",2,3],["or",8,6],["or",9,7],["not",10],["and",0,11],["or",12,4],["and",1,11],["or",14,5],["or",13,15],["and",16,10],["or",17,4],["or",18,5],["or",19,6],["or",20,7],["or",0,1],["or",10,0],["or",23,1],["and",22,10],["or",11,25],["or",26,2],["or",27,3],["and",24,28]],"outs":[29,21]}
Consequence. The world of a set must depend on the circuit, and worlds strictly between 0 and top_w (ADV3 uses
e_v) are needed. Any proof has to pay for a killed world pair with the gates of the gadget that kills it: that is
the Rado count itself, and I have no proof of it. Per-set world choice (fact 4) is necessary; it is not sufficient
to choose among two canonical worlds, and a pairwise argument cannot close m >= 3 (ADV3 is a triangle).
Caveat on coord's MergeWorld2 / RefinedNoMixedFrac: I tested the menu {0, top_w}; if that target uses another
two-world menu, rerun test F1' below on ADV3 with its exact menu before trusting it.

## (c) Smallest open lemma and falsification tests

Smallest lemma that is genuinely open and that the proved part reduces the 2-set case to:
  LEMMA O2-PAIR (CONJECTURE). Correct one-NOT circuit, two sets A, B with |A ∩ B| <= 1 in configuration O2.
  Then there are zero points z_A, z_B with M_{z_A}(A) ∩ M_{z_B}(B) = ∅.
With b4 it gives MergeSDR for every 2-set circuit. It does NOT finish m >= 3: there the open statement is MergeSDR
itself (or the weighted dual). I could not find a smaller statement that implies it; K-Rado does not (a).
Useful sharpening inside O2: at top_A, top_B and all their atoms h = 1, so M_top is computed in the monotone
circuit C_0; an O2 pair with a (top,top) conflict needs the NOT-free gadget G(top,top), and then (0,0) was disjoint
on all 8 such corpus pairs except the two cxT pairs.

Tests (all with M_z(w) = systems.merges(c, S, systems.system(c, S, z, {u: z | 1 << u for u in S})[2])[0],
z over all 2^(n-|S|) zero points, h = c.h_wire, down = set(c.downstream())):
- F1 MergeSDR(c): exists (z_w)_w with M_{z_w}(w) pairwise disjoint (backtracking over the distinct merge sets,
  sets ordered by menu size). A circuit with MergeFrac L* <= 1 and F1 false separates integral from fractional;
  one with L* > 1 kills the route. F1' = same with the menu {0, top_w} (false on ADV3).
- F2 O2-PAIR(c, A, B): O2 := for every z' with z' ∩ B = ∅ and |A \ z'| <= 1: h(z') = 1 and h(z' & ~mask(A)) = 0, and the
  same with A, B swapped. If O2, test exists (z_A, z_B) with disjoint merge sets. Attack: hill-climb 2-set circuits
  (two 4-sets sharing one point, n = 7..9, start from cfgI minus set 2 and cxT2 restricted) minimising the number of
  disjoint world pairs, moves = insert the three gadgets of b5 at a random position with random u_i, v_i.
- F3 0/1 gap(c): R(c) = max over K ⊆ (union of all merge sets) of sum_w m_w(K) / |K| versus L*. R < L* on some
  circuit proves K-Rado is strictly weaker than MergeFrac in practice (expected to exist since CMP_w fails; none in
  the 163, where R = L*). Exhaustive for <= 20 gates in the union.
- F4 regression for b3: for all w != w', zero points z of w, z' of w' with z & ~z' = 0, |S_w \ z'| <= 1 and
  h(z | 1 << u) = h(z') for all u in S_w ∩ z': M_z(w) ∩ M_z'(w') = ∅. Must never fail (it is a theorem).
- F5 gadget stress for MergeFrac itself: on three or four 4-sets apply G(0,0), G(top,top) and G(chain) to every
  pair and to several intermediate worlds (G(chain) with x_v replaced by x_v & x_t kills only worlds containing t),
  keep the circuit correct/clean/read/essential as in ADV3, and track L*. ADV3 reached only 0.75.

Scripts (session scratchpad, may be cleaned; each < 60 lines, definitions above are complete):
/tmp/claude-0/-home-user-pequalnp-proofs/37a24535-f713-547f-b2b8-cd5b1ceb2b58/scratchpad/{fam,t1,t2,t3,t4,t5,t6,t7,t8,adv2,adv4}.py
(t1 matroid + F1; t2 CMP + pure rules; t3/t4 two-world menu and conflict types; t5 b1; t6 F4; t7 staircase; t8 O2).
