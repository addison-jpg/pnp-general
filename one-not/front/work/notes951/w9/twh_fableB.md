# twh_fableB.md — angle B: FracMatch via LP duality + minimal counterexample (restart-safe log)
NOTE (coordinator, verified): the fixed 1/2-1/2 coin rule / corrected two-world Hall is REFUTED by w9/tw/cxtw3c.json
(twoworldhall.md T2). That circuit has a Theorem-X zero-set family, so it is outside the Lean sorry's case. Free-choice
FracMatch (my target) is unaffected there (L*=1). cxtw3c/cxtw4c used below as test cases.

## D0 CHECKED: the plain FracMatch dual is trivially tight (not informative by itself)
fb/dual.py = fraclp + HiGHS dual prices pi. cxtw3c: L*=1 with pi = unit mass on ONE output (o_i of a triple whose every maximal
counted set has exactly d=2 gates {m_i,o_i} / {G,o_i}); cx2: L*=6/11, pi uniform on the 11 counted gates. L*=1 whenever some set
has |cnt|=d_w in every system, so "L*=1" in the data (badT: 63/63) says nothing about shared gates.
0/1 prices: pi=1_K gives the condition  (K-Rado, free choice):  for every gate set K:  Σ_w min_σ (d_w - |cnt_σ(w) \ K|)^+ <= |K|.
K = all gates is the bound s >= base itself.

## D1 CHECKED: deletion-minimality B8(3) holds for NO data circuit
fb/irr.py: max over proper F of P(F)-d(F) (P(F) = #gates in no cone outside F); a minimal counterexample needs <= -1.
cx1:+6 cx2:+2 cx3:+4 cxr:+5 cxtw3c:+10; badT min +1; bad min +1; chk/c min +2; w5ess min +5; tri_ess +5. So no data circuit is
deletion-irreducible; statements "under B8(3)" cannot be tested on existing data (confirmed).

## T1 PROVED (new, elementary): integral free-choice MatchG — hence the bound s >= base — for ALL systems with max |S_w| <= 3
Hypotheses: correct circuit, AND/OR fan-in 2 + one NOT, clean (no two wires compute the same function, no constant wire).
Menu used: only the B3 systems Σ(z) (z vanishing on S_w, atoms z+e_u, K = all gates). [Σ(z) is a Lean TestSys by B3.]
Claim: there are z_w and an injective choice of d_w gates in cnt_{z_w}(w), for all w simultaneously.
Proof. Every set takes its output o_w (o_w ∈ cnt_z(w) for every z; outputs are distinct wires). A triple i needs one more gate.
 Let o_i = A∘B (o_i is an AND/OR gate: it is monotone non-constant, so not the NOT).
 (OR-top) o_i = A∨B: A,B <= OR(S_i). At z=0: A(0)=B(0)=0 and the three units e_u (u∈S_i) are covered, so one input, say A, is 1 on
   two units of S_i. A is then not a variable and not N (N antitone, N(0)=0 would give N(e_u)=0), so A is a gate, A ∈ cnt_0(i).
   Take z_i=0, φ(i)=A. A is "i-dedicated": A <= OR(S_i) and A(e_u)=A(e_u')=1 for two u≠u' in S_i.
 (AND-top) o_i = A∧B: A,B >= OR(S_i), A∧B = OR(S_i); A≠B as wires (else o_i = A, not clean); neither is a variable or N
   (x_v >= OR(S_i) impossible; N >= OR(S_i) forces N(1)=1, N ≡ 1). Call A,B the "above-gates" of i; edge e_i={A_i,B_i}.
 Distinctness. (a) dedicated gates of different triples differ: A <= OR(S_j) and A(e_u)=A(e_u')=1 gives u,u' ∈ S_j, so j=i.
 (b) a dedicated gate is no output: A = OR(S_j) <= OR(S_i) forces S_j ⊆ S_i, j=i, and A≠o_i by cleanness. Same for above-gates
   (OR(S_j) >= OR(S_i) forces j=i). (c) dedicated ≠ above: OR(S_j) <= g <= OR(S_i) forces j=i and g ≡ OR(S_i), not clean.
 (d) STAR-FOREST LEMMA: in the graph H (vertices = above-gates, edges e_i) every edge has an endpoint of degree 1.
   Else e_i={A,B}, A ∈ e_j, B ∈ e_k, j,k≠i. Pick u ∈ S_j\S_i, v ∈ S_k\S_i, x = e_u ∨ e_v. OR(S_i)(x)=0 but A(x) >= OR(S_j)(x)=1,
   B(x) >= OR(S_k)(x)=1, so (A∧B)(x)=1. Contradiction. (Edges are distinct for distinct i since A∧B determines S_i.)
 For an AND-top triple take the degree-1 endpoint L_i. L_i is not constant (clean) and L_i >= OR(S_i), so L_i(z)=0 for some z
   vanishing on S_i (otherwise L_i ≡ 1); at that z, L_i(z+e_u)=1 for all three u: L_i ∈ cnt_z(i). Take z_i=z, φ(i)=L_i.
 Leaves of different edges differ, so φ is injective and avoids outputs. ∎
Same argument gives, for arbitrary set sizes: s >= Σ_w min(d_w, 2) and a matching saturating min(d_w,2) per set.
CHECKED fb/top2.py, top2c.py: the constructed matching verified on every clean circuit with a triple in cx1-3, cxr, cxtw3c/4c,
badT (15), bad (15), chk/c (824), tri_ess (11): 0 failures. (On UNCLEAN data circuits the leaf can be the constant 1: 118 cases; cleanness is used.)
CONSEQUENCES. (i) cx2, cxtw* (all triples) can never be bound-counterexamples; canonical / R* / coin rules fail on them only because
they are fixed rules. (ii) The real difficulty starts at |S| >= 4 = depth 3 below an output. (iii) In the dual (K-Rado) language the
proof shows: for sizes <= 3 every 0/1 price K satisfies Σ_w min_σ (d_w-|cnt_σ(w)\K|)^+ <= |K| (charge o_w, then dedicated/leaf gates).

## T2 PROVED (extension of T1, same proof): function-level private classes
D_w := {gates g : g <= OR(S_w) pointwise, g(e_u)=1 for >= 2 u in S_w}  (contains o_w). Then D_w ⊆ cnt_0(w) (system Σ(0)), the D_w are
pairwise disjoint, and disjoint from all above-gates (g >= OR(S_j), g ≢ 1) of AND-top sets. So there is an integral matching
(free choice, Σ(z) menu) saturating  min(d_w, |D_w|) for OR-top sets and min(d_w, 2) for AND-top sets, all sets simultaneously.
CHECKED fb/ded.py: cxr (4-sets, OR-top): |D_w|=4 >= 3 (self-sufficient at z=0, as known). cx1, cx3 (4-sets, AND-top o=C∧L_w, C shared
centre): D_w={o_w}, above-gates {C, L_w}: T2 gives 2 of the 3 needed; the third gate is the first gate below the leaf L_w.

## EXACT GAP after T1/T2 (analysis, not a proof)
Missing: the THIRD and later gates of sets with |S| >= 4, i.e. depth >= 3 below an output. Two places where privacy is not function-level:
 (G1) below a leaf L (L >= OR(S), L = P∨Q): the pair-sensitive input P at the chosen z is an arbitrary gate.
 (G2) below a dedicated gate A ∈ D_w that is an AND-cut A = P∧Q (P,Q >= A arbitrary).
 Partial (PROVED): for (G2), if h=0 on all inputs of weight <= 2, the cut pairs {P,Q} of gates with A(0)=0, two units in S_i, again
 form a star forest (same proof in C1: P^1(e_u∨e_v) >= P(e_u)=1, and the real circuit equals C1 at e_u∨e_v). Without that
 hypothesis the proof breaks (the point e_u∨e_v can be heavy).
Dual (0/1 price) view of what an adversary must do: a pool K, |K| < total deficiency, such that for most sets w EVERY gate outside
K∪{o_w,...} is never S_w-pair-sensitive at any z vanishing on S_w (K-Rado with free choice). Observations:
 - R*-world (z=z_S) is poolable with O(k) gates for ANY set size k: the monotone T=[zeros(x) ⊊ some S_j] is <= every OR(S_j) and fully
   sensitive at every z_{S_j}; with transversal classes one OR gate merges a pair for all sets at once (generalises G of cxtw).
 - unit world (z=0) is poolable with k-1 gates (X = OR of class-ORs, cx1's g,h) but then o_w = X∧Y_w with Y_w ∋ N, and Y_w = OR(S_w)
   off {X=0}: Y_w is fully sensitive at every z≠0 with Y_w(z)=0, and (K = all gates!) every hidden monotone chain W with units is
   counted at z=0 even when its parent is 1 there. In every hand design tried the intermediate worlds (zeros = S_w ∪ E) expose
   >= d_w non-pool gates. No FracMatch counterexample found; no proof that the intermediate worlds always suffice. CONJECTURE stands.

## L (coordinator's literature lead) CHECKED/PROVED, with a slightly more general form
Exactness lemma: on any input x, C0 gives o_w(x) whenever o_w(x)=0 or h(x)=1 (since g0<=f, g0=f on h=1); C1 gives o_w(x) whenever
o_w(x)=1 or h(x)=0. Hence on a subcube ρ: C0|ρ computes o_w|ρ iff h>=o_w on ρ; C1|ρ computes o_w|ρ iff h<=o_w on ρ.
Lead: if h|_{x_k=1} >= o_w for all w ∌ k then C0|_{x_k=1} is a monotone circuit for {o_w: w ∌ k}; N and every reader of x_k disappear:
s >= 1 + fanout(x_k) + Σ_{w∌k} d_w  (monotone bound). Correct. So a counterexample has Σ_{w∋k} d_w >= 2 + fanout(x_k) for such k.
Not combined with T1 yet (after x_k=1 the sets through k are constant; T1 only guarantees min(d,2) per set in the full circuit).

## T1 — exact list of facts used (for the Lean formalisation)
Data: wires = inputs x_0..x_{n-1} then gates; each gate AND/OR of two earlier wires or the single NOT N = ¬h, h an earlier wire.
F1 (monotone/antitone) every wire before N is monotone in x; hence N is antitone. [Only used to exclude N in F3/F5.]
F2 (clean) no wire is constant; no two distinct wires compute the same function.
F3 (output is AND/OR) o_w computes OR(S_w), |S_w|>=2: not an input wire (two units), not N (antitone+monotone ⇒ constant).
F4 (sets) |S_w|>=2, |S_a∩S_b|<=1 for a≠b. Consequences used: OR(S_j)<=OR(S_i) ⇒ j=i; a pair {u,u'} ⊆ S_i∩S_j ⇒ i=j;
   for j≠i there is u ∈ S_j\S_i.
F5 (OR-top) o_i=A∨B ⇒ A,B<=OR(S_i) pointwise, A(0)=B(0)=0, and for each u∈S_i: A(e_u)=1 or B(e_u)=1; |S_i|=3 ⇒ one input has
   two units; that input is a gate: not an input wire x_v (one unit), not N (N(0)=0 ⇒ N(e_u)=0 by F1).
F6 (AND-top) o_i=A∧B ⇒ A,B>=OR(S_i) pointwise; A≠B (else o_i≡A, F2); neither is x_v (x_v(e_u)=0 for u≠v∈S_i) nor N (N(1)=1 ⇒ N≡1).
F7 (star-forest) e_i={A,B}, A an input of AND-top o_j, B an input of AND-top o_k, j,k≠i ⇒ False (x=e_u∨e_v, u∈S_j\S_i, v∈S_k\S_i).
F8 (leaf has a zero) L>=OR(S_i), L≢1 ⇒ ∃z, z=0 on S_i, L(z)=0 [take any x with L(x)=0; then x=0 on S_i]. At that z, L(z+e_u)=1 ∀u∈S_i.
F9 (Σ(z) is a TestSys, B3) z=0 on S, atoms p_u=z+e_u, K=all gates; cnt = {gates g: g(z)=0, g(z+e_u)=1 for >=2 u∈S}.
   Used z: z=0 (OR-top) and the z of F8 (AND-top). o_i ∈ cnt for every such z.
F10 (distinctness) dedicated(i)≠dedicated(j) [pair in S_i∩S_j]; dedicated/above ≠ any output o_j [F4 + F2]; dedicated(i) ≠ above(j)
   [OR(S_j)<=g<=OR(S_i) ⇒ j=i, impossible since o_i is OR-top xor AND-top]; leaves of different edges differ [degree 1].
Not used: h(0)=0, hardness, essential NOT, read-closure of the cone, DD, s<base. (Simpler variant of the AND-top choice in T3 below:
take any input-tree frontier gate that is not >= OR(S_j) for all j≠i; it avoids the graph argument.)

## T3 PROVED: private classes Π_i (cleaner and stronger form of T1/T2), and which 4-set cases it closes
Over ALL gates g of the circuit define
  D_i = {g : g <= OR(S_i) pointwise, g(e_u)=1 for >=2 u∈S_i}          (dedicated-below; o_i ∈ D_i)
  P_i = {g : g >= OR(S_i) pointwise, g ≢ 1, and g ≱ OR(S_j) for every j≠i}   (private-above; o_i ∈ P_i)
(1) Π_i = D_i ∪ P_i are pairwise disjoint over i (D_i∩D_j: common pair; P_i∩P_j: by definition; D_i∩P_j: OR(S_j)<=g<=OR(S_i)).
(2) D_i ⊆ cnt_0(i); and g ∈ P_i is in cnt_z(i) for EVERY z vanishing on S_i with g(z)=0 (then g(z+e_u)=1 for all u∈S_i).
(3) PRIVATE-FRONTIER LEMMA: if o_i is AND-top, let F_i = the OR-gates reached from o_i through AND gates only (o_i = ∧F_i, all >= OR(S_i),
   none a variable or N). Some R ∈ F_i lies in P_i. Proof: else each G∈F_i has j(G)≠i with G>=OR(S_{j(G)}); pick u_G ∈ S_{j(G)}\S_i,
   x=∨_G e_{u_G}: every G(x)=1 so o_i(x)=1, but x misses S_i. Every AND gate on the path o_i→R is in P_i too (it is <= R and >= OR(S_i))
   and vanishes wherever R does.
(4) Hence with m_i := max_z |Π_i ∩ cnt_z(i)| there is an integral free-choice matching saturating min(d_i, m_i) for all i at once, and
   m_i >= 2 for every set of size >= 3 (this reproves T1). m_i >= 3 — so a 4-set is fully served by private gates — when
   (a) |D_i| >= 3 [o_i=A∨B with both inputs having two units, or the >=3-unit input A is an OR gate], or
   (b) two gates of P_i\{o_i} have a common zero vanishing on S_i [e.g. the private frontier gate R is not a direct input of o_i,
       or o_i=A∧B with A,B ∈ P_i and A(z)=B(z)=0 for some z].
OPEN 4-set configurations (exactly these):
 (I)  o_i = A∨B, A ∈ D_i with >=3 units of S_i, A = P∧Q an AND gate, B has <=1 unit, D_i={o_i,A}.   [third gate: P or Q; G2]
 (II') o_i = R∧C, R ∈ P_i an OR gate R=P∨Q, and C is either shared (C>=OR(S_j), some j≠i: cx1, cx3) or in P_i with no common zero with R
      on Z(S_i) (then C = ¬R on Z(S_i)).                                                           [third gate: P or Q; G1]
LEMMA (PROVED, for (II') with shared C): if C >= OR(S_j) then R(x)=OR(S_i)(x) for every x that hits S_j; in particular for v ∈ S_j\S_i
 the gate R restricted to the subcube {x_v=1} computes OR(S_i) EXACTLY. So R is a "virtual output" there, and at z=e_v (legal: vanishes
 on S_i) the gates g with g<=OR(S_i) on {x_v=1}, g(e_v+e_u)=1 for >=2 u (class D_i^v) are counted: in cx1/cx3 this is exactly the private
 chain that rescues the set. But D_i^v is NOT function-level private: it can meet D_j or D_k^v only for sets through v, and P_k only for a
 pair S_k={s,v}; across different v, v' there is no relation. So (II') reduces to a Hall problem among the relative classes D_i^v.
Status: all |S| <= 4 NOT proved; reduced to (I) and (II').
CHECKED (fb/t3.py, clean circuits with a set of size >=3): Π_i pairwise disjoint and m_i >= min(d_i,2) in cx1, cx2, cx3, cxr, cxtw3c,
badT (15), bad (15), tri_ess (11), chk/c (824): all. m_i >= d_i for every set in all of these except cx1 and cx3 (4-sets, m=2 < 3:
configuration (II') with shared C); cxr has m=4 >= 3.

## E1 CHECKED: configuration (I) DOES occur in a clean hard-case circuit with heavy low-weight inputs (fb/cfgI.py, fb/cfgI.json)
cx1 with set a recomputed: P = ((x0 ∨ (x7∧h)) ∨ x1) ∨ x2, Q = ((x0∨N) ∨ x1) ∨ x2, A = P∧Q (≡ x0∨x1∨x2), o_a = A ∨ x3; h = OR(x1..x6)
(all units of 1..6 heavy, so h≠0 on weight-1 and weight-2 inputs). verify: correct, clean, all read, C0 wrong, C1 wrong, s=25, base=7;
a,b hard N-sets, no Theorem-X family (Good(Q) forces Q ⊇ {1..6} as in cx1). ded.py: D_a = {A, o_a} exactly, top = OR, A an AND gate with
3 units: this is (I). t3.py: m = [2,2,2] for d = [3,3,1]. fraclp (full Lean menu): L* = 0.35 (FracMatch holds with room); coin rule 0.46.
So (I) cannot be excluded by cleanness/hard case; here the third gates are the P- and Q-chains (junk), visible at z=0 resp. z=e_v.
JSON: {"n": 9, "sets": [[0,1,2,3],[0,4,5,6],[7,8]], "gates": [["or",1,4],["or",2,5],["or",3,6],["or",9,10],["or",12,11],["not",13],
["or",13,0],["or",0,14],["or",16,4],["or",17,5],["or",18,6],["and",15,19],["and",7,13],["or",21,8],["or",22,14],["or",7,13],["or",24,8],
["and",23,25],["or",0,21],["or",27,1],["or",28,2],["or",16,1],["or",30,2],["and",29,31],["or",32,3]], "outs": [33,20,26]}

## C PROVED: conflict lemma for the relative classes  D_i^v = {g : g <= OR(S_i) on {x_v=1}, g(e_v+e_u)=1 for >=2 u∈S_i}, v ∉ S_i
(all of D_i^v is counted by i in Σ(e_v) provided g(e_v)=0, which follows from g<=OR(S_i) on {x_v=1}.)
 (a) same v: D_i^v ∩ D_k^v = ∅ for i≠k, v ∉ S_i∪S_k.  [the two atoms e_v+e_u must hit S_k ⇒ two points of S_i∩S_k]
 (b) D_i^v ∩ D_k ≠ ∅ ⇒ v ∈ S_k.   (c) D_i^v ∩ P_k ≠ ∅ ⇒ S_k = {s,v} is a pair (which only needs its output, so no demand conflict).
 (d) different v≠v', both heavy (h(e_v)=h(e_v')=1): D_i^v ∩ D_k^{v'} ≠ ∅ ⇒ v ∈ S_k and v' ∈ S_i.
     [N=0 above e_v, so g is monotone there: g(e_v+e_u+e_v')=1, a point of {x_v'=1}, must hit S_k; v'∉S_k; both u's in S_k is impossible.]
 (e) for (II') with shared C: the admissible v are V_i = {v ∉ S_i : C >= x_v}; R_i|_{x_v=1} = OR(S_i), and the child of R_i=P∨Q with
     two atoms at e_v is a gate of D_i^v (not a variable, not N).
Consequence: if all (II')-sets can use ONE common heavy v (v ∈ ∩V_i), their third gates are pairwise distinct and can only collide with the
dedicated gates D_k of sets through v. In general (d) does not exclude collisions: cx1 itself has v_a ∈ S_b, v_b ∈ S_a (no actual collision
there, the chains differ), and function-level a shared gate g = x_v∧OR(S_i\v') ∨ x_v'∧OR(S_k\v) satisfies all constraints.
NOT PROVED: a Hall argument over the choice of v. Obstruction found: each time a shared gate is assumed, its own sub-circuit again
contains pair-merges for S_i at the same z, which are private only relative to a further region (sibling = 0/1); the regress has no
function-level end. A proof needs a global potential (induction on something), not one more level of classes.
Checked dead end: induction by x_v=1 (kills o_k, P_k for k∋v, and o_i for v∈V_i) fails already for monotone circuits
(o_k = (x_a∨x_b)∨x_v: only one gate dies, d_k=2).
