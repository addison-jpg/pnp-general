# s_fable.md — price-form / weighted-elimination attack on free-choice FracMatch (restart-safe log)
Code: w9/s/ (sl.py classes, chk1-3.py). Data set D = 2558 circuits with n <= 12 (jcut/bt.allcirc: cx1-3, cxr, cfgI, fc/*, tw/*, badT, bad, chk/c), all verified correct.
Notation: C0/C1 = circuit with N:=0/1 (monotone); U1={h=1} (up-set, real=C0 there), U0={h=0} (down-set, real=C1). w hard iff h(z_{S_w})=1.
For a gate g write g^0=C0(g), g^1=C1(g) (monotone functions, g^0 <= g^1; g^0=g^1 iff g is N-independent as a function pair).

## S1 PROVED: two-world class system (cleans up E0.1/J; three new points marked NEW)
Classes (sets of gates):
 (E)  w easy:  Ē_w = {g : g^1 <= o_w everywhere, g^1(e_u)=1 for >=2 u in S_w}.
 (0,z) w hard, z in U1, z∩S_w=∅:  H_z(w) = {g : g^0(z)=0, g^0 <= o_w on the cube {x>=z}, g^0(z+e_u)=1 for >=2 u in S_w}  (= I^L_z(w); real=C0 on that cube).
 (1,c) w hard, c in U0, c∩S_w=∅:  E_c(w) = {g : g^1 <= o_w on Dom_c = {x in U0, x <= c ∨ 1_{S_w}}, g^1(e_u)=1 for >=2 LIGHT u in S_w}.
Coverage:
 (a) NEW  |Ē_w| >= d_w for every easy w, heavy units included.  Proof: for easy w, C1 computes o_w EXACTLY on all inputs (C1_w >= o_w always,
     C1_w = o_w on U0, and o_w(x)=0 forces x <= z_{S_w} in U0). So C1 is a monotone circuit for o_w: Mehlhorn exploration (RM with Dom = everything)
     from o_w, B(g) = {u in S_w : g^1(e_u)=1}, gives >= d_w OR gates with |B|>=2 and g^1 <= o_w.  (J's E1 gave only L_w - 1.)
 (b) NEW  |H_z(w)| >= d_w for EVERY z in U1 vanishing on S_w (J's E3 was z = z_{S_w} only). Proof: Dom = cube {x>=z} is inside U1 and closed under join,
     so RM applies in C0; atoms z+e_u; leaves are variables/constants with value 0 at z.
 (c) |E_c(w)| >= L_w - 1 (L_w = #light units; J's E1 with a ceiling).
Conflicts (w != w'):
 (d) Ē_w ∩ Ē_w' = ∅;  NEW Ē_w ∩ E_c(w') = ∅ (two light units of S_w' would lie in S_w).
 (e) H_z(w) ∩ H_z'(w') != ∅  =>  z hits S_w' and z' hits S_w.     (E0.1(c))
 (f) E_c(w) ∩ E_c'(w') != ∅  =>  |S_w ∩ Q'| >= 2 and |S_w' ∩ Q| >= 2, Q = zero set of c (Theorem X condition).
 (g) NEW cross-world: a gate lying in a world-1 class (Ē_w or E_c(w)) and in a world-0 class H_z'(w') is N-DEPENDENT (g^0 != g^1).
     Proof: if g^0=g^1=g monotone, g(e_u)=1 for two u in S_w gives g(z'+e_u)=1, two points of the cube {x>=z'} of which at most one hits S_w'. ∎
     Sharper: collision impossible if g^1 <= o_w' on {x>=z'} ("0-strict") or g^0(e_u)=1 for the two units ("1-strict").
 (h) Z_g(w) = {z : g in H_z(w)} is an up-set in {z in U1, z∩S_w=∅}.
CHECKED on D (chk1.py, chk2.py): 3069 easy classes, 46825 (0,z) classes, 36559 (1,c) classes: 0 short. Conflict lemmas: 0 violations; cross-world
 collisions: 28 (E vs 0) + 44 (1 vs 0) class pairs, ALL on N-dependent gates.
CHECKED: FracMatch LP with ONLY these classes (free choice of world/z/c): L* <= 1 on all 2558 circuits (L*=1 2547 forced-private, else <= 0.82).
REFUTED-as-rule (chk3.py): "world-0 sets use 0-strict classes" (kills all cross-world conflicts by (g)): 251 hard sets have no full strict class
 and no full world-1 class (203 circuits uncovered; cxT2 L=3). So cross-world collisions cannot be defined away; they must be charged.

## S1' CORRECTION to the "L* <= 1 on all data" line of S1
The S1 menu (sl.py: (0,z) base points, (1,c) with LIGHT unit atoms only) FAILS on cxT4 (n=15): L* = 4/3 (same failure as C's restricted
relative rule). It is <= 1 only on the 2558 circuits with n <= 12. The menu of S2 below repairs it (cxT4: 0.632).

## S2 PROVED: LIFTED MONOTONE FORM and the single-domain class lemma (unifies Thm X, X+, E0.1, B4, heavy point, J's E1/E3)
Lift. Replace N by a new input y: M(x,y) is a MONOTONE circuit on n+1 inputs with s-1 gates; real value at x = M(x, ¬h(x)); C0 = M(.,0), C1 = M(.,1).
F_w := M_{o_w}. Spec (PROVED, exactness lemma):  F_w(x,0) <= o_w(x) <= F_w(x,1) for ALL x;  F_w(x,0)=o_w(x) on U1;  F_w(x,1)=o_w(x) on U0.
 Forced zeros of F_w: (x,0) for every x avoiding S_w [also x in U0: a "virtual" point], (x,1) for x in U0 avoiding S_w.
 Forced ones:  (p,1) for every p hitting S_w [also p in U1: virtual],  (p,0) for p in U1 hitting S_w.
So 951 is equivalent to a purely monotone statement: a monotone circuit over (x,y) containing a y-free wire h and outputs
 F_w in [o_w ∧ (y ∨ h), o_w ∨ (y ∧ h)] has >= base - 1 gates.
LEMMA S2.1 (lifted counting). Let Z be a nonempty JOIN-CLOSED set of points of {0,1}^{n+1} with F_w = 0 on Z, and a_1..a_k points with F_w(a_i)=1,
 such that (L) every input variable (x_v or y) vanishing identically on Z is 1 at <= 1 of the a_i. Then
 cl(Z,a) := {gates g : M_g = 0 on Z, M_g(a_i)=1 for >= 2 i} contains >= k-1 OR gates.
 Proof. V = wires vanishing on Z. OR in V => both inputs in V. AND G=s∧t in V => s in V or t in V (else s(a)=1, t(b)=1 with a,b in Z, a∨b in Z,
 G(a∨b)=1). B(g) = {i : g(a_i)=1}. Union-find over the wires of V in circuit order, invariant "B(g) lies in one block": inputs by (L); AND: B(G) ⊆
 B(child in V); OR: union of two blocks, a merge if they differ (then |B|>=2, G in cl). B(o_w) = everything, so >= k-1 merges. ∎
LEMMA S2.2 (lifted X+ / pair budget). Configurations (Z_a,a^a) of set a, (Z_b,a^b) of set b, P(a|b) := {i : a^a_i not below any point of Z_b}.
 Every g in cl_a ∩ V_b has B_a(g) ⊆ P(a|b); at most (|P(a|b)|-1)^+ merge gates of a lie in V_b. So |P(a|b)| <= 1 or |P(b|a)| <= 1 => cl_a ∩ cl_b = ∅.
LEMMA S2.3 (classification of FUNCTION-LEVEL domains). A join-closed set of forced zeros of F_w lies in
   Z^0_w = {(x,0) : x avoids S_w}   (type 0),   or in   ↓(c,1), c in U0 avoiding S_w   (type 1, Q = zero set of c).
 (If Z has a level-1 point, the join of all of Z is a level-1 point (c,1) of Z.) Larger Z is better for (L), for the class size and for privacy.
 Type 0 with |S_w| atoms: atoms (p_u,0), p_u in U1, p_u ∩ S_w = {u}; at most one atom may be at level 1.  cl = {g : g^0 <= o_w EVERYWHERE, >=2 atoms}.
 Type 1: atoms (p_u, l_u) with traces p_u ∩ Q pairwise disjoint, p_u ∩ S_w = {u}; level 0 only if p_u in U1 (e.g. (e_u,1) for all u, heavy or not).
 Blocking: a type-0 atom (p,0) is below Z^0_b iff p avoids S_b, never below a type-1 domain; a level-1 atom (p,1) is below ↓(c',1) iff p <= c', never below
 Z^0_b; a level-0 atom of a type-1 set is below Z^0_b iff it avoids S_b.  (Thm X = type 1/type 1; E0.1, B4 = type 0/type 0; cross-type pairs with
 level-1 atoms are always fully blocked: this is the two-world obstruction, cf. S1(g).)
 CIRCUIT-DEPENDENT extension: Z may be any join-closed subset of the ACTUAL zero set of F_w (e.g. ↓(c,1) for c in U1 with F_w(c,1)=0) and atoms any
 actual one-points (p,0) with F_w(p,0)=1, p in U0.
CONSEQUENCES (PROVED).
 (i) ClassFrac: if every set has finitely many configurations and a fractional assignment of d_w units into the classes with every gate load <= 1,
     then s >= base + 1 (N is not a gate of M, so no class contains it). ClassFrac is NOT literally the Lean FracMatch (virtual points are not real test
     points: easy sets at type 0, heavy unit atoms (e_u,1)), but it implies the bound by the same counting; its LP dual is the same price form with
     "cnt_σ" replaced by "cl(Z,a)". For hard sets, type-0 classes with p_u <= z_{S_w}+e_u are inside cnt of the Lean system (z_{S_w}; atoms p_u).
 (ii) every set, hard or easy, heavy units or not, has FULL coverage d_w in every configuration (repairs J's "L_w - 1" and E's coverage warning:
     coverage is never the problem in a join-closed domain; only privacy is).
 (iii) any proof through lifted classes gives s >= base+1 for circuits containing a NOT (matches CHECKED "no live-NOT circuit of size <= base+1").
CHECKED (chk4.py, random atoms, n <= 10): 41556 type-0 and 25222 type-1 configurations: 0 short classes; 6151 colliding pairs: 0 violations of S2.2.
CHECKED (lift.py, lift2.py; function-level + circuit-dependent menu, caps 40 ceilings x 128 atom combos): ClassFrac LP L* <= 1 on ALL data:
 2555 circuits n <= 9 (L*=1: 2542 forced-private; else <= 0.667), cx3 0.5625, cxtw4/cxtw4c 1.0, cxT4 (n=15) 0.632 (mixes type 0 with weight 0.37 and
 type 1 with 0.63; an integral type-1 matching also exists). No ClassFrac counterexample.

## S3 CHECKED: extreme prices (plan step 1)
dual2.py (S1 menu, HiGHS vertex duals, 2558 circuits): EVERY optimal dual price vector is uniform on its support (0/1 prices up to scaling).
 2546 are single-set vertices (π = indicator of the union of one set's classes, or of one forced gate); only 12 involve interaction
 (cxtw*, cxe3, 4 of bad: unit mass on one gate shared by all size-d classes; cxT2: 11 gates uniform; cx44_0/1: 17 gates uniform).
 So on data the price form is attained at K-Rado prices π = 1_K:   Φ(K) := Σ_w min_cfg (d_w - |cl_cfg(w) \ K|)^+ <= |K|.
 (General π does not reduce to 0/1 by threshold decomposition: min does not commute with the integral; K-Rado is the weaker statement, and K = all
 gates is already the bound.)
## S4 CHECKED / REFUTED-as-method: weighted gate elimination along chains (plan step 3)
elim.py: Φ(K) <= |K| holds on all 2558 circuits for every prefix chain (K = first i gates) and suffix chain (K = last i gates).
 But the increment Φ(K+g) - Φ(K) exceeds 1 on 27 circuits (prefix order), 9 (suffix order), 49 (greedy smallest-increment order).
 REFUTED as method: "eliminate one gate, at most one set loses one unit". A gate-by-gate induction needs a potential with memory (amortisation).
 Paper analysis of the other elimination moves in price form: (a) last gate = an unread output o_w*: gives the bound iff m_w*(π) <= π(o_w*): false;
 (b) x_v := 0 with π restricted to survivors: reduces to "each set through v finds one extra counted gate, total cost <= π(dead)" = weighted (K),
 false for bloated monotone circuits (E2) although the price inequality itself is trivial there (z = 0, D_w private). So variable/gate elimination is
 the wrong induction for the price form; the natural induction parameter is the set of N-DEPENDENT gates (S1(g): all cross-world sharing lives there).

## S5 EXACT GAP (after S2)
PROVED: s >= base+1 whenever a pairwise X+-compatible family of lifted configurations exists (S2.1+S2.2); function-level families are classified (S2.3).
NOT PROVED: ClassFrac (or its price/K-Rado form) for every circuit. Function-level families do not always exist (two complementary sets with
 h = Th_2: every type-0 atom hits the other set; type-1 ceilings have weight <= 1), so the proof must read gates. What is missing, precisely:
 for a gate g lying in cl_a ∩ cl_b (then |B_a(g)|,|B_b(g)| >= 2 inside the blocked sets), a charging of the collision to a gate in NO chosen class.
 Known structure of a colliding gate: (same type 0) g^0 <= o_a ∧ o_b: every one-point of g^0 hits both sets; (cross type) g is N-dependent and,
 if g = p ∨ q merges in both worlds, one input p is an N-dependent "selector" (p^1 >= x_u, p^0 not >= x_u). CONJECTURE (S-repay, = J-repay in lifted
 form): #collisions (with multiplicity) of an optimal ClassFrac solution <= #gates outside all chosen classes. Not tested beyond L* <= 1 (data slack).
 Smallest hand target: two complementary 4-sets, h = Th_2 (no function-level family; bound known only via R0').

## PNP-SUBPROBLEM LINKS (coordinator directive; hand arguments, NOT checked by code)
 1. S2.1 is a statement about ANY monotone circuit, so it applies after lifting ANY number k of NOT gates (y in {0,1}^k, real points (x, ν(x)),
    forced zeros (x,y), y <= ν(x), f(x)=0; forced ones (x,y), y >= ν(x), f(x)=1). It is a lower-bound technique for OR gates: a join-closed zero
    domain Z plus k one-points, each Z-vanishing input 1 on <= 1 of them, gives k-1 OR gates vanishing on Z.
 2. For f_G = OR_{uv in E} x_u x_v in a MONOTONE circuit: Z = ↓1_I, I a maximum independent set (join-closed, f_G = 0), atoms 1_I + e_v for v not in I
    (each has an edge into I when I is maximal): >= n - α(G) - 1 = τ(G) - 1 OR gates, all vanishing on 1_I. This is the "τ - 1" term of |E| + τ - 1.
    The |E| term needs the dual lemma (meet-closed one-domain, AND merges) and is not obtained this way (one AND per edge needs a separate argument:
    e.g. at the zero point 1_{V \ {u,v}}... not worked out).
 3. C4-free link (NOT a result): for u in an independent set I, Z = {0, e_u}, atoms e_u+e_v (v in N(u)) give deg(u)-1 OR gates per u by S2.1, but
    these classes are NOT private by S2.2 (no atom of u lies below a zero domain of u'), so Σ_{u in I}(deg(u)-1) does not follow. Privacy would need
    "g <= OR(N(u)) on {x_u=1}"-type classes, i.e. the relative classes D_i^v of Fable B, whose privacy is exactly the open regress here.
 4. With NOTs the same obstruction as here appears: classes at different lifted levels are mutually unblocked; any amortisation that closes S5 would
    transfer to f_G on C4-free graphs.

## FALSE-STATEMENT NOTICE (qg101 = session_01GmnDhdZb2EsYNLc1r4M85e, 08:29 UTC; recorded by front)
S1(g) ("all cross-world sharing lives on N-dependent gates") does NOT carry over from the class system H_z to the union-find merge
sets M_z(w) without two extra hypotheses: (i) the world-1 point z' of b also vanishes on S_a; (ii) C0(g)(z_{S_a}) = 0.
(H_z(a) has (ii) built in via strict_of_cube.) PROVED in Lean under (i)+(ii): pequalnp-work crossworld @ c72d6ff, W951/CrossWorld.lean,
CrossWorldAt.ndep / ndep_canonical. Both hypotheses necessary (correct circuits checked by decide, n = 5, S = {01, 23}, h = x4):
 - cx1: f = (x0|x2)|(x1|x3) is in M_{e4}(a) (world 0) AND in M_0(b) (world 1), and is N-INDEPENDENT.
 - cx2: f = (x0&(x2|x4)) | ((x1&x4)|(x0&x3)), with z' = e0 meeting S_a.
=> any rule/lemma that assumes "cross-world merge gates are N-dependent" must add (i)+(ii) or work with H_z classes.
