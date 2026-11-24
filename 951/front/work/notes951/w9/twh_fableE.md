# twh_fableE.md — agent E (lateral/global angle), restart-safe log

## E0 (coordinator's "relative sandwich" lead) — conflict lemma PROVED, coverage CHECKED
Definitions. For set w and a point z vanishing on S_w, system Σ(z) (atoms z+e_u, K = all gates, always legal).
  I^L_z(w) = {g ∈ cnt_z(w) : g <= OR(S_w) on the cube {x >= z}}   (lower part; z=0 gives D_w)
  I^U_z(w) = P_w ∩ cnt_z(w), P_w = {g >= OR(S_w), g ≢ 1, g ≱ OR(S_j) for j≠w}      I_z(w) = I^L ∪ I^U.
LEMMA E0.1 (PROVED). Let w≠w'.
 (a) I^U_z(w) is disjoint from I_z'(w') for all z,z'. [P_w∩P_w'=∅ by definition. g ∈ P_w ∩ I^L_z'(w'): g(z')=0 and g>=OR(S_w) give
     z'∩S_w=∅; for a ∈ S_w\S_w' the point z'+e_a is in the cube, g=1 there, OR(S_w')=0 there. Contradiction.]
     (This sharpens B's C(c): no exception for pairs.)
 (b) If g ∈ I^L_z(w) ∩ I^L_z'(w') then  [z ∩ S_w' ≠ ∅  or  some u∈S_w has h(z+e_u)=0 and h(z∨z'+e_u)=1 ("crossing at the z side")]
     AND the same with (w,z),(w',z') exchanged.
     [g(z+e_u)=1 for two u∈S_w. If neither step z+e_u -> z∨z'+e_u is crossing, A2.1 gives g(z∨z'+e_u)=1; that point is in the cube
      {x>=z'}, so it hits S_w'; z'∩S_w'=∅ and at most one of the two u is in S_w', so z hits S_w'.]
 (c) Consequences for the rule "z=0 or z a 1-point of h":  (0,0): never collide.  (heavy z, heavy z'): collide only if z hits S_w' AND z' hits S_w.
     (z=0 for w, heavy z' for w'): collide only if z' hits S_w (and then a crossing e_u -> z'+e_u exists automatically).
 COROLLARY (PROVED): if z_w ∈ {0} ∪ h^{-1}(1) are chosen so that no pair w≠w' has (z_w' hits S_w and (z_w=0 or z_w hits S_w')),
     then the I_{z_w}(w) are pairwise disjoint and  s >= Σ_w min(d_w, |I_{z_w}(w)|)  (integral matching in Lean systems Σ(z_w)).
 NO pair budget beyond (b) is provable at function level: g_j = x_c'∧(partial OR of S_w) ∨ x_c∧(partial OR of S_w') (c∈S_w', c'∈S_w)
     gives arbitrarily many common gates of I^L_{e_c}(w) and I^L_{e_c'}(w'). A budget must use the circuit above g.
CHECKED (w9/fe/rel.py; z ∈ {0} ∪ minimal 1-points of h of weight <=2 off S_w): cx1, cx2, cx3, cfgI, cxr, cxtw3c, cxe3, badT(63), bad(160),
 c.jsonl (first 400): 0 violations of (a),(b); actual collisions are rare (3 pairs in all); max_z |I_z(w)| >= d_w for EVERY set in all of
 these (slack: cx1 [1,1,2], cx3 [1,1,1], cfgI [1,1,2], cxr [1,1]).  So the coordinator's coverage claim is confirmed on my side.
WARNING (CONJECTURE, not built): coverage max_z|I_z(w)| >= d_w is not a theorem-shaped statement: below a mixed cut the pair-merges
 are <= OR(S_w) only relative to a non-cube region (sibling = 1), e.g. R = (A∧B) with A = OR(S_w)∨J1, B = OR(S_w)∨J2, J1∧J2 killed by the
 shared sibling; then no gate of the A- or B-chain lies in any I^L_z. A proof of coverage needs relative regions that are not cubes.

## E1 PROVED: point-deletion reductions (induction on n over the FULL statement "every correct one-NOT circuit has s >= base")
Restriction ρ = (x_v := b). A gate is DEAD under ρ if its restricted function is constant, a variable, or the restricted function of
one of its own inputs. All dead gates can be removed simultaneously (redirect readers to the constant/variable/input; propagate
constants), giving a correct AND/OR + <=1 NOT circuit for the restricted family (S_w\{v} for b=0; the sets avoiding v for b=1; sets of
size <=1 are dropped, they have demand 0). So  s >= s(restricted) + #dead.  Every gate reading x_v directly is dead (x_v∨c -> c,
x_v∧c -> 0, ¬x_v -> 1); for b=0 every pair-output o_{v,u} is dead (≡ x_u); for b=1 every gate >= x_v is dead (≡ 1).
THEOREM R0. Let v be a point such that at most one set through v has size >= 3. Then #dead(x_v:=0) >= deg(v) = loss of base.
 Proof. Sets through v: w0 (size >= 3, if any) and pairs {v,u_j}, j=1..p. The p outputs o_j are dead and distinct. If there is no w0, done
 (also x_v:=1 works: the p outputs are ≡ 1, base loss p). Else we need one more dead gate. Suppose there is none. Then every direct
 reader of x_v is some o_j (so N does not read x_v), o_j = x_v ∘ c; ∘=AND is impossible (o_j(e_{u_j})=1); so o_j = x_v ∨ c with
 c|ρ = x_{u_j}. If c is a gate it is dead and differs from every o_j' (different restricted function) — contradiction. So c is the input
 x_{u_j}: every reader of x_v is a gate x_v ∨ x_{u_j}. Put x_{u_j}=1 for all j, everything else 0: no wire changes when x_v is toggled,
 but OR(S_w0) does (u_j ∉ S_w0). Contradiction. ∎
COROLLARY R0' (PROVED, given the Lean-proved case max|S_w| <= 3): the bound s >= base holds for every system whose CORE has no set of
 size >= 4, where the core is obtained by repeating: delete a point lying in at most one set of current size >= 3; drop sets of size <= 1.
 Equivalently: a minimal counterexample (minimal n) satisfies
   (N1) every point lies in >= 2 sets of size >= 3;
   (N2) for every v: #(direct readers of x_v) <= #dead(x_v:=0) <= deg(v) - σ,  σ = base - s >= 1;
   (N3) for every v: #(gates >= x_v pointwise) + #(gates unread after x_v:=1) <= Σ_{w∋v} d_w - σ.
 In particular cx1, cx3, cfgI, cxr-type systems (4-sets whose points other than one centre have degree 1) are covered by R0' without any
 Hall argument; the smallest systems still open have a 4-set with all four points in a second set of size >= 3 and all those sets
 again closed under (N1), e.g. n=8: {1,2,3,4},{1,5,6},{2,5,7},{3,6,7},{4,5,8},{2,6,8} (base 13), or the 4x3 grid (n=12, base 17).
 (Exhaustive SAT at s = base-1 = 12, n = 8 is out of the 5-minute budget; not run.)
CHECKED (fe/kill.py, fe/r0.py: restricted truth tables, functional cleanup, cone of surviving outputs): R0 on 1602 (circuit, v) instances
 from cx1, cx2, cx3, cfgI, cxr, cxtw3c, badT, bad, c.jsonl[:400]: 0 violations.
STRUCTURE of a degree-2 point in a minimal counterexample (PROVED from N2): exactly one gate r reads x_v and nothing else dies.
 If r = x_v ∨ c then c is a non-constant gate, x_v-free, c <= OR(S_a\v) ∧ OR(S_b\v) (a "sub-junk" gate: with r=1 forced by c, o_a cannot
 see x_v). If r = x_v ∧ c then c = 1 wherever OR(S_a\v)=0 or OR(S_b\v)=0 (so c(0)=1, c is downstream of N). r = ¬x_v gives h = x_v.

## E2 CHECKED / REFUTED-as-method: "one variable always pays" (K)
(K): in every correct circuit some v has #dead(x_v:=0) (+unread) >= deg(v), or #dead(x_v:=1)(+unread) >= Σ_{w∋v} d_w.  (K) ⇒ 951 by induction.
CHECKED: holds with slack on all data (min over circuits of max_v surplus: badT 5, bad 3, c400 2, cx1 15, cx3 15, cfgI 18, cxr 8, cx2 12,
 cxtw3c 16, cxe3 35) — but all data are far above base, so this is weak evidence.
Paper analysis (not machine-verified): (K) for x_v:=0 is probably FALSE for bloated MONOTONE circuits (plane of order >= 7: single useful
 reader a_v = x_v ∨ J_v with J_v = AND over lines through v of ORs of shared pair-gates; each variable has <= 7 readers < deg = 8 and no
 cascade). So (K) can only be true/provable for minimal counterexamples, where the junk needed to block deaths costs gates. A
 strengthened hypothesis is needed, candidate (CONJECTURE ★): #gates outside J^L ∪ J^U >= base, where J^L = gates below two different
 sums (g <= OR(S_a)∧OR(S_b), a≠b: contains T, x0∨T of cxtw and every "x_v ∨ sub-junk" reader), J^U = gates above two different sums
 (shared centres C). J^L, J^U are disjoint from all private classes Π_w (PROVED: a gate of J^L has <= 1 unit; a gate of J^U is not in P_w
 by definition; D_w∩J^U and P_w∩J^L would give OR(S_a) <= OR(S_b)).  Not tested (data cannot discriminate), not proved.

## E3 angle 1 (A3 on the relative systems Σ(e_v)) — REFUTED as stated
A3's blocked set for a=(i, z=e_v, atoms e_v+e_u), b=(k, z=e_v'): an atom is unblocked only if e_v+e_u <= z_b, which never holds for
small z_b. So P(a|b) = S_a and the pair budget is vacuous: A3 needs LARGE zero points (z_Q-type), the relative classes need SMALL ones.
What survives is the conflict lemma E0.1 (collisions only between sets whose z's mutually hit), with no function-level budget.
Combination with the restriction bound (PROVED, simple): let v be heavy (h >= x_v). Sets avoiding v: systems (z_{S_w}; atoms e_u+e_v)
 are legal and pairwise separated (C3: e_u+e_v <= z_{S_w'} for u ∉ S_w', all heavy), giving Σ_{w∌v} d_w pairwise distinct counted gates
 [this is PartialBound in system form]. The sets through v (a star) then need Σ_{w∋v} d_w - (s - 1 - Σ_{w∌v} d_w) further gates; the star's private
 classes Π_w (T3) are disjoint from each other but NOT provably from the counted gates of the other sets (a gate of D_w, w∋v, can be
 counted by w'∌v at z_{S_w'} with atoms e_u+e_v only if it is 1 at e_u+e_v for two u ∈ S_w' and 0 at z_{S_w'}; g <= OR(S_w) forces
 nothing there because x_v=1). Using atoms z_{S_w'}-side "g(z_{S_w'})=0" and g∈P_w (g>=x_v, v ∈ ones(z_{S_w'})) gives g(z_{S_w'})=1: so
 P_w (w∋v) IS disjoint from all those counted sets.  PROVED: for heavy v,
     s >= 1 + Σ_{w∌v} d_w + Σ_{w∋v} |P_w|     (N itself is not counted by any of them: N(z)=0 needs h(z)=1, then N=0 at all atoms).
 So with a heavy point v the only sets that can lose are OR-top sets through v and AND-top sets through v with |P_w| < d_w.

## STATUS (agent E)
PROVED: E0.1 (conflict lemma for the relative sandwich classes I_z, any heavy z), R0/R0' (point deletion; minimal counterexample has every
 point in >= 2 sets of size >= 3), heavy-point bound s >= 1 + Σ_{w∌v} d_w + Σ_{w∋v}|P_w|.
REFUTED as methods: A3 on Σ(e_v) (vacuous), one-variable induction (K) without a strengthened hypothesis.
OPEN (exact gap): a system whose core (R0') contains a set of size >= 4, in configuration (I) or (II'); needed: either coverage+matching for
 the relative classes (cross-set collisions only between mutually hitting z's, no budget), or an induction with hypothesis ★.
No counterexample to FracMatch or to the bound found; no new circuit with L* > 1.
