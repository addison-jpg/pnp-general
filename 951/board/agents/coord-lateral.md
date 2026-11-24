# NOTES.md — lateral attack on 951 via Sokolov's dag-like game (restart-safe log, 2026-11-24)
Lane: GAME / ADVERSARY formulation only. Files: defect.py, rundef.py (section 3), hor2.py (section 5).
Labels: PROVED-PAPER / CHECKED / CONJECTURE / REFUTED. Nothing here is in Lean.
Notation: M = lifted monotone circuit over (x,y), s-1 gates; h y-free wire, h(0)=0; U1={h=1}, U0={h=0};
F_w output; d_w=|S_w|-1; base=Σd_w. Points (q,l), l = value of y. Ω_w := o_w ∨ (y∧h).

## 0. Summary (read this first)
- S1 PROVED-PAPER  translation into the multi-root game; a game is a circuit read top-down, with canonical
  rectangles; h = a node whose rectangle is an x-cylinder on both sides; the root rectangles are DEFINED from it.
- S2 PROVED-PAPER  the two existing lemmas are rectangle statements: S2.1 = adversary holding atoms × (join-closed
  Bob set); S2.2 = "a rectangle contains its cross pairs". NEW: AND-witness lemma (S2.3 below).
- S3 PROVED-PAPER + CHECKED  DEFECT FORM (exact, no choices): canonical classes "wires ≤ Ω_w" are pairwise private
  for EVERY h; all loss sits at Bob-splitting ("split") AND nodes:  s-1-base = #rest − Σ_T (m(T)−1)  (identity).
  So 951 ⇔ Σ_T (m(T)−1) ≤ #rest. This is the game view's version of S-repay: a MERGE-SET form (not whole-class,
  which front's referee refuted), and as an identity it is a restatement, not a reduction.
- S4 PROVED-PAPER  h ≤ x_a (in particular h = x_a∧x_b, the suggested target) is already a Theorem-X family: s ≥ base+1.
- S5 PROVED-PAPER (partial, new) h = x_a ∨ x_b, the simplest h with no function-level private family:
  s ≥ base + 1 − ⌊K/2⌋, K ≤ π = #points ≠ a,b lying on both a set through a (not b) and a set through b (not a).
  Hence 951 for h = x_a∨x_b when π ≤ 3, s ≥ base+1 when π ≤ 1. Full case OPEN: exact sticking point in 5.5.
- **S8 (follow-up) PROVED-PAPER + CHECKED: THEOREM H2. h = x_a ∨ x_b ⇒ every lifted circuit has ≥ base gates
  (s ≥ base+1). Conjecture H2 of 5.5 is closed; this is FJ for h = x_a∨x_b (h need not be a wire). See section 8.**
- Negative result: the adversary view does not escape the sharing obstruction; it relocates it (section 6).

## 1. Translation (deliverable 1)  PROVED-PAPER
Bob's/Alice's sets for root w (h fixed as a function):
  U_w = {(p,1): p hits S_w} ∪ {(p,0): p hits S_w, h(p)=1},   V_w = {(q,0): q avoids S_w} ∪ {(q,1): q avoids S_w, h(q)=0}.
Every pair in U_w×V_w has an answer i ∈ S_w (p_i=1,q_i=0); y is a legal answer only for pairs ((p,1),(q,0)).
Multi-root game: DAG, one root per w with rectangle U_w×V_w, inner rectangle ⊆ union of the two children's, leaf
rectangle answered by one coordinate (x_i or y). By Sokolov Thm 3.2 (both directions are node-for-node):
  game with S inner nodes  ⇔  monotone circuit with S gates with F_w(U_w)=1, F_w(V_w)=0.
1.1 (canonical rectangles) Given a game, the circuit built from it gives monotone f_v with f_v=1 on A_v, 0 on B_v.
  Replacing R_v by (f_v^{-1}(1)) × (f_v^{-1}(0)) keeps a valid game on the same DAG. So WLOG: OR node = Alice
  splits (Bob side inherited by both children), AND node = Bob splits (Alice side inherited). The adversary only
  ever needs: at an OR, B_child ⊇ B_node; at an AND, A_child ⊇ A_node and B_node ⊆ B_σ ∪ B_τ.
1.2 (what h is) h is a node whose canonical rectangle is {(p,·): h(p)=1} × {(q,·): h(q)=0}: both sides are
  cylinders in y. The root rectangles are cut out by this cylinder: U_w = {o_w=1} ∩ ({y=1} ∪ A_h),
  V_w = {o_w=0} ∩ ({y=0} ∪ B_h). So LiftedBound is a SELF-REFERENTIAL game: "a DAG containing a y-cylinder node h,
  whose roots solve the rectangles defined by h, has ≥ base−1 inner nodes". For fixed h it is an ordinary partial
  monotone problem (but then the cost of h is not counted and the bound is false in general: 1-slice, see
  tractability-nominCE.md). Any proof must use that h is a node (e.g. S5 uses atoms (e_a,0), available only
  because h(e_a)=1, and the gate h is itself the cheapest colliding wire h∨x_p).
1.3 Forced zeros of root w have tops (z_{S_w},0) and (c,1), c maximal in U0 avoiding S_w. Bob's set is a union of
  principal down-sets, join-closed iff one top. Number of tops−1 = how often Bob can be split usefully.

## 2. Adversary lemmas in rectangle form  PROVED-PAPER
2.1 (S2.1 = adversary) Bob set Z join-closed (one top t), atoms a_1..a_k ∈ U_w, every leaf vanishing on Z is 1 on
  ≤1 atom. Adversary state = (block of atoms) × Z. An AND node cannot split Z (the top t lies in one child, whose
  Bob side then contains all of Z); an OR node splits the atoms. ≥ k−1 OR nodes where two blocks meet.
2.2 (S2.2 = cross pairs) A node reached by the adversaries of roots a and b with states A_a×Z_a, A_b×Z_b has a
  canonical rectangle containing A_a×Z_b: every atom of a in play is ≰ every point of Z_b. That is all of S2.2.
2.3 AND-WITNESS LEMMA (new, PROVED-PAPER). Let g vanish on Z_a ∪ Z_b and g(α)=1, and suppose no input variable
  vanishing on Z_a ∪ Z_b is 1 at α. Then some AND gate G, reachable down from g through wires vanishing on
  Z_a ∪ Z_b, vanishes on Z_a ∪ Z_b, has G(α)=1, and has a child that does not vanish on Z_a ∪ Z_b.
  Proof: walk down from g along wires that are 1 at α; the walk ends in an input that is 1 at α, which does not
  vanish on Z_a∪Z_b; the last wire on the walk that vanishes there is a gate whose walk-child does not, so it is
  not an OR. ∎  (Game form: the adversary holding {α} × (Z_a ∪ Z_b) must pass a Bob-splitting node.)
  Use: every collision of S2.2 has AND gates below it, and AND gates lie in no merge class. What fails in general
  is multiplicity: one AND can serve many pairs (a,b) when the minterm of h inside the atom is large.

## 3. DEFECT FORM (deliverable 2, general h)  PROVED-PAPER + CHECKED
Canonical ("honest") class of w: V**_w = {wires ≤ Ω_w} = wires vanishing on ALL of Bob's set V_w.
Atoms: α_u = (e_u, 1) if h(e_u)=0, (e_u,0) if h(e_u)=1 (real points, in U_w). B_w(ξ) = {u : ξ(α_u)=1}.
3.1 PRIVACY IS FREE: ξ ∈ V**_w ∩ V**_w' ⇒ B_w(ξ) ⊆ S_w ∩ S_w' (ξ(α_u)=1 ⇒ Ω_w'(α_u)=1 ⇒ u ∈ S_w', because the
  level of α_u is ¬h(e_u)). Inputs in V**_w: exactly x_u, u∈S_w (y ∉ V**_w since Ω_w(0,1)=h(0)=0).
3.2 Union-find over V**_w in circuit order: OR ⇒ both children in V**_w; AND T=σ∧τ: either a child is in V**_w
  (blocks inherited) or NEITHER is ("split AND", Bob-splitting node of 1.1); then merge all blocks met by B_w(T);
  m_w(T) := (#blocks met) − 1.  Honest merges HM_w = OR gates joining two blocks.
  IDENTITY: |HM_w| + Σ_T m_w(T) = d_w. HM_w pairwise disjoint (3.1); a split AND with m ≥ 1 has |B_w| ≥ 2, so it
  has a defect for one w only. With SD = {split ANDs with m ≥ 1}, rest = gates of M not in ∪HM_w ∪ SD:
     s − 1 − base = #rest − Σ_{T∈SD} (m(T) − 1).
  So 951 ⇔ Σ_{T∈SD}(m(T)−1) ≤ #rest for every lifted circuit ("defect repay").
3.3 CHECKED (defect.py, rundef.py): identity + privacy asserts pass on 3600 circuits of data-fixh16 (n=4, all
  pair sets, 2291 with a split AND, excess 0 trivially) and on 21 front example circuits n ≤ 9 (cfgI, cx44_*,
  cxT2, cxe3, cxstar5/44, cxP1,3,4,5,6, pg3_ess43, tw/*, srepay_ref/*): excess up to 5, rest−excess ≥ 3.
  (cxT4, cxP2 skipped: n ≥ 15.) These circuits were copied from branch front-match to scratchpad, not stored here.
3.4 Relation to S-repay and to the referee's report (coordinator note): this is a MERGE-SET form with a
  canonical selection (no configurations, no LP). It is not whole-class S-repay (REFUTED by front's referee,
  v2whole_cx.json) and it is not Lemma J: the Bob set is all of V_w, whose tops (z_S,0), (c,1) have weight ≥ 2
  in general, so weight-≥2 inputs enter through "ξ ≤ Ω_w". But like the referee's R6/R8 it is an identity, i.e.
  a restatement of s−1 ≥ base; its content is only WHERE the deficit sits: at ANDs T=σ∧τ ≤ Ω_w with σ,τ ≰ Ω_w
  (σ is 1 at a forced zero z1, τ at z2, z1∨z2 not a forced zero — K_{2,2}-type or cross-world).
3.5 Relation to the "chist" lane (fractional rectangle coverings): no weights are used here; the rectangles
  atoms × V_w are the per-root semantic rectangles, used integrally. I did not go into fractional charging.

## 4. h below a variable  PROVED-PAPER (not new: instance of Theorem X / type-1 families)
If h ≤ x_a (e.g. h = x_a∧x_b): {x_a=0} ⊆ U0. Classes: w ∋ a: {g: g^1 ≤ o_w everywhere, g^1(e_u)=1 for ≥2 u∈S_w}
(C1 computes o_w exactly: its zeros have x_a=0); w ∌ a: {g: g^1 ≤ o_w on {x_a=0}, g^1(e_u)=1 for ≥2 u∈S_w}.
Each has ≥ d_w OR gates (Mehlhorn on a cube); a common gate would give two units in S_w∩S_w'. So s ≥ base+1.
The suggested target "h = single AND of two variables" is therefore closed and uninformative.

## 5. h = x_a ∨ x_b  (PARTIAL, new)
Set types: A (∋a,∌b), B (∋b,∌a), N (neither), at most one AB (⊇{a,b}). π := #points p∉{a,b} on an A-set and a B-set.
5.1 PROVED-PAPER no function-level private family in general: all-type-0 classes collide on every A/B pair
  (atom e_b+e_u always hits a B-set); all-type-1 classes collide on A/B pairs sharing a point; mixed types are
  unblocked (S2.3 of s_fable). If π = 0 the type-1 family is private (Theorem X).
5.2 Configuration (W1 with REAL atoms): c_w = complement of S_w∪{a,b}; Z_w = ↓(c_w,1); atoms (e_a,0), (e_b,0),
  (e_u,1) for u∉{a,b}. (L) holds. R_w = wires vanishing on Z_w with a path to F_w inside such wires; union-find on
  R_w gives merges Mg_w, |Mg_w| ≥ d_w (S2.1; R_w is closed under the children the proof uses).
5.3 PROVED-PAPER crossing table: ξ vanishing on Z_w' has B_w(ξ) ⊆ P(w|w') = S_w ∩ (S_w'∪{a,b}).
  ⇒ a gate is in ≤ 2 merge sets; g ∈ Mg_w ∩ Mg_w' only for an A-set w and B-set w' with S_w∩S_w'={p};
  then B_w(g)={a,p}, B_w'(g)={b,p}, g(e_a,0)=g(e_b,0)=1 (so g ≥ h on level 0, e.g. g = h∨x_p), and for fixed w
  the points p are distinct. K := #colliding gates ≤ π.  (Virtual atoms (e_a,1) would allow junk g=(y∧h)∨x_p.)
5.4 PROVED-PAPER half repay: #gates outside ∪Mg ≥ K/2, hence s − 1 ≥ base − ⌊K/2⌋.
  Proof. Fix an A-set w with collisions g_1..g_k (points p_i). F_w(e_b,0)=0 and g_i(e_b,0)=1, so on the path
  from g_i to F_w inside R_w (fixed parent map) there is a first AND T_i; before it only ORs, all ≥ g_i, so they
  have p_i,a ∈ B_w. No g_j lies on the chain of g_i (B_w(g_j)={a,p_j}). The chains form a forest:
  #chain tops + #junction ORs ≥ k. A junction OR has children with p_i resp. p_j and both with a: same block, not
  a w-merge; it has p_i,p_j ∈ B_w, so it vanishes on no other Z_v (|P(w|v)∖{a}| ≤ 1): outside every merge set and
  private to w. A chain top is a child of an AND and determines w (p_i ∈ B_w), so each AND carries ≤ 2 tops.
  K ≤ #junctions + 2·#ANDs ≤ 2·#outside. ∎   The gate h and the AB-set need no special care (AB-set never collides).
5.5 STUCK HERE (exact): the factor 2. An AND T = ξ∧ξ' may be the first AND for two chains (two A-sets, or two
  chains of one A-set). Such T is still 1 at (e_b,0) and (e_a,0), lies in R_w ∩ R_w', has lost p_i and p_j, and
  the path above it must hit a further AND killing (e_b,0). Charging the second collision to that later AND is
  the natural repair, but after the first AND the path wires carry no atom of w other than a, so (i) different
  A-sets' paths can run together, (ii) an OR junction above T can be a genuine private merge of a third set
  (example: J = (h∨x_p1)∨(h∨x_p2) is a merge of an N-set through p1,p2), (iii) a later colliding gate can sit on
  the path (g_3 = T∨x_p3). I found no potential that survives all three. CONJECTURE H2: K ≤ #outside, i.e.
  s ≥ base+1 for every circuit with h = x_a∨x_b.
5.6 CHECKED (hor2.py, seeds 1,2: 6000 constructed correct lifted circuits, n ≤ 10, mixes of honest sets and
  multiplexed sets F_w = (∨ shared (h∨x_p)) ∧ (y ∨ T_w); 4543 with collisions, K up to 6): every statement of
  5.2–5.4 holds as an assert; min(#outside − K) = 1, so no evidence against H2. Constructed family only: this
  is weak evidence, not an exhaustive search.
5.7 Corollary PROVED-PAPER: h = x_a∨x_b and π ≤ 1 ⇒ s ≥ base+1; π ≤ 3 ⇒ s ≥ base (951 for these circuits).

## 6. Why the game view lands on the same obstruction (deliverable 2, negative part)  PROVED-PAPER as analysis
An adversary for root w must choose what to hold on Bob's side.
 (i) a join-closed part Z (one top): never split, coverage d_w is automatic (2.1), but nodes are shared between
     roots whenever cross pairs exist (2.2) — front's S-repay, collisions between classes;
 (ii) all of V_w: sharing is impossible (3.1), but Bob is split at AND nodes and coverage is lost there (3.2).
(i) and (ii) are the two ends of one trade-off; the total deficit is the same number, s−1−base+…, in both.
In (ii) it is Σ(m(T)−1) over split ANDs; in (i) it is the collision count. The game language adds 2.3 (collisions
cost AND nodes) and the canonical form 3.2, not a new invariant: Sokolov's equivalence is node-for-node, so every
adversary argument is a top-down circuit argument. What a proof still needs is a bound on how many roots/pairs one
Bob-splitting node can serve; for h = x_a∨x_b that number is 2 (5.4) and the missing step is to bring it to 1.

## 7. Not done / next steps
- Th_2 on two complementary 4-sets was not attacked as an isolated system: it is a hyperforest (Lemma J / R4 of
  the referee already give s ≥ base+1 there), so it only makes sense as a local pattern inside a core system.
- Next for S5: a potential over ANDs that are 1 at both (e_a,0),(e_b,0) ("h-like ANDs"), counting b-kills and
  a-kills separately (every colliding gate must lose (e_b,0) on the way to F_w AND (e_a,0) on the way to F_w').
  5.4 uses only the first; using both simultaneously is the unexplored slack.
- An exhaustive small-case search for H2 (SAT, h pinned to x_a∨x_b, π ≥ 2) was not run.

## 8. FOLLOW-UP: THEOREM H2 (closes 5.5)   PROVED-PAPER, steps CHECKED by code; not in Lean, not refereed
THEOREM H2 (FJ form). Let h = x_a ∨ x_b. Any monotone AND/OR circuit M over (x,y) with outputs
o_w∧(y∨h) ≤ F_w ≤ o_w∨(y∧h) for a (1,1)-disjoint system has ≥ base gates. (h need not be a wire of M and its
cost is not counted: the proof uses only the function h.) Hence a one-NOT circuit whose NOT reads x_a∨x_b has
s ≥ base+1. This is Fable R's conjecture FJ for this h, and a case with no function-level private family (5.1).
What changed against 5.4: (i) merges are defined with DELIVERED atoms, so a colliding gate has a path to F_w that
keeps its private atom p alive; (ii) the charged AND is the b-KILL on that path (not the first AND), which has a
unique b-live child, so two chains can only share it by merging first; (iii) only A-sets pay. The "use a-kill and
b-kill together" idea was not needed.
8.1 Setting as in 5.2: c_w = complement of S_w∪{a,b}; V_w = wires that are 0 at (c_w,1); atoms α_a=(e_a,0),
  α_b=(e_b,0), α_u=(e_u,1) otherwise; "u-live" = value 1 at α_u; "b-live" = value 1 at (e_b,0).
  Δ_w(ζ) (ζ∈V_w) := atoms u of w such that some upward path ζ → … → F_w stays in V_w and u-live.
8.2 Delivered union-find. Process V_w in circuit order, blocks on S_w, invariant "Δ_w(ζ) lies in one block":
  input x_v: ≤1 atom; OR ζ1∨ζ2: both children in V_w and Δ(ζ) ⊆ Δ(ζ1)∪Δ(ζ2) (extend the path by the child that
  is u-live); AND with child σ∈V_w: Δ(ζ) ⊆ Δ(σ). Merge = OR gate whose Δ meets two blocks. Δ(F_w)=S_w, so
  |Mg_w| = d_w exactly.
8.3 Crossing table (5.3 unchanged): a gate is in ≤2 merge sets; g ∈ Mg_w∩Mg_w' only for an A-set w and a B-set w'
  with common point p, and then Δ_w(g)={a,p}, Δ_w'(g)={b,p}; in particular g is b-live. For fixed w the points p
  of its collisions are distinct. K := #colliding gates. Identity: (#gates of M) − base = #outside − K, where
  outside = gates in no merge set. So H2 ⇔ K ≤ #outside.
8.4 Kill ANDs. Fix an A-set w with collisions g_1..g_k, points p_i. As p_i∈Δ_w(g_i) there is a path P_i from g_i
  to F_w inside V_w, p_i-live. g_i is b-live and F_w is not ((e_b,0) is a forced zero of F_w). Let T_i be the
  first wire on P_i that is not b-live and ξ_i its predecessor. T_i is an AND, ξ_i is its only b-live child,
  T_i ∈ V_w and T_i is p_i-live. T_i is in no merge set (AND), and it is not T_j' of another A-set v:
  T∈V_v gives B_w(T) ⊆ S_w∩(S_v∪{a,b}) = {a}, but p_i ∈ B_w(T_i).
8.5 Junction ORs. For ζ∈V_w let λ(ζ) := {j : some upward path ζ → … → ξ_j stays in V_w and p_j-live}
  (j∈λ(g_j), j∈λ(ξ_j)). Union-find on {1..k} over V_w in circuit order, invariant "λ(ζ) in one class": inputs carry
  ≤1 label, OR: λ(ζ) ⊆ λ(ζ1)∪λ(ζ2), AND: λ(ζ) ⊆ λ(V_w-child). Junction = OR gate whose λ meets two classes.
  All j with the same ξ_j end in one class, and T_i determines ξ_i, so  #junctions + #distinct T_i ≥ k.
  A junction ζ=ζ1∨ζ2 has i∈λ(ζ1), j∈λ(ζ2) in different classes, i≠j; hence p_i∈Δ_w(ζ1), p_j∈Δ_w(ζ2)
  (continue the path from ξ_j along P_j). Then:
  (a) ζ is in no Mg_v, v≠w, and is not a junction or kill of another A-set: ζ∈V_v would force p_i,p_j∈S_v.
  (b) ζ ∉ Mg_w. If g_i,g_j both precede ζ: a~p_i and a~p_j already, Δ(ζ1) and Δ(ζ2) lie in the block of a, so
      Δ(ζ) meets one block. If, say, g_j comes after ζ: after ζ the invariant gives p_i~p_j; whichever of g_i,g_j
      is processed last then finds its two atoms {a,p} already in one block and is not a merge — contradiction.
  (c) ζ is an OR, the T's are ANDs.
8.6 Count. The gates of 8.4, 8.5 are outside every merge set and pairwise distinct over all A-sets, and every
  collision involves exactly one A-set: #outside ≥ Σ_{A-sets}(#junctions + #kills) ≥ Σ k_w = K. ∎
  Nothing is charged to B-sets, N-sets or the AB-set (the AB-set never collides).
8.7 CHECKED (h2proof.py = every step of 8.2–8.6 as an assert; all circuits verified against the lifted spec):
  - 4000 constructed circuits (hor2 family, seeds 1,7; 3018 with collisions, K ≤ 5): pass.
  - h2fuzz.py, seeds 1,2: 8007 accepted random mutants (rewire / op flip / gate insertion, kept iff still
    correct; 4325 with collisions, K ≤ 4): pass. min(#gates − base) = 1 over all of them.
  - 300 SAT-generated circuits with 1,3,5 slack gates: pass, but none has a collision (weak test).
  Scope: constructed + mutated circuits, n ≤ 10; no exhaustive enumeration of circuits.
8.8 SAT hunt (sath2.py, sath2_batch.py, log sath2_log.jsonl; Cadical via python-sat; h forced as gate 0):
  random systems with π ≥ 2. Batches 1,2 (120 systems, n ≤ 8, base ≤ 10): UNSAT at G = base−2 and G = base−1
  for all 120 (G = number of gates of M; s = G+1). So no H2 violation and no 951 violation there. At G = base:
  57 SAT / 63 UNSAT; SAT here does not contradict H2 (it is the bound s = base+1 being attained, with h used as
  a real OR gate of the system). Batch 3 (seed 11, 40 systems, 900 s timeout) and the FJ-form run (satfj.py: h not
  forced, G = base−1): results in 8.10. Encoder sanity: G = base+1 SAT, solution verified correct with
  w951.Circuit.verify (imported from /home/user/coord951/tools, not copied).
8.9 Extension to h = OR(P)   PROVED-PAPER (same proof, NOT checked by code).
  THEOREM H3. Let h = OR_{t∈P} x_t. Assume (i) every set meets P in ≤1 point, (ii) every point outside P lies on
  ≤2 sets that meet P. Then every lifted circuit has ≥ base gates.
  Proof = 8.1–8.6 with c_w = complement of S_w∪P, atoms (e_t,0) for t∈P: P(w|v) = (S_w∩P)∪(S_w∩S_v), collisions
  only between sets of different P-types sharing p∉P, Δ_w(g)={t_w,p}; (ii) gives multiplicity ≤2; pick either set
  as payer, it must kill (e_{t_v},0); a kill shared by two payers w,v would force p to lie on both, i.e. the
  same collision. For |P|=1 there are no collisions (Fable R's x_p configuration is this one).
  OPEN for OR(P): (a) a point outside P on ≥3 sets of different P-types: one gate x_p∨h-like can be a merge of all
  of them, and a single AND g∧(y∨x_p) can be the kill for all payers; the missing gates are then the ORs that
  build the multi-t-live child of g, which I could not make private; (b) sets with ≥2 points of P (for |P|=2 the
  single AB-set is harmless, in general wires on P-atoms lie in every V_v).
  R's x_p configuration does not generalise to pairwise DISJOINT classes for two special atoms: g = x_p∨x_a∨x_b
  is a genuine merge of both sets through p in any such configuration; the repay 8.4–8.5 is what replaces it.
