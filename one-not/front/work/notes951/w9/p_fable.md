# p_fable.md — task P: the Π* private-class matching (C2/Π*), restart-safe log
Tools: w9/p/plib.py (independent truth-table evaluator, classes, matching, builder), chk1.py, cxp1.py. Data = Opus J's 2559 + g3 (2561).

## P0 Definitions pinned (all classes are properties of the REAL gate functions; C0 = real on U1, C1 = real on U0)
U0={h=0} (down-set, contains 0), U1={h=1} (up-set). w hard iff h(z_{S_w})=1; easy iff h <= o_w (equivalent!).
 Dr_w  = {g <= o_w everywhere, g(e_u)=1 for >=2 u in S_w}                 (T3 definition; "DrS" = Opus cls2 variant x_u <= g everywhere, smaller)
 Pr_w  = {g >= o_w everywhere, g≢1, g ≱ o_j for j≠w}
 D1_w  = {g <= o_w on U0, g(e_u)=1 for >=2 light u in S_w}               (all sets)
 D0_w  = {g <= o_w on U1, g >= x_u on U1 for >=2 u in S_w}               (hard w only)
 P0_w  = {g >= o_w on U1, g≢1 on U1, g ≱ o_j on U1 for hard j≠w}         (hard w only)
 Π*_w = Dr ∪ Pr ∪ D0 ∪ P0 ∪ D1.
CHECKED (chk1.py, own evaluator): Opus J's numbers reproduce: 0 short sets, matching full on all, one conflict (chk/c.jsonl:1718).

## P1 PROVED — THEOREM E (easy sets are fully served by Dr alone; closes "heavy units of easy sets")
For every easy set w (h(z_{S_w})=0), in ANY correct one-NOT circuit:  |Dr_w| >= d_w.  Moreover D1_w ⊆ Dr_w = M_w (Opus G3.4 class).
Proof. Gatewise C0(g) <= real g <= C1(g) (every gate is monotone in (x,N)). Z := {wires g : real g(z_S)=0}. N(z_S)=1 so
 real = C1 at z_S; C1(g) is a monotone function and every x missing S_w is <= z_S, so g∈Z ⇒ C1(g) <= o_w ⇒ real g <= o_w EVERYWHERE.
 Union-find on S_w over wires of Z in circuit order with blocks B(g) = {u∈S_w : real g(e_u)=1}: variables in Z are x_u (u∈S_w);
 N∉Z; OR gate in Z: both inputs in Z, B = union; AND gate in Z: some input is in Z (real values at z_S), B ⊆ B(that input).
 o_w ∈ Z with B = S_w ⇒ >= d_w merging OR gates, each in Z (so <= o_w everywhere) with |B| >= 2: in Dr_w. ∎
 (Weight>=2 input used: z_S. No cleanness/liveness needed.)
COROLLARY E' (PROVED): s >= Σ_{easy} d_w + Σ_{hard} min(d_w,2)  [Dr_w (easy) and T3's Π_w = Dr_w∪Pr_w (hard) are pairwise disjoint, T3(1)].
 In particular s >= base whenever every HARD set has size <= 3 (any number of hard sets). Improves Opus J "s >= Σ_easy (L_w−1)".
 So the whole residual problem is about HARD sets of size >= 4 (third and later gates).
CHECKED: 3075 easy sets in data: |Dr| >= d in all, D1 ⊆ Dr in all (DrS variant short on 4 sets: use the T3 definition).

## P2 REFUTED — (a) |Π*_w| >= d_w and the Π* matching (C1/C2 of j_cut_opus) — cxP1 (w9/p/cxp1.py, cxP1.json)
n=9, S_a={0,1,2,3,4}, S_c={5,0}, S_d={6,1}, S_e={7,2}, S_f={8,3}; base 8, s=38. Verified: correct, clean, live, C0 wrong, C1 wrong, h(0)=0.
 h = x5x6 ∨ x7x8 (two minterms A, B, both avoiding S_a: a is hard; all units light).
 U0 side (crossing-join junk): K = o_c∨x1∨..∨x4 (= o_a∨x5, every gate >= o_c), K2 = o_d∨x0∨x2..x4 (= o_a∨x6, every gate >= o_d),
   M = (N∧K)∧K2: equals o_a on U0 because x5x6 is in U1 (the crossing join e5∨e6 that RM needs is exactly what fails for hard sets).
 U1 side (minterm split): R_A = ∨_u (x_u∧x5x6), R_B = ∨_u (x_u∧x7x8), F = R_A∨R_B, o_a = M∨F.
 Classes of a: Dr={M? no; o_a + one}, exactly Π*_a = {M, F, o_a}: |Π*_a| = 3 < d_a = 4 for m=5 (and 3 for every m: m=6 gives 3 < 5).
 Matching with Π*: 7 < 8 (m=5), 7 < 9 (m=6).  Mechanism: gates of R_A are >= x_u only on the cone of minterm A, not on all of U1
 (kills D0), K-chain gates are not <= o_a on U0 (kills D1) and are >= o_c (kills Pr/P0).
 Not a core system and s >> base; but every LOCAL hypothesis of the sorry case that can be tested holds (clean, live, essential, h(0)=0,
 all sets hard). So (a) cannot be proved without using s < base (or N2/B8(3)-type minimality) in an essential way.
 (cxP1 detail: Dr_a = D1_a = {M, o_a}, D0_a = P0_a = {F, o_a}, Pr_a = {o_a}.)

## P3 Repair of (a) and its refutation as a matching rule — cxP2 (w9/p/cxp2.py, cxP2.json = m=8)
PROVED (a'): for hard w and every minterm M of h avoiding S_w, D0^M_w := {g <= o_w on cone(M), g(1_M+e_u)=1 for >=2 u∈S_w} has
 >= d_w gates (union-find in C0 on the cube x >= 1_M, top zero z_S; C0 monotone there; this is system Σ(1_M)). So with
 Π**_w := Π*_w ∪ ⋃_M D0^M_w, |Π**_w| >= d_w is a THEOREM for every set (easy: Theorem E).  Conflicts (PROVED, = E0.1(c)):
 D0^M_w ∩ D0^M'_j ≠ ∅ ⇒ M hits S_j and M' hits S_w;  D0^M_w ∩ Dr_a ≠ ∅ ⇒ M hits S_a and g has a LIGHT unit u∈S_a\S_w (crossing e_u → e_u∨1_M);
 D0^M_w ∩ Pr_a = ∅ always.
REFUTED: Hall/matching for Π** (so "per-minterm world-0 classes + T3 + D1 + P0" is not a valid rule either). cxP2(m): n=2m,
 S_1={p,p',u..}, S_2={q,q',v..}, pairs {p,q},{p',q'}; h = x_p x_p' ∨ x_q x_q' (the minterm avoiding S_1 lies inside S_2 and vice versa).
 Pool: y_k = (S_1[k]∧hq) ∨ (S_2[k]∧hp), G = ∨ y_k: its m−1 OR gates are merges of S_1 on cone(hq) AND of S_2 on cone(hp) (multiplexed).
 o_i = (G ∨ sel_i) ∨ W_i, W_i = (N∧K_i)∧K_i'' (crossing junk, K's >= pair outputs).  Private gates per big set: 3; pool m−1.
 m=8 (n=16, s=73, base 16): |Π**_1 ∪ Π**_2| = 13 < 14 = d_1+d_2, matching 15 < 16. m=9: 16 < 18. Verified correct, clean, live, essential.
 (m=5, n=10: |Π*| = 3 < 4 again.)  Free-choice MatchG is NOT refuted: Σ(0) for both big sets gives a full matching (free.py; the
 K-chain gates are counted at z=0). So this is again "a fixed rule fails, free choice survives" (same family as cx1/cxr/cxtw/cxE).

## P4 (b) pairwise disjointness: exact table (w ≠ j; "hard/easy" as needed).  PROVED unless marked.
 Dr–Dr, Dr–Pr, Pr–Pr: ∅ (T3).            D1–D1: ∅ (light u∈S_w\S_j, e_u∈U0).      D1_w–Dr_j: ∅ (same u).
 D0–D0 (both hard): ∅ (u∈S_w\S_j, point z_{S_j}∈U1).   D0_w–P0_j: ∅ (point z_{S_w}∈U1).   P0–P0: ∅ by definition.
 D0_w–Pr_j: ∅ (z_{S_w}).   D0_w–Dr_j, j HARD: ∅ (z_{S_j}).   P0_w–Dr_j, j HARD: ∅.   P0_w–Pr_j: ∅ (j hard: definition; j easy: g≡1 on U1).
 For easy w: D1_w ⊆ Dr_w, D0_w = P0_w = ∅.
 NOT disjoint in general (all are two-world "multiplexer"/heavy-point effects; each needs a crossing pair):
  (x1) D1_w–Pr_j: possible iff S_j\S_w is all heavy.  REFUTED by cxP3 (n=5, S_a={1,2,3,4} hard, S_c={0,1}, h=x0, s=14: K-chain gates
       o_c∨x2, o_c∨x2∨x3 ∈ D1_a ∩ Pr_c; correct, clean, LIVE, essential). So Opus' single data exception is not a junk artefact.
  (x2) D0_j–Dr_w and D0_j–D1_w, w EASY, j hard: REFUTED by cxP4 (n=6, S_w={0,1,2} easy, S_j={3,4,5} hard, h=x0, s=16):
       g = (N∧x1 ∨ x0∧x3) ∨ (N∧x2 ∨ x0∧x4) ∈ Dr_w ∩ D1_w ∩ D0_j; clean, live, essential.
  (x3) P0_j–Dr_w (w easy), D1_w–D0_j, D1_w–P0_j (both hard): function-level possible by the same multiplexer g = N∧A ∨ h∧B
       (not built separately).
 None of these small conflicts breaks the MATCHING by itself (cxP3, cxP4 have full Π* matchings); the matching breaks by P2/P3.

## P5 REFUTED — (a) already for 4-sets, and inside a CORE system
cxP5 (w9/p/cxp5.py, cxP5.json): n=8, S_a={0,1,2,3}, pairs {4,0},{5,1},{6,2},{7,3}, h = x4x5 ∨ x6x7, s=32, base 7.
 o_a = P∧K2, P = ((N∧K)∨R_A)∨R_B, K = o_c∨x1∨x2∨x3, K2 = o_d∨x0∨x2∨x3 (T3 configuration (II'): R=P private, C=K2 shared).
 Π*_a = {P, o_a}: |Π*_a| = 2 < 3 = d_a (same for every m: m=5 gives 2 < 4). Π* matching 6 < 7. Correct, clean, live, essential, h(0)=0.
cxP6 (cxp6.py, cxP6.json): the same gadget in the n=9 CORE system {0123},{045},{146},{256},{347},{157},{068},{278},{358}
 (every point in >= 2 sets of size >= 3), h = x4 ∨ x5x6, the K-chains start from the TRIPLE outputs o_{045}, o_{146}; s=43, base 19:
 |Π*_a| = 2 < 3, Π* matching 18 < 19; correct, clean, live, essential, h(0)=0, 7 hard sets. So hcore/h4/hhard do not help;
 only s < base (σ>=1: N2, B8(3), G1.x) is left as a hypothesis that could exclude it, and that cannot be tested (s=43 >> 19).

## P6 PROVED — small positive lemmas for hard sets
(H1) heavy-unit lemma: a hard set with k heavy units has |D0_w| >= k−1 (union-find in C0 at z_S with atoms e_u, u heavy: C0(g)(z_S)=0
     ⇒ C0(g) <= o_w everywhere ⇒ g <= o_w on U1; C0(g)(e_u)=1 ⇒ g >= x_u on U1).
(H2) if ALL sets are hard: Dr_w ∪ Pr_w ∪ D0_w ∪ P0_w are pairwise disjoint (table P4), so s >= Σ_w |Dr∪Pr∪D0∪P0|.
     The only conflicts of these four families are Dr_easy–D0_hard and Dr_easy–P0_hard (cxP4).
(H3) (a') per-minterm classes, P3.   (H4) Theorem E / E' (P1).
CHECKED (rnd.py): 1415 random two-world circuits on the n=8 and n=9 core systems (4183 easy, 6437 hard sets): Theorem E, D1⊆Dr (easy),
 (H1), (a'), and every "∅" entry of table P4: 0 failures.  (No SAT runs: an essential-NOT circuit near base on a core system
 (n>=8, base>=13) is far outside a 5-minute pysat budget; the lemmas are proved, the refutations are explicit.)

## P7 Exact gap
After P1: easy sets cost nothing more (d_w private gates each, function-level). Open = HARD sets of size >= 4 only: the third and
later gates. For a hard set every provable full-size class is a world class at a base point: Σ(1_M) (M minterm avoiding S_w; U1 side)
or Σ(z_Q) with h(z_Q)=0 (U0 side, gates <= OR(Q) everywhere by the Theorem E argument); such classes of two sets collide exactly when the
base points hit each other's sets (E0.1), and the sorry case (no Theorem X family) says a collision-free choice does not exist.
cxP1/cxP5/cxP6 show that a hard set's U0 side can be reduced to ONE class gate (crossing junk) and its U1 side to ONE class gate (minterm
split) at the price of ~3d junk gates; cxP2 shows per-minterm classes can be pooled across two sets by multiplexing.
In all these circuits free-choice MatchG holds (Σ(0) sees the K-chains). So: any FIXED finite list of function-level classes is refuted;
what is still unrefuted is only free choice over all Σ(z), i.e. the original open statement. A proof must charge the junk
(K-chains, R-chains, y_k) — i.e. be a counting/induction argument using s < base — not a class-matching rule.

## PNP-SUBPROBLEM LINKS (f_G = OR_t x_t∧OR(N_t), C4-free G, unlimited NOT; glanced at pnp_sub/)
- No lemma here gives a lower bound for f_G directly: Theorem E needs the sandwich C0 <= real <= C1 of ONE NOT and outputs that are
  themselves the sums. In f_G the sums OR(N_t) appear only after the restriction x_t=1, x_{V\N[t]}=0, one t at a time; the restricted
  circuit then needs >= deg(t)−1 gates (trivial), and different t use incompatible restrictions.
- Transferable negative message: class-matching ("private gates per neighbourhood") is refutable by two-world multiplexing with a single
  NOT (cxP2: g = hq∧OR(A) ∨ hp∧OR(B) merges for two sums at once); with free NOTs a selector x_t is available for every star, so
  a lower-bound proof for f_G via private gate classes per star should be expected to fail the same way; gate elimination
  (Red'kin style, the analogue of R0/N2 here) is the method that survives in both problems.
- Transferable positive tool: the union-find at the top zero point z_S of a restricted MONOTONE sub-world (G3.3/Theorem E) — in a
  subcube where a circuit for f_G is monotone in the remaining variables (e.g. all NOT-inputs constant there) it yields deg(t)−1
  gates <= OR(N_t) with >= 2 units, pairwise disjoint over t for C4-free G (two common neighbours = a C4). Their girth-5 data
  (|E|+τ−1 attained) is consistent with that count plus one AND and one OR per cover vertex; nothing in their data was used here.
