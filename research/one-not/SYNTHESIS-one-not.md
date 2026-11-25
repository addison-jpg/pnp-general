# 951 in three layers (front's draft, 2026-11-24 ~12:27 UTC)

Sent by front (session_01GmnDheKL3UENhJCL6pD1hS) by message for research/SYNTHESIS.md §3-4; landed by coord
(front cannot push; owner 12:05). Front's text, verbatim except headings. A2's 13:15 HEAVY-COUNT
result will come as a short delta. Coord checked that every Lean name in layer 1 exists on main and
that the full build has 1 sorry (no_minCE) with standard axioms.

## 0. The whole chain in one paragraph

951 (one NOT gate saves nothing on (1,1)-disjoint Boolean sums) is reduced in Lean to no_minCE, and
no_minCE to ONE counting statement about the circuit's two monotone worlds. Every set w gets a menu
of "classes": merge sets of a union-find run in the LIFTED monotone circuit M(x, y) (y replaces the
NOT); each class has exactly d_w = |S_w| − 1 gates (Lemma M / GM'). If the union U of all valid
classes has at least base = Σ d_w gates (MU / MUL), the circuit has at least base gates. Front's
contribution: (a) the menu machinery that makes the reduction sound (Lemma R, L-LIFT, Theorem U);
(b) the inductive counting form STAR-COUNT that peels one star (the sets through a point v) per
step, whose heavy half HEAVY-COUNT has 0 failures on all data; (c) the lifted price route (2G-LIFT).
Remaining maths (as of 12:27): two counting lemmas, HEAVY-COUNT (front, A2) and LIGHT-COUNT (integrator's Opus). UPDATE 12:42: over UC, LIGHT-COUNT is FALSE for general circuits (PAPPUS-JUNK, s = 66, base 18; UC-MU still holds there); the heavy case transfers to UC on data (34,387/34,387). Candidate repair: count F2 (real witnesses only, F2 ⊆ UC), which passes MU and the step on everything tested so far, PAPPUS-JUNK included (tight); decision at 13:30.

## 1. Layer 1 — THEOREMS (Lean, all gated, std axioms, only sorry = no_minCE)

- no_minCE ⇐ MUL (base ≤ |⋃ liftMenu|): `no_minCE_of_MUL` (fb5dfef)
- MUL ⇐ LiftSDR ⇐ MergeSDR (L-LIFT: real merge sets are lifted classes): `liftSDR_of_mergeSDR`,
  `muL_of_mergeSDR`, `run_lift` (cc21bf9)
- no_minCE ⇐ ∀ Q ∃ v StarCountG over menu2 (peeling induction): `no_minCE_of_starCount2`,
  `sum_alive_le_UQG` (d6c12cf)
- no_minCE ⇐ PurePrice (LP dual of the fractional form): `no_minCE_of_purePrice`,
  `pureFrac_iff_purePrice` (ca2412c)
- StarSep ⇒ PureSDR ⇒ PureFrac ⇔ PurePrice ⇒ MU ⇒ MUL ⇒ no_minCE (PureStar, PureMenu, PureGP)
- heavy case of STAR-SEP: `starSep_heavy`, `starSep_of_hQ` (5f87562); L-U_v: `menu2_U_zero`
  (621e1bf); GP + Theorem U: `disjoint_gp` (7faa424); menu transfer under 0/1 restriction:
  `restrictedMenu*_subset_pureMenu`, `restricted*_deficient` (660700f, e73f27c)
- (added by coord) MU over the count-set union UC: `no_minCE_of_MUC`, the point inductions with the
  gain as hypothesis `no_minCE_of_gainOne` / `_gain` / `_gainOne_pts`, Lemma C0 `card_C0_le_gain`
  (machines-Lean, MUInduct.lean, 1bc66bd + 96d1932)

Paper (refereed by front's lane C unless marked): Lemma R (restricted classes = original classes at
(Z ∪ R1, a ∪ R1), extended menus); L-LIFT; GM', Theorem U, Theorem ND (= GP form of
bound_of_noDD); STAR-SEP ⇒ SDR and STAR-COUNT ⇒ MU inductions (only Q changes, never the circuit,
so MinCE facts may be used); the heredity inequality is CIRCULAR; graph systems are vacuous
(MinCE.has4); B1 (in a MinCE the whole family is Hall-deficient; heredity only reduces to the
spanning family); 2G-LIFT (NOT yet refereed): Σ_w min_z |M_z(w) ∩ {g, g'}| ≤ 2 under condition
C(b), proof = ceilings + pigeonhole force a triangle, then an odd-cycle contradiction; graph-system
heavy v reduces to a Hall step inside the star; B3' (not refereed): type-B I0 classes lie at or
before the wire h.

## 2. Layer 2 — CERTIFICATES AND DATA

- HEAVY-COUNT over Menu2 (every heavy v): 44,093/44,093 corpus + 64/64 barrier, 0 failures.
- STAR-COUNT (∃ v) and MU over Menu2: 100% on 21,699 corpus instances (incl. cxMU_dd, selector
  path, cxT2, PG(2,3)) and 36/36 barrier instances.
- GP-SDR on every circuit run (incl. all barriers); U-certified GP selection on 29,751/29,753
  (fails only on cxT2, cx44_1, all sets DD).
- BARRIER SUITE (refutes every minimality-free statement over Lean's narrow menus; fine over
  lifted/GP menus; run new conjectures here first): cxMU_dd, cxMU_clean2, cxMU_clean2_DD,
  cx44_1_junk (`research/one-not/data/witnesses/`).
- REFUTED (witnesses on board / DEAD_ENDS): heavy-star world rules; bounded local exchange (selector
  path); D1/D+; CANON; PEEL; looseness lemma; STAR-SEP (SDR form) over Menu1 and Menu2; V-COUNT;
  cxT2's '2-SAT core' (artefact of minimal atoms).

## 3. Layer 3 — PREMISES AND MAPS

- HEAVY-COUNT (front A2): h(Q ∪ e_v) = 1 ⇒ |U(Q) \ U(Q ∪ v)| ≥ Σ_{w ∈ star(v)} d_w over Menu2.
  Map: on the cube Q ∪ v the NOT is constant (h ≡ 1), so U(Q ∪ v) consists of MONOTONE (C_0) classes
  at top_w', all 0 at (Q + e_v, world 0) (L-U_v): a classical monotone-type count ('the star pays
  d_w gates the monotone remainder cannot see'), with the twist that some paying gates are 0 at
  Q + e_v (V-COUNT refuted), so the count must use classes, not single points. Graphs: a Hall step
  inside the star.
- LIGHT-COUNT (integrator's Opus) — FALSE over UC for general circuits (PAPPUS-JUNK, 12:40); candidate repair F2. Original statement: no heavy alive point ⇒ some v satisfies STAR-COUNT. Data hint:
  every set is private on all 1,019 no-heavy-point corpus circuits (B) — likely the easier half.
- Alternative (A1, lifted price form): ∀ π ≥ 0, Σ_w min_z π(M_z(w)) ≤ π(U); proved for 1-gate
  prices and 2-gate prices under C(b); the 2-gate proof is a PARITY argument (odd triangle), not
  uncrossing; a k-gate version needs an odd-cycle / 2-colouring statement on the hypergraph of
  pairwise intersection points; the open 2-gate configuration is cxT2's.
- Diagnosis (B): every obstruction seen is a HEAVY-POINT HUB (world 1: a wire with C_1 ≥ x_p ∨ h
  merging for every set through p; world 0: one gate merging the heavy atom {u} for every set
  through u) — exactly the HEAVY / LIGHT split.

## 4. Barrier check per technique (honest)

951 is a LINEAR bound in a restricted model (AND/OR + one NOT) for an explicit family; the three
barriers concern super-polynomial bounds / class separations, so none blocks 951; the real question
is whether the techniques scale.

- Union-find merge counting (Lemma M, classes, MU/MUL, STAR-COUNT). Oracle: does not relativize and
  need not — an oracle gate could compute all outputs at once (s ≥ base false), so a proof must
  inspect AND/OR semantics, which ours does. Low-degree extension: the argument evaluates gates only
  at Boolean cube points and uses monotonicity (g_0 ≤ g_1, h monotone); meaningless for gates
  computing field extensions — not algebrizing, not ruled out. Natural proofs: the property ('a
  (1,1)-disjoint Boolean sum needs ≥ base gates') is not LARGE and is circuit-specific — not
  natural, not ruled out. Scaling: k NOT gates give up to 2^k worlds (lifted cube {0,1}^k), so the
  method degrades with k; with O(log n) NOTs (Markov/Fischer) circuits are general up to poly
  blow-up and counts are linear at best — no route past linear general bounds; its value is the
  one-NOT / small-k rung.
- Lifted price / LP duality (PurePrice, 2G-LIFT): same assessment; the parity step is a design
  fact, not a random-function property.
- Restriction / heredity (Lemma R): classical gate elimination; used only for menu transfer, known
  to give linear bounds at most.

Bottom line: the 951 chain is barrier-free (no barrier applies) and barrier-bounded (no technique
here goes past linear for general circuits).

## 5. The ladder's big picture (scaffold, 12:30; landed by coord)

Data: 2,159 essential one-NOT circuits on PG(2,3) (v = 13, base 39) and 65 on AG(2,4) (v = 16,
base 60), all correct, slack s − base = 4..8; Fano v = 7 and AG(2,3) v = 9 at slack 1..5 found
nothing in 30-40 min per size (not UNSAT). So this is about near-minimal circuits, NOT s < base.
U below is the union of NARROW pure classes (I1 at maximal h-zero Z, I0 at top_w).

1. **The count is tight at the merge layer; the slack is NOT-gadget overhead.** MU = |U| − base ∈
   {0, 1, 2} on every ladder circuit while s − base = 4..8: each circuit is a monotone merge
   skeleton (about one d_w-gate class per line) plus a NOT gadget that never merges in any pure
   world (gates outside U: about 4.2 per circuit — the NOT, ANDs gated by N, other ANDs, some ORs).
   U does use 2-3 N-dependent merges: the NOT does not save merges, it moves a few. Tight circuits
   (MU = 0, 8%) occur at every slack.
2. **Hub structure.** h is almost always one point (the hub u) or an OR of 2-3 points. Lines through
   u are type B (world-1 class at top_w); the other q² lines are type A (u ∈ top_w). On
   28,066 / 28,067 sets the I1 class is unique, at Z = top_w − {u}, and for most type-A lines it
   EQUALS the I0 class: both worlds merge the line at the same gates.
3. **Sharing is rare, local and paid for.** Shared U gates: 0 on 1,975 circuits, 1 on 182, 2 on 2.
   A shared gate has the world-switching shape g = (y ∧ A) ∨ (¬y ∧ B) (merges line a in one world,
   line b in the other); the line gets a second class, net |U| change 0. Long chains of switching
   gates (selector path) need an off-plane system; none on planes.
4. **Point deletion is almost free; the hub is always good.** x_v := 0: MU = MU'_v + (lost − new −
   deg v) exactly; the step holds at every point on 2,106 / 2,159 circuits and at ≥ 11 of 13 on
   all; all 60 bad points are NON-hub; deleting a heavy point is always good (narrow menus; for the
   count-set union UC the x_v := 0 route is dead, see the Fable's N1).
5. **MUL and the next rung (speculative).** The barriers (cxMU_dd) are the opposite regime: high
   slack, junk gates that collapse classes. The real enemy is a long chain of world-switching
   gates; with one NOT there is one selector y. With 2 NOTs (4 worlds, selectors y1, y2) a switching
   gate can serve up to 4 lines and chains can branch; prediction: on planes the count stays
   tight; where 2 NOTs could beat base is a 2-selector selector path. Proposed later tests (after
   the 13:30 convergence, per the owner's no-new-routes rule): MUL with 4-world lifted classes on a
   2-NOT PG(2,3) circuit with two hubs; a 2-selector selector path.

## 6. A2's final HEAVY-COUNT delta (front, 12:31; front's lanes are now all stopped)

1. GRAPH SYSTEMS, heavy v — PROVED ON PAPER, two constructions: (G1, inside Menu1 ⊆ menu2) if
   h(X ∪ {a}) = 1 for every light neighbour a (X = V \ ({v} ∪ L); automatic when another point is
   heavy over Q), the I0 classes at top_va with m_v = Q ∪ {v}, m_a = X ∪ {a} (light) / Q ∪ {a}
   (heavy) are pairwise distinct v-gates, hence STAR-SEP and STAR-COUNT at v; (GL, in liftMenu_Q,
   NOT in menu2) lifted classes with zero point (Q ∪ N[v] \ {v,a}, y_a), atoms (Q + e_v, 0),
   (Q + e_a, t_a) are distinct v-gates unless two light neighbours both have C_1(o_va)(z_a) = 1.
   Data: G1 ∨ GL covers 35,069 / 35,069 graph-heavy instances; the residual case (v the only heavy
   point, two light neighbours with C_1 wrong at their points) never observed, open.
2. MENU DECISION (pending at coord): GL needs liftMenu_Q := lifted classes with zero-point x-part ⊇ Q
   and every atom x-part ⊇ Q (monotone, sound, L-U_v holds). Front recommends running the
   STAR-COUNT / MU induction over liftMenu_Q; then LIGHT-COUNT must be stated over it too.
3. |S| ≥ 3 still open: on cxMU_clean2 (v = 1) the gain is 4 ≥ 3 but only one new gate is a v-gate;
   the rest come from non-v merges of the star class and from a NON-STAR class (output of
   {0,4,5,6}) that disappears in the cube Q ∪ v.
4. REFUTED (front's own suggestion): 'merge sets of different sets at a common zero point are
   disjoint' — 178 / 24,108 coincidences, e.g. chk/c#1174.

Referee (desktop Coord, 12:31): 2G-LIFT (A1 §8 Theorem 2G-b, §9 2G-lift) CORRECT; open: cxT2-type
triples; cTAHG to state it in Lean.

## 7. Rung 2 and the MUL hunt (scaffold, 12:49; landed by coord)

All numbers use EXACT lifted menus (PureGP semantics, full enumeration). With k NOTs every NOT
output is its own free coordinate: lifted cube {0,1}^(n+k).

**MUL hunt (1 NOT).** Random walk over CORRECT one-NOT circuits (moves: rewire an input slot, insert
a junk gate, a → (a ∧ N) ∨ (a ∧ h), prune dangling gates; objective: minimise |⋃ liftMenu| − base;
starts cxMU_dd, cxMU_clean2, selector50, ~8 min each). Best: margin 0 (TIGHT, not violated) at
s = 90, base 6, slack 84 (cxMU_clean2 lineage; LiftSDR exists), but there the NOT had become
INESSENTIAL. CORRECTION (scaffold 12:50): every record with margin 0-3 has an INESSENTIAL NOT; best
with an ESSENTIAL NOT: +4 at slack 80 (selector50 lineage), +5 at slack 54 (cxMU_dd lineage). No negative margin. Reading: junk
gates that never merge cost nothing in MUL, so MUL can be tight at any slack; breaking it needs
classes to COLLAPSE below base, which random junk did not achieve.

**Rung 2 (2 NOTs).**
- (b) Selector path with 2 selectors: sets = the 6 edges of K4 (cyclic), selectors y1 = x4, y2 = x5 in
  no set, NOTs on both, 4 worlds with shifts t ∈ {0,1,2,3}; trap g_j = ⋁_world (lit ∧ OR(e_{j+t})),
  o_j = ⋁_world (lit ∧ g_{j−t}). Correct, BOTH NOTs essential, n = 6, s = 138, base 6: MUL margin
  +54, menus 36-52 per set, LiftSDR exists (1-selector version, s = 61: +18).
- (a) Two hub points on a plane (Fano; PG(2,3) with 2 NOTs is 2^15 lifted points, infeasible
  exactly): hubs 0 and 1 as selectors, NOTs on x0 and x1, each world a random permutation of the 7
  lines. Correct, both NOTs essential, s = 216, base 14: MUL margin +51 / +49, LiftSDR exists (1-hub
  analogue, s = 99: +19 / +21).
- Reading: 4 worlds make the lifted menus BIGGER (each world adds its own test systems), so these
  world-switching constructions move MUL AWAY from failure; a rung-2 threat would have to collapse
  classes across worlds. Next, if wanted: a mutation hunt from the 2-selector path with both NOTs
  essential (~10 min, exact menus ~2 s each). Scaffold's scripts: liftk.py, hubs.py, hunt.py (its
  scratchpad).

