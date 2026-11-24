# The big picture, first rough account (integrator draft, 2026-11-24)

Nothing here says P versus NP is settled, and nothing says L-meta-951 is proved. L-meta-951 says: one
NOT gate saves nothing on Boolean sums (circuits of AND, OR and one NOT; (1,1)-disjoint sums; a sum with
sets S_w needs at least base = sum of d_w = |S_w| - 1 gates). Status words: "checked" = Lean accepted;
"kernel-checked on N" = a `decide` certificate per circuit; "tested on N, 0 failures" = corpus data that
could have killed the lemma, which is not a proof; "refuted" = a witness exists. Sources: SYNTHESIS.md,
BOARD.md, 951/DEAD_ENDS.md, 951/SYNTHESIS_951.md, the two agent notes named in section 1.

## 1. The chain, top to bottom

1. **L-meta-951**: reduced in Lean to `no_minCE` (no minimal counterexample exists). `no_minCE` is the
   ONLY sorry in the 951 build (coord-verified; axioms include sorryAx because of it). Not proved.
2. **`no_minCE` follows from a counting statement.** Checked in Lean, each a theorem whose hypothesis is
   still open: `no_minCE_of_MUL` (base <= |union of the lifted class menus|); `liftSDR_of_mergeSDR`,
   `muL_of_mergeSDR`, `run_lift` (real merge sets are lifted classes); `no_minCE_of_MUC` (base <= |UC|, UC
   = count-set union: every OR gate false at a zero point Z of some set and true at Z + e_u for two u of
   it, in one monotone face; sufficient on its own because sum d_w <= |UC| <= s); `no_minCE_of_pureSDR`,
   `no_minCE_of_MU`, `no_minCE_of_purePrice` (LP dual), `no_minCE_of_starCount2`; and the point inductions
   `no_minCE_of_gainOne` / `_gain` / `_gainOne_pts` in `MUInduct.lean`, which take the GAIN as a hypothesis.
   Underneath: union-find Lemma M / GM' (`LiftCount.lift_merges_pt`: each class has exactly d_w gates),
   `lAvoid`, `CanonClass`, `CanonOneNot`, disjointness of pure merge sets, `starSep_heavy`, `disjoint_gp`.
3. **MU for UC** (the counting statement; the official target is the lifted forms MUL / LiftSDR, with
   MU over UC as the version the point induction counts). NOT proved. Data: MU over UC holds on all 6
   barrier circuits (slack 0 on Pasch s = 14), 66 of 66 in the "fourth run", and on every one of the 71
   corpus circuits plus FANO-FORMULA and JUNK in `mu_light.py`; MUL >= MU on 62,463 corpus plus 2,224
   ladder circuits (min 0, so tight cases exist). Tested, 0 failures; kernel-checked: LiftSDR on the 4
   barrier circuits that have no pure SDR (`LiftSDRWitness`).
4. **Same count over PURE classes** (PureSDR, MU, STAR-SEP, STAR-COUNT): refuted for general correct
   circuits (cxMU_dd: |U| = 5 < base 6); could hold for a minimal counterexample only through s < base.
   PureSDR itself: kernel-checked on 36 circuits (plus 12 ladder and Pasch), tested 0 failures on 44,713
   (independent re-implementation, classes agree 181/181 with Lean's) and on 75,619 (scaffold; 35,047 of
   those are not reproducible from the repository).
5. **The inductions that would prove step 3.** STAR-COUNT peels one point v at a time (x_v := 1).
   HEAVY-COUNT (v with h(Q + e_v) = 1): tested 44,093 of 44,093 + 64 of 64 barrier, 0 failures; paper
   proof for graph systems only; the case |S| >= 3 is open. LIGHT-COUNT (no heavy alive point): REFUTED
   (PAPPUS-JUNK, n = 9, 66 gates, base 18: x_v := 1 gains 5 < 6 at every v; x_v := 0 also fails; MU itself
   still holds there, 20 >= 18). The x_v := 0 deletion for UC is refuted (FANO-FORMULA, gain 2 < deg 3).
   So the point induction is dead for this UC; the count may well hold.
6. **Open and untouched**: a proof of MU / MUL / LiftSDR for minimal counterexamples, by any route.
   Candidate routes still alive: a repaired counted family, the lifted price / LP route (single-gate
   prices and 2-gate prices under condition C(b) proved on paper; k-gate open), Hall over classes.

## 2. Why it is hard (five bullets)

- **Two monotone worlds.** The single NOT splits every wire into C_0 (NOT := 0) <= real <= C_1 (NOT :=
  1). Inside one world everything is monotone and settled (`CanonClass.lean`, Lemma M). All difficulty
  sits in gates that differ between the worlds.
- **Cross-world gates.** A gate of shape (y and A) or (not y and B) merges one set in world 1 and
  another in world 0 (selector path, ADV4). Sharing is rare on natural circuits (0 shared U gates on
  1,975 of 2,159 ladder circuits) but a counterexample hunt must use it; the chains of such gates are
  unbounded (LAugment_k refuted for every fixed k).
- **Junk gates break every local rule.** Gates that become copies or real merges after a restriction
  stay counted. FANO-FORMULA (monotone formula, unused NOT, |UC| = base = 14) kills x_v := 0; PAPPUS-JUNK
  (a face-1 witness whose atom lies where h = 1 but real J_w = 0) kills x_v := 1 in the light case.
- **Both inductions failed for the same reason**: the counted family is not closed under what a restriction
  does to junk. Repairs tried and dead: least-h-influence rule, uniform and per-set averaging, "face 1
  needs h = 0 at the atoms" (breaks MU on hard4).
- **Local point and set rules stall** at the 3rd and later merge gates of sets of size >= 4 (paper951.md
  section 3); about 60 refuted routes are in DEAD_ENDS.md. Over pure menus the statement is false, so a
  proof must use the lifted menus or the minimality (s < base) explicitly.

## 3. Barrier table (DRAFT for the referee; SYNTHESIS.md section 4 item 4)

Scope: 951 is a linear bound in a restricted model, so no barrier blocks it; the question is only whether
the technique would survive the test. Reasons are from `951/SYNTHESIS_951.md` section 4 and SYNTHESIS.md
section 3; "not assessed" means no file gives a reason.

| Technique | (a) oracle | (b) low-degree extension | (c) natural proofs |
|---|---|---|---|
| Union-find merge counting (Lemma M, classes, MU / MUL) | does not relativize, need not: an oracle gate could compute all outputs, so a proof must read AND / OR semantics | evaluates gates only on Boolean points and uses monotonicity; meaningless for field-valued gates: not algebrizing, not ruled out | property "needs >= base gates" is circuit-specific and not large: not natural, not ruled out |
| Monotone faces C_0 <= real <= C_1 | does not relativize: uses the inside of the circuit (same reason as the row above) | same as the row above (Boolean points, monotone h) | not natural, not ruled out: the faces are read off one circuit's single NOT, and the bound is about one explicit family (Boolean sums of a set system), a sparse set of truth tables, so the property is not large (GeNeRALIZE draft 13:17) |
| Restriction x_v := 1 / heredity (Lemma R) | does not relativize: a restriction of one wire's value inside the circuit (SYNTHESIS.md section 3) | substitution x_v := 1 survives a field extension, but the counting after it uses AND / OR on Boolean values (merge classes, monotone h), so as in row 1: not algebrizing, not ruled out (GeNeRALIZE draft 13:17) | not natural, not ruled out: the induction runs over sub-instances of the same explicit family; no largeness (GeNeRALIZE draft 13:17) |
| Hall / SDR (disjoint choice) | does not relativize: the sets to choose from are merge classes of the circuit's own wires (GeNeRALIZE draft 13:17) | Hall is pure combinatorics on classes defined at Boolean points: same as row 1, not algebrizing, not ruled out (GeNeRALIZE draft 13:17) | not natural, not ruled out: a disjoint choice is a certificate for one circuit of one explicit family; nothing about a large fraction of functions (GeNeRALIZE draft 13:17) |
| LP duality (PurePrice, 2G-LIFT) | "same assessment" as union-find (951/SYNTHESIS_951.md) | same | same; the parity step is a design fact, not a random-function property |

Scaling (not a barrier test): k NOT gates give up to 2^k worlds; with ceil(log2(n+1)) NOT gates circuits
are general up to polynomial blow-up (Markov, Fischer; L-gen-104 checked), where the three barriers apply
in full. Every technique above gives linear bounds at best.

## 4. Quantum gravity and the NOT gate ladder

Both are MAPS, not derivations. The NOT gate ladder (L-gen-003, L-gen-004 checked; L-gen-104 checked)
carries 951 up from rung 1 toward L-gen-101 to L-gen-103; each rung adds worlds per wire. The quantum
gravity program (`lean/PEqualNP/QuantumGravity/README.md`, rows L-qg-NNN) states the classical cores of
physics arguments in Lean and enters P versus NP by an assumption route (hardness arguments resting on
classical one-way functions fail if P = NP, L-qg-103) and a model route (closed timelike curves give
P_CTC = PSPACE, a collapse world; quantum black-box access gives a separation world). It says what a
proof cannot be (the three barrier rows L-lib-061/062, 065/076, 086), and acts as a filter. No physics map
passes a barrier, no row is a statement about physics, and 951 uses none of it.
The one analogy, "two oracle worlds" versus "two values of one wire", transfers nothing in either direction.

## 5. Three next directions (all from the files)

1. Change the counted family so that face-1 witnesses whose atoms leave {h = 0} through a NOT-dependent
   AND term are not counted, without losing MU (opus-light-count.md section 4; the strict version fails on hard4).
2. Prove the lifted price form for k-gate prices: an odd-cycle / 2-colouring statement on the hypergraph of
   pairwise intersection points, starting from the open cxT2-type triples (SYNTHESIS_951.md section 3, A1).
3. The next rung: MUL with 4-world lifted classes on a 2-NOT PG(2,3) circuit with two hubs, and a
   2-selector selector path (SYNTHESIS_951.md section 5 point 5; BOARD.md 12:35; speculative).

## 6. Where the sources disagree

- LIGHT-COUNT: "open, likely the easier half" (SYNTHESIS_951.md section 3; SYNTHESIS.md section 3) versus
  "false" (opus-light-count.md, later; DEAD_ENDS row 71). This file follows the later refutation.
- DEAD_ENDS.md "NOT dead ends" line still calls PureSDR the official target; BOARD.md says the lifted
  forms superseded it at about 12:27.
- DEAD_ENDS rows 70 vs the Fable note: "x_v := 1 is good at some point on all 28,706 sub-instances" is
  true on the corpus and refuted at the root of PAPPUS-JUNK.
