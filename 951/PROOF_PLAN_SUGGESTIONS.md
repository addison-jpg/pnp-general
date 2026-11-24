# Suggestions for the open step of `no_minCE` (why a collision-free choice exists)

From the board integrator (session_01GmnDhfo8QCanitMDqFa2x1), 2026-11-24, at the owner's request:
"begin suggesting the proof plan/open step to agents, so that we do not hit dead ends".
These are SUGGESTIONS, not results. Each has a kill test that costs CPU only; run the test before
any proof effort. Refuted routes are in [`DEAD_ENDS.md`](DEAD_ENDS.md): check there first.

Notation: `h` is the input of the NOT gate (monotone), `C_0` / `C_1` the circuit with NOT := 0 / 1
(both monotone, `C_0(g) ≤ C_1(g)` on every wire), `U = {h = 1}`, `D = {h = 0}`, `top_w` the point
with every variable outside `S_w` set to 1, `o_w` the sum of `S_w`, `d_w = |S_w| - 1`.

## 0. Results of the first kill tests (integrator, 2026-11-24)

Run on the 62 correct one-NOT circuits with `n ≤ 10` and at least two sets that are in this
repository (scripts and commands: `951/tools/kill_tests/`). Scaffold has the full corpus and should
rerun them there.

| Item | Result |
|---|---|
| Lemmas W0, W1, X (section 2) | 0 violations on 62 circuits (sizes, both disjointness claims, NOT-dependence of cross-world gates). Still need the referee. |
| Canonical start (section 3) | **DEAD.** Its options admit no SDR on 13 of 62 circuits. |
| Interval classes at extreme points only | **DEAD**, also in the matching form: fail on cxT2 and cxe3 even when split sets get every plain zero point. |
| Plain zero points (MergeSDR) | holds on 62 of 62, as scaffold found on the full corpus. |
| Mixed zero points | **NECESSARY for sets through a heavy point, also when `h(top_w) = 1`.** cxe3: all 8 solutions use a mixed point for at least two of the three sets through the heavy point 0. cxT2: 2 of 108 solutions are world-pure. |
| One-set induction in a fixed order of the sets | **DEAD.** No tested order makes every partial disjoint choice extendable: best is "latest output first", 53 of 62; every failure is a fixh16 circuit. |

**What this changes.** Sections 3 and P1 below are withdrawn as stated. The sets that carry the
difficulty are the sets through a heavy point (`h ≥ x_u`), at mixed zero points; for the other
sets W0, W1 and X give provable disjointness. The existence argument has to be about the star of
a heavy point, which is what front's Case II (`HeavySplitFloat`) already isolates. P2 and P3 stand
untested.

## 1. Rules that keep us out of dead ends

1. **Test before proving.** Every candidate lemma is run on the corpus first, always including
   CfgI, ADV3, ADV4, cxT4, cxU_8_4, cxr, HARD4 and the 24 fixh16 circuits. One failure kills the
   lemma as stated; record it in `DEAD_ENDS.md` with the witness.
2. **Prefer statements about all correct circuits.** No minimal counterexample exists in any
   corpus, so a lemma that needs `s < base` cannot be tested. If minimality is needed, use only
   the `MinCE.*` facts already in Lean, and say which one carries the step.
3. **Reduction first, in Lean, as hypotheses** (the `Augment.lean` pattern): check that the lemma
   closes `no_minCE` before anyone tries to prove it.
4. **Weaken `LAugment` before attacking it.** As stated it asks for an improving move from EVERY
   colliding choice of avoiding options. The descent needs it only along the states actually
   visited. A fixed canonical start (section 3) plus "an improving move exists from every state
   reachable from that start" is a smaller statement.
5. **One referee pass before anything is built on a paper lemma.**

## 2. Three short lemmas on canonical classes (proofs below; referee them)

They use general test systems (zero point `Z`, one atom point `p_u ≤ Z + e_u` per `u ∈ S_w`),
which `Frame` / `GapG` / `MatchG` already accept. `LiftCount` S2.2 (`liftCl_disjoint`) may
already contain W0; if so, only W1 and X are new.

**W0 (world 0).** Let `m` be a minterm of `h` with `m ∩ S_w = ∅`. Put
`K_0(w; m) = {OR gates g : C_0(g)(top_w) = 0 and C_0(g)(m + e_u) = 1 for at least two u ∈ S_w}`.
Then `|K_0(w; m)| ≥ d_w`, and `K_0(w; m) ∩ K_0(w'; m') = ∅` unless `m ∩ S_w' ≠ ∅` and
`m' ∩ S_w ≠ ∅`.
*Proof.* Size: `top_w` and all `m + e_u` lie in `U`, where `C_0` is the real circuit; run Lemma M
in the monotone circuit `C_0` with zero point `top_w` and atoms `m + e_u`. Disjointness: `g` in
both gives `C_0(g) ≤ o_w'` (it vanishes at `top_w'` and is monotone) and `C_0(g)(m + e_u) = 1` for
two `u ∈ S_w`. If `m ∩ S_w' = ∅` both `u` lie in `S_w'`, against `|S_w ∩ S_w'| ≤ 1`.

**W1 (world 1).** Let `h(top_w) = 0` and `h(e_u) = 0` for every `u ∈ S_w` (no heavy point). Put
`K_1(w) = {OR gates g : C_1(g)(top_w) = 0 and C_1(g)(e_u) = 1 for at least two u ∈ S_w}`.
Then `|K_1(w)| ≥ d_w`, and `K_1(w) ∩ K_1(w') = ∅` for every other such set `w'`.
*Proof.* Size: Lemma M in `C_1` with zero point `top_w` and atoms `e_u`, all in `D`.
Disjointness: `C_1(g) ≥ x_u1 ∨ x_u2` and `C_1(g)(top_w') = 0` put `u1, u2` in `S_w'`.

**X (cross-world).** If `g ∈ K_1(w) ∩ K_0(w'; m')` then `g` depends on the NOT gate, and
`x_u1 ∨ x_u2 ≤ C_1(g) ≤ o_w` while `C_0(g) ≤ o_w ∧ o_w'`.
*Proof.* If `C_0(g) = C_1(g)` then `x_u1 ≤ C_0(g) ≤ o_w'` for two points of `S_w`.

**What is left after W0, W1, X.** (a) world-0 pairs whose minterms cross (`m` meets `S_w'` and
`m'` meets `S_w`); (b) cross-world pairs at NOT-dependent gates of the shape in X; (c) sets with
`h(top_w) = 0` and a heavy point (the split sets), which need mixed zero points.

## 3. A canonical start

Each set with `h(top_w) = 1` starts in world 0 with a minterm avoiding it; each set with
`h(top_w) = 0` and no heavy point starts with `K_1(w)`; split sets start at a mixed zero point.
The options are then indexed by the prime implicants of `h` (world 0) and the choice structure no
longer mentions the circuit. Classes shrink when the zero point is raised and when atom points
are lowered, so `top_w` and minterm atoms are the extreme, least-colliding options.
**Kill test (scaffold):** on the corpus, count collisions of this start by type (a), (b), (c), and
check that an SDR is reachable from it by re-picks of minterms only. If type (a) never occurs once
minterms are chosen by a fixed rule (for example the first minterm, in a fixed order, avoiding the
set), the whole difficulty is (b) and (c).

## 4. Shapes for the existence proof, most promising first

**P1. Monotone re-picks (no counting of collisions).** Order the options of each set (for example
minterms in a fixed order, world 0 before world 1). Conjecture: in every colliding state reached
from the canonical start, some colliding set has a later option that removes its collisions with
the sets already settled. Then the process never goes back and ends, with no potential on the
number of colliding pairs. **Kill test:** replay scaffold's 100,174 collision states; in each,
is there an improving single-set move that is forward in the order? The 58 two-set cases
(fixh16) are the first place to look.

**P2. Acyclic forcing by gate position.** Label each forced re-pick with the shared gate that
forced it. Conjecture: along a forcing chain the labels are strictly monotone in circuit order
(or all lie on one side of the NOT gate). Monotone labels exclude cycles, so an augmenting chain
exists and has length at most the number of NOT-dependent gates. **Kill test:** the labels along
the 58 two-set chains, and the implication graph of the 2-SAT model (already built: 0
contradictory components on 47,674).

**P3. Exact Hall as the fallback target.** Hypergraph Hall conditions (Haxell, Aharoni-Haxell)
are sufficient only, and research found they fail here. For FIXED picks, choosing `d_w` distinct
gates from the count set of each `w` (the `MatchG` form) is bipartite matching, where Hall's
condition is exact: a failure is a subfamily `W'` with `|⋃ count sets| < Σ_{W'} d_w`. If MergeSDR
resists, prove `MatchG` instead: the obstruction is a concrete subfamily, which is the natural
place for minimality (`MinCE.heredity`, `outDel`) to enter. **Kill test:** the smallest circuit
where every MergeSDR choice fails but a `MatchG` choice exists; if there is none in the corpus,
keep MergeSDR.

## 5. What would stop the plan

A correct one-NOT circuit with no MergeSDR and no `MatchG` choice at plain zero points. Then the
target moves to general test systems (section 2) or back to the fractional form. Scaffold's
adversarial search around CfgI and the fixh16 family is the right place to look for it.
