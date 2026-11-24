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
| Lemmas GM, W0, W1, X (section 2) | 0 violations on 62 circuits. Referee: correct (GM checked step by step). **Checked in Lean:** `951/lean/PEqualNP/W951/CanonClass.lean` (`canon_size`, `orClz_disjoint`, `orClz_cross`, `canon_disjoint`, `canon_cross`), for any monotone gate list; standard axioms only. |
| Canonical start (section 3) | **DEAD.** Its options admit no SDR on 13 of 62 circuits. |
| Interval classes at extreme points only | **DEAD**, also in the matching form: fail on cxT2 and cxe3 even when split sets get every plain zero point. |
| Plain zero points (MergeSDR) | holds on 62 of 62, as scaffold found on the full corpus. |
| Mixed zero points | Needed among PLAIN zero points (cxe3: all 8 plain solutions use one for at least two of the three sets through the heavy point). **Not needed with interval classes: see the second run below.** |
| One-set induction in a fixed order of the sets | **DEAD.** No tested order makes every partial disjoint choice extendable: best is "latest output first", 53 of 62; every failure is a fixh16 circuit. |

### Second run (after the referee strengthened W1): pure interval classes suffice on all 62

The referee showed W1's size bound needs no "no heavy point" hypothesis (`C_1 ≥ real` wirewise, so
`C_1(o_w)(e_u) = 1` always). So world-1 classes exist for EVERY set, and world-0 atoms can be
chosen per atom. `kill_tests/ext.py` tests exactly these two kinds of class, with no plain and no
mixed zero point anywhere:

* **I1 (world 1, every set):** tables of `C_1`, zero point any point of `D` avoiding `S_w` that is
  maximal with that property (`top_w` when `h(top_w) = 0`), atoms `e_u`.
* **I0 (world 0, sets with `h(top_w) = 1`):** tables of `C_0`, zero point `top_w`, atom of `u` =
  `m_u ∪ {u}` for a minterm `m_u` of `h` with `m_u ∩ S_w ⊆ {u}`, chosen separately for each `u`
  (a heavy point uses `m_u = {u}`).

| Family of options | Circuits with an SDR (of 62) |
|---|---|
| I0 and I1 only | **62** (every class has exactly `d_w` merges) |
| I1 only (world 1 everywhere) | 47 |
| I0 for sets with `h(top_w) = 1`, I1 for the others | 55 |
| canonical start of section 3, plus the W1 class for split sets | 49 (the same 13 failures) |

So mixed zero points are NOT needed: the earlier "necessary" was an artefact of offering only one
minterm for all atoms and no world-1 class to sets with a heavy point. On the two hard circuits:
cxT2 has exactly 2 pure SDRs, cxe3 has 8, and in every one of them **exactly one set through each
heavy point is in world 0 and the other sets through it are in world 1**.

**Proposed target (replaces plain MergeSDR if scaffold confirms it on the full corpus): PureSDR.**
Every set picks a class of kind I0 or I1, pairwise disjoint. Every class lives in one of the two
MONOTONE circuits `C_0`, `C_1`, so `CanonClass.lean` applies to all of them: sizes by
`canon_size`, same-world disjointness by `orClz_disjoint` (explicit crossing condition),
cross-world collisions only at NOT-dependent wires by `orClz_cross`. What remains is a choice of
world per set (and of minterms / of the point of `D`), with the heavy-star rule above as the first
conjecture to test.

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

**GM (Lemma M for a general test system; W0 and W1 rest on it).** Let `C` be a list of AND / OR
gates and constants (no NOT gate), `o` a wire, `Z` a point and `p_u` (`u ∈ S`) points such that
(1) `o(Z) = 0` and `o(p_u) = 1` for every `u ∈ S`, and (2) every input variable `v` with `v ∉ Z`
lies in `p_u` for at most one `u`. Put `V = {wires g : g(Z) = 0}` and `B(g) = {u : g(p_u) = 1}`.
Then the union-find run over `V` in circuit order makes exactly `|S| - 1` merges, each at an OR
gate `g ∈ V` with `|B(g)| ≥ 2`.
*Proof.* Invariant: after a wire of `V` is processed its `B` lies in one block. Inputs: by (2),
`|B(x_v)| ≤ 1`. OR `g = s ∨ t ∈ V`: both inputs are in `V` and `B(g) = B(s) ∪ B(t)`; merge if the
two blocks differ. AND `g = s ∧ t ∈ V`: one input, say `s`, is in `V`, and `B(g) = B(s) ∩ B(t) ⊆
B(s)`. Constants: `0` has `B = ∅`; `1 ∉ V`. At the end `o ∈ V` and `B(o) = S` by (1). No
monotonicity and no order between `Z` and the `p_u` is used: the atoms need NOT be `Z + e_u`.

**W0 (world 0).** Let `m` be a minterm of `h` with `m ∩ S_w = ∅`. Put
`K_0(w; m) = {OR gates g : C_0(g)(top_w) = 0 and C_0(g)(m + e_u) = 1 for at least two u ∈ S_w}`.
Then `|K_0(w; m)| ≥ d_w`, and `K_0(w; m) ∩ K_0(w'; m') = ∅` unless `m ∩ S_w' ≠ ∅` and
`m' ∩ S_w ≠ ∅`.
*Proof.* Size: GM in `C_0` with `Z = top_w`, `p_u = m + e_u`. (1): `top_w` and `m + e_u` lie in
`U`, where `C_0` agrees with the real circuit, which is correct. (2): the variables outside
`top_w` are those of `S_w`, and `m` avoids `S_w`. Disjointness: every wire of `C_0` is a monotone
function, so `C_0(g)(top_w') = 0` gives `C_0(g) ≤ o_w'`; with `C_0(g)(m + e_u) = 1` for two
`u ∈ S_w` and `m ∩ S_w' = ∅`, both `u` lie in `S_w'`, against `|S_w ∩ S_w'| ≤ 1`.

**W1 (world 1).** Let `h(top_w) = 0` (the referee: no condition on heavy points is needed,
because `C_1 ≥ real` wirewise gives `C_1(o_w)(e_u) = 1` for every `u`). Put
`K_1(w) = {OR gates g : C_1(g)(top_w) = 0 and C_1(g)(e_u) = 1 for at least two u ∈ S_w}`.
Then `|K_1(w)| ≥ d_w`, and `K_1(w) ∩ K_1(w') = ∅` for every other such set `w'`.
*Proof.* Size: GM in `C_1` with `Z = top_w` and `p_u = e_u` (NOT `top_w + e_u`: the atoms are
the low points). (1): `top_w` and every `e_u` lie in `D`, where `C_1` agrees with the real
circuit. (2): the variables outside `top_w` are those of `S_w`, and `e_u` contains only `u`.
A gate such as `x_u ∧ x_v` with `v ∉ S_w` is in `V` with `B = ∅`, which the invariant allows; it
is simply not counted. Disjointness: `C_1(g)` is monotone, so `C_1(g)(e_u) = 1` gives
`C_1(g) ≥ x_u`; then `C_1(g)(top_w') = 0` puts `u1, u2` in `S_w'`.
(`kill_tests/canon.py` measures exactly this class: zero point `top_w`, atoms `e_u`, tables of
`C_1`; the run has `d_w` merges on all 28 such sets of the small corpus.)

**X (cross-world).** If `g ∈ K_1(w) ∩ K_0(w'; m')` then `g` depends on the NOT gate, and
`x_u1 ∨ x_u2 ≤ C_1(g) ≤ o_w` while `C_0(g) ≤ o_w ∧ o_w'`.
*Proof.* Every wire of `C_0` and of `C_1` is a monotone function, and `C_0(g) ≤ C_1(g)` for every
wire (induction over the gates: the NOT gate is `0 ≤ 1`, AND and OR are monotone).
`C_1(g) ≤ o_w`: if `C_1(g)(x) = 1` with `x ∩ S_w = ∅` then `x ≤ top_w` and `C_1(g)(top_w) = 1`,
against `g ∈ K_1(w)`. `C_1(g) ≥ x_u1 ∨ x_u2`: from `C_1(g)(e_ui) = 1`. `C_0(g) ≤ o_w`: from
`C_0(g) ≤ C_1(g)`. `C_0(g) ≤ o_w'`: as in W0, from `C_0(g)(top_w') = 0`. Dependence: if
`C_0(g) = C_1(g)` then `x_ui ≤ C_0(g) ≤ o_w'` for two points `u1, u2` of `S_w`, so both lie in
`S_w'`.

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
