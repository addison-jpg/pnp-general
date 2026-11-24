Serves README items L5, L6, C2 (task continuous-mapping)

# The continuous form of the count: what was built, what died, what reaches the `sorry`

(main's Fable, 2026-11-24.) Words: **checked** = Lean accepted it; **paper** = complete argument below;
**tested n/N** = computed, with counts; **premise** = a map, never a Lean statement; **missing** = nobody has it.
Formal names as in NAMES.md. Lean names `slack`, `Phi`, `Phi_zero`, `no_minCE_of_Phi_zero_nonneg` are those of
`one-not/lean/PEqualNP/W951/ContinuousAttach.lean` (main); nothing is redefined here.

## 0. Verdict

1. **No continuous route on the cubes.** Every continuous statement about `Phi` or about the multilinear
   extension `ext` of the slack that I could formulate is either equivalent to the count (no gain) or refuted on
   the twin trees, the matched twin trees or the Fano corpus (§2, §3, §5). The reason is one line: the
   gradient of `ext` at the corner p = 0 is the vector of one-point slack changes, and all of them are positive on
   the twin trees. A fractional step is not weaker than the one-point step.
2. **One object is kept: the three-state extension `ext3`** (each point is set to 1 with probability p_v, to 0
   with probability r_v, left free otherwise), i.e. the slack on mixed states (Q, R). Its corner always has a
   first-order descent direction on the data: the **mixed step** (`MixedStep`, old name: mixed induction) holds at
   72,106,627 of 72,106,627 mixed states tested, including all 3^14 states of the six twin trees and all 3^16
   states of both matched twin trees, where the one-point step and the k-point step fail (§4).
3. **Chain to the `sorry`** (§6): `MinCE S gates out` → [MISSING] mixed descent at the states of negative slack
   → [checked] `Continuous.Phi_zero_nonneg_of_mixed_descent` : `0 ≤ Phi gates S 0` → [checked]
   `no_minCE_of_Phi_zero_nonneg` : `no_minCE`. **The single missing arrow** is the mixed step at the states of
   negative slack of a minimal counterexample. It is a discrete statement. The continuous form adds the
   maximum principle (descent is needed only where the slack is negative, checked) and nothing else.
4. Honest limit: at a state of negative slack the mixed step is logically equivalent to the count for the
   restricted circuits (if the count holds it is vacuous). It does not weaken the open problem. What it changes is
   the candidate local lemma: C2 and C3_k are false without `MinCE.no_rewire`; `MixedStep` has no counterexample
   with or without it.

## 1. Definitions

Setting as in README (Theorem, D5, D8). slack(Q) = |`realWitness`(Q)| − `base`(Q) (Lean: `slack gates S Q`).

**Definition 1 (`ext`, multilinear extension).** For p ∈ [0,1]^n let μ_p put each point v in Q independently with
probability p_v. ext(p) = E_{μ_p}[slack(Q)] = Σ_Q Π_{v∈Q} p_v Π_{v∉Q} (1 − p_v) slack(Q). It is linear in each p_v,
ext(1_Q) = slack(Q), and ∂ext/∂p_v (p) = E_{μ_p}[slack(Q + v) − slack(Q) | v ∉ Q].

**Definition 2 (`Phi`, the diagonal; Lean `Phi gates S p`).** Φ(p) = ext(p, …, p) = Σ_i C(n,i) p^i (1−p)^{n−i} m_i,
where m_i is the mean of the slack over the cubes with i points (Bernstein form). Φ(0) = slack(∅) (checked:
`Phi_zero`), Φ(1) = slack of the full cube = 0.

**Definition 3 (up-Laplacian).** lap f (Q) = Σ_{v ∉ Q} (f(Q + v) − f(Q)).

**Definition 4 (mixed state, mixed slack, `ext3`).** A mixed state is a pair (Q, R) of disjoint sets of points:
x_Q = 1, x_R = 0. It is the cube Q of the circuit restricted by x_R = 0, which is a correct one-NOT circuit for
the sets S_w ∖ R (those with at least 2 points left). base(Q, R) = Σ (|S_w ∖ R| − 1) over the sets that avoid Q
and keep ≥ 2 points; `realWitness`(Q, R) = the OR gates with g(Z) = 0, g(Z + e_u) = g(Z + e_u') = 1 for a zero point
Z ⊇ Q, Z ∩ R = ∅ and u ≠ u' in S_w ∖ R; slack(Q, R) = their difference. slack(Q, ∅) = slack(Q). A **1-step** puts a
free point in Q, a **0-step** puts it in R; a step **pays** if the base drops. ext3(p, r) = E[slack(Q, R)] when each
point is independently in Q with probability p_v, in R with probability r_v (p_v + r_v ≤ 1).
Python: `continuous.slack_table(c, R)` (all Q for one R). No Lean definition of slack(Q, R) exists (**missing**,
a definition, not a lemma: it is `slack` of the restricted gate list).

**Conjecture `MixedStep`.** For every correct one-NOT circuit and every mixed state with base(Q, R) > 0 some paying
0-step or 1-step has slack no larger.

## 2. `Phi`: computed exactly, no route

**Lemma 1 (Russo–Margulis form; paper).** (1 − p) Φ′(p) = E_p[lap slack(Q)], and
Φ′(p) = n Σ_{i<n} C(n−1,i) p^i (1−p)^{n−1−i} (m_{i+1} − m_i).
*Proof.* dΦ/dp = Σ_v ∂ext/∂p_v = Σ_v E_p[(slack(Q+v) − slack(Q)) 1_{v∉Q}] / (1 − p); the second form is the
derivative of a Bernstein polynomial. ∎

**Lemma 2 (checked: `Continuous.Phi_nonneg_of_slack_nonneg`).** If slack(Q) ≥ 0 at every cube then Φ ≥ 0 on [0,1].
Conversely ext ≥ 0 on [0,1]^n iff slack ≥ 0 at every cube (a multilinear function has its minimum at a vertex;
paper). So "ext ≥ 0" is the count at every cube: **no gain**.

**Tested 23/23** (`continuous.py phi`; the 23 witness circuits with ≤ 1 NOT gate and n ≤ 16; exact rational
Bernstein coefficients; signs on the grid j/400):

| | Φ ≥ 0 on [0,1] | Φ′ ≤ 0 on [0,1] | sign changes of Φ′ | sign changes of Φ″ |
|---|---|---|---|---|
| 15 circuits (pappus_junk_gain, fano_formula, star4, …) | yes | yes | 0 | ≤ 1 (− then +) |
| 6 twin trees (n = 14): m = 6, 8.29, 7.87, 6.55, 5.11, 3.84, 2.80, …, 0 | yes | **no**, Φ′(0) = 14 · 2.29 > 0 | 1 (+ then −) | 1 (− then +) |
| MATCH-C(7), MATCH-S(7) (n = 16): m = 15, 16.75, 14.96, 12.35, …, 0 | yes | **no**, Φ′(0) = 16 · 1.75 > 0 | 1 (+ then −) | 1 (− then +) |

Φ is not monotone, not convex, not concave; m is not log-concave as a route either (it starts by rising).
**Why no shape property helps (paper).** A property P of Φ gives the Theorem only if "P and Φ(1) = 0" imply
Φ(0) ≥ 0. Unimodal (up, then down) and "one inflection" do not: Φ(p) = (1 − p)²(p − ε) has both and Φ(0) = −ε < 0.
The observed shapes are compatible with a negative corner, so they are data, not a route.
**Reweighting.** Φ(p)(1 − p)^c is nonincreasing iff (1 − p)Φ′ ≤ cΦ, i.e. E_p[lap slack − c·slack] ≤ 0. If this holds on
[0,1) for one c ≥ 0 then Φ(0) ≥ lim_{p→1} Φ(p)(1−p)^c = 0 (Grönwall form; paper). But for Φ > 0 on [0,1) such a c
always exists (near p = 1, Φ ~ a(1−p)^k and (1−p)Φ′ < 0), and for Φ(0) < 0 with Φ′(0) ≥ 0 none exists: the
averaged inequality is equivalent to the sign of Φ. **No gain.** Its pointwise form is refuted in §3.

## 3. The multilinear extension: the corner is a strict local minimum on the twin trees

**Lemma 3 (corner obstruction; paper).** Let Q be a cube with slack(Q + v) > slack(Q) for every free point v on an
alive set, and slack(Q + v) ≥ slack(Q) for the other free points. Then for every direction d ≥ 0 that moves at least
one alive point, the derivative of ext at 1_Q along d is > 0: every path that leaves the corner and makes
progress goes up first. *Proof.* ∇ext(1_Q)·d = Σ_v d_v (slack(Q+v) − slack(Q)). ∎
So a monotone path of `ext` from the corner 0 exists only if the one-point step (C2) holds at ∅ up to equality.
The straight segment to 1_D has end value slack(D): "ext(1_D) ≤ ext(0)" is C3_k, refuted for every fixed k.

**Counterexample (tested, `continuous.py grad`).** Of 176,994 cubes with positive base on the 23 witness circuits,
8 have every paying direction strictly uphill: Q = ∅ on the six twin trees (changes +1, +2, +3, +5; slack 6) and
on MATCH-C(7), MATCH-S(7) (changes +1, +2, +6; slack 15). **DEAD:** monotone path / gradient flow / fractional
step for `ext`.

**Refuted `Refuted.tightCubeRigidity`** (my own candidate). Statement: slack(Q) = 0 ⇒ slack(Q + v) = 0 for every
free v (the zero set of the slack is an up-set; equivalently lap slack ≤ c · slack pointwise for some finite c,
which by the maximum principle would give the count). It holds at 17,562 of 17,562 tight cubes of the
3,155-circuit corpus and on the 23 witnesses, and **fails on the Fano corpus: 245 of 2,456,029 tight cubes**
(80,198 circuits). Smallest: 19 gates, Fano lines, Q = ∅, v = 4: slack(∅) = 14 − 14 = 0, slack({4}) = 9 − 8 = 1
(checked with `core.slack` as well):
`{"n":7,"sets":[[0,1,2],[0,3,4],[0,5,6],[1,3,5],[1,4,6],[2,3,6],[2,4,5]],"gates":[["not",4],["or",2,0],["or",8,1],["or",3,0],["or",10,4],["or",0,5],["or",12,6],["or",3,1],["or",14,5],["and",6,7],["and",6,2],["or",16,17],["or",18,1],["or",19,4],["or",3,2],["or",21,6],["and",2,7],["or",23,4],["or",24,5]],"outs":[9,11,13,15,20,22,25]}`
(`continuous.TIGHT_UP`; `continuous.py check` re-verifies it.) Uphill steps on the Fano corpus by slack of the cube:
245 at slack 0, 2,731 at slack 1, 3,564 at slack 2. Still, at every one of the 5,132,672 Fano cubes SOME paying
1-step has slack no larger (known: coord, `fano/f2check.py`).

## 4. The kept object: mixed states and `ext3`

**Lemma 4 (maximum principle; checked: `Continuous.nonneg_of_descent_at_neg`).** On any set of states with a
rank in ℕ: if every state of NEGATIVE value has a state of smaller rank whose value is no larger, no value is
negative. Instances (checked): cubes, `slack_nonneg_of_cube_descent_at_neg`; mixed states,
`Phi_zero_nonneg_of_mixed_descent`; the averaged form `nonneg_of_upLaplacian_le` (lap f ≤ 0 at the negative cubes
and f(full cube) ≥ 0). This sharpens L7 (`ChainSum.slack_nonneg_of_descent`), which asks for the descent at every
non-terminal cube: only the negative ones are needed, and there no terminal condition is needed at all.

**Lemma 5 (`MixedStep` gives the count; paper, abstract part checked).** If `MixedStep` holds for a circuit then
slack(Q, R) ≥ 0 at all its mixed states, in particular slack(∅) ≥ 0. *Proof.* A paying step lowers the base, so
the rank base(Q, R) drops; apply Lemma 4. (In Lean the rank n − |Q ∪ R| is used.) ∎

**Lemma 6 (the corner of `ext3`; paper).** ∂ext3/∂p_v and ∂ext3/∂r_v at a vertex (Q, R) are the slack changes of
the 1-step and of the 0-step at v. So `MixedStep` says: at every vertex with positive base, `ext3` has a
coordinate direction that pays and does not go up; following such directions is a monotone path along edges
from (∅, ∅) to a state of base 0. This is the "continuous chain" that survives; it is piecewise linear along
edges, so it is the discrete statement and nothing more.

**Tested (`continuous.py mixed`; every one of the 3^n mixed states of every circuit listed).**

| data | circuits | states with base > 0 | no paying 1-step ≤ | no paying 0-step ≤ | neither (`MixedStep` fails) |
|---|---|---|---|---|---|
| 15 witness circuits with n ≤ 9 | 15 | 17,046 | 0 | 2 (fano_formula, pappus_junk_gain, both at (∅, ∅)) | 0 |
| six twin trees, n = 14 | 6 | 10,270,860 | 6 (only (∅, ∅)) | 0 | 0 |
| MATCH-C(7), MATCH-S(7), n = 16 | 2 | 55,906,338 | 2 (only (∅, ∅)) | 0 | 0 |
| corpus (`f2lib.corpus(9)` + `randgen(1, 3000)`, as on disk now) | 3,166 | 1,052,263 | 0 | 2 | 0 |
| Fano corpus, every 20th circuit | 4,010 | 4,860,120 | 0 | 2 | 0 |
| total | 7,199 | 72,106,627 | 8 | 6 | **0** |

Hill climbing against `MixedStep` (`continuous.py hunt 300 2 6` and `hunt 300 3 7`: 207,536 and 88,907 mutations,
55,296 and 21,220 accepted): no counterexample; hill climbing that finds nothing proves nothing.

**What it shows on the twin trees.** At (∅, ∅): every 1-step raises the slack (6 → 7, 8, 9, 11), but 0-steps change
it by −2 (cost 1), −1 (cost 2) or +1 (cost 1). The junk of a leaf pair is an AND with one input; setting that
input to 0 removes the junk of every leaf at once and costs one unit per set through the point. On MATCH-C(7):
0-step changes −6 (cost 2), −1, −1.
**Lemma 7 (MATCH-C(k), every k; paper).** At (∅, ∅) of MATCH-C(k) the 0-step at y lowers the slack by at least
k − 1. *Proof.* Cost: A loses one point, E = {y, a_0} drops to one point: 2. Gain: the k gates p_i = u_i ∨ y a_i are
in `realWitness`(∅) (fable-chain-sum Lemma 3 with D = ∅) and become the input u_i when y = 0; X_A = y ∨ a_0 becomes
a_0. So at least k + 1 gates leave. ∎ (k = 7: −6, as computed.) So the family that kills C3_k for every fixed k
does not touch `MixedStep` at its non-local corner.
Not known: `MixedStep` at the deeper states of MATCH-C(k) for k ≥ 8, and a circuit where both kinds of junk
(pappus: 0-step fails; twin trees: 1-step fails) sit at one state. A disjoint union of the two does not do it
(the points of each part keep their good step).

## 5. The LP for a local potential: infeasible

**Definition 5 (potential).** ψ(Q) = Σ_{OR gates g} c(k_g, kb_g, b_g) − Σ_w a(|S_w|, |S_w ∩ Q|), where k_g = number of alive
sets g witnesses at Q (capped at 3), kb_g = number it witnesses with Z = Q itself (capped at 2), b_g = g(bottom point
of the cube). Sign constraints: c = 0 for non-witness gates, c ≤ 1 for witness gates, a(s, 0) ≥ s − 1,
a(s, j) ≥ 0, a(s, s) = 0. Then ψ ≤ slack at every cube and ψ(full cube) = 0. Local inequality, two forms:
*all*: ψ(Q + v) ≤ ψ(Q) for every free v; *avg*: lap ψ(Q) ≤ 0. Either gives ψ ≥ 0 (Lemma 4), hence slack ≥ 0.
ψ = slack is in the family (c = 1, a = base); it fails both forms on the twin trees.

**LP verdict (tested, `continuous.py lp`, scipy HiGHS).**

| data | parameters | form *all* | form *avg* |
|---|---|---|---|
| twin trees alone, gate features (k, b) only | 19 | infeasible | infeasible |
| twin trees alone, features (k, kb, b) | 29 | infeasible (392 inequalities) | feasible: weight 1/3 on gates that witness one set but not at the bottom point |
| MATCH-C(7) alone | 30 | infeasible | feasible (same 1/3) |
| the 23 witnesses jointly | 47 | infeasible (2,359) | feasible (7,365) |
| 23 witnesses + corpus (3,166) + Fano sample (4,010) | 53 | **infeasible** (58,913) | **infeasible** (46,401) |

**DEAD** in this family: no potential of this local form exists on the data. The reason is visible in the
feasible cases: the LP discounts junk (witness only above the bottom point); on the Fano corpus the same
feature occurs on gates that are needed at tight cubes, where ψ ≤ slack = 0 forces full weight.
A potential with circuit-specific end conditions (only ψ(∅) ≤ slack(∅) and ψ(full) ≥ 0) is vacuous: ψ = 0 is
feasible exactly when the count holds. And the greatest decreasing minorant of the slack is
ψ*(Q) = min_{Q' ⊆ Q} slack(Q'), which is not local. So the potential form is the count or it is refuted.

## 6. The chain to the `sorry`, arrow by arrow

Target line (main, `ContinuousAttach.lean`): `MinCE S gates out → 0 ≤ Phi gates S 0`.

| # | arrow | word |
|---|---|---|
| 1 | `MinCE S gates out` ⟹ there is f : mixed states → ℤ with f ∅ ∅ = `slack gates S ∅` (f = mixed slack of Definition 4) | definition **missing** in Lean; Python `slack_table(c, R)`; f(Q, ∅) = slack(Q) by definition (paper) |
| 2 | ⟹ at every state with f Q R < 0 some state with Q ∪ R strictly larger has f no larger (`MixedStep` at the negative states) | **MISSING** (the open lemma). Tested in the stronger form "every state with positive base, every correct circuit": 72,106,627/72,106,627, but no tested circuit has a negative state, so the data is about the positive states only |
| 3 | ⟹ `0 ≤ Phi gates S 0` | **checked**: `Continuous.Phi_zero_nonneg_of_mixed_descent` (through `Phi_zero`) |
| 4 | ⟹ `¬ MinCE S gates out` | **checked**: `Continuous.no_minCE_of_mixed_descent` (through `no_minCE_of_Phi_zero_nonneg`, `no_minCE_of_MUF2`) |

The other continuous statements and why they cannot reach the line:
- Φ ≥ 0 on [0,1] ⟸ slack ≥ 0 at every cube (checked, Lemma 2): the arrow points the wrong way; Φ ≥ 0 on (0,1] says
  nothing about p = 0 beyond continuity, and Φ(0) ≥ 0 by continuity IS a route only if Φ ≥ 0 on (0, ε) is proved
  first, which is the count on average over cubes with few points: not easier (no tested circuit separates them).
- Φ′ ≤ 0 ⟹ Φ(0) ≥ Φ(1) = 0 (paper): the hypothesis is false on the twin trees (§2).
- monotone path for `ext` ⟹ ext(0) ≥ 0 (paper): no such path on the twin trees (Lemma 3).
- tight-cube rigidity / lap slack ≤ c · slack ⟹ count (checked form `nonneg_of_upLaplacian_le` for c = 0 at the
  negative cubes): refuted on the Fano corpus as a statement at slack 0; at slack < 0 it is the count.
- local potential (§5): infeasible.

**The single missing arrow: arrow 2.** As a Lean statement, for one gate list (mixed slack written `mslack`):
`MinCE S gates out → ∀ Q R, mslack gates S Q R < 0 → ∃ v ∉ Q ∪ R, mslack gates S (insert v Q) R ≤ mslack gates S Q R ∨ mslack gates S Q (insert v R) ≤ mslack gates S Q R`.
What a proof may use that the tested form does not have: f < 0 (fewer witness gates than the base, so no junk
is affordable) and the facts of L2. What it may not use: locality or `MinCE.no_rewire` are not needed on any
tested circuit.

## 7. Link to L6 (short) and the C4 side (short)

**L6.** The Cesàro mean averages an orbit over time; Φ averages the slack over cubes with weight μ_p; the Shapley
form (`sum_shapley`, qg-d2) averages over orders. All three share the telescoping identity and one more thing,
which is also only an identity: ∫_0^1 Φ′(p) dp = Φ(1) − Φ(0) = −slack(∅), with Φ′ given by Lemma 1, is the same
sum regrouped (∫_0^1 C(n−1,i) p^i (1−p)^{n−1−i} dp = 1/n gives the Shapley weights). L6 has an estimate (the orbit
is bounded, so the mean step tends to 0); the product measure has none: the mean of gain − cost says nothing
about the sign of slack(∅). **Premise** (never a Lean statement): time ↔ the parameter p; orbit ↔ the family μ_p;
fixed point ↔ p = 1. Nothing about closed timelike curves is proved or used.

**C4.** Definitions 1 to 4 and Lemma 4 use only that the family decreases along cubes, so they extend unchanged
to `witness` (D9, any gate type) and to t NOT gates. The statements do not: on
`Cex.generalWitnessCountBelowBase` (t = 4, any-gate family) Φ < 0 and increasing on [0,1) (level means −1, −0.43,
−0.14, −0.03, 0), 69 of its mixed states are negative, and the mixed step fails at 40 of 529 states with positive
base (one test, forced by Lemma 4).

## 7a. The five ideas of `sonnet-continuous-lit.md`, each attacked on the twin trees

1. *Monotone level means* (m_0 ≥ m_1 ≥ … ⟹ Φ′ ≤ 0 ⟹ 0 ≤ Φ(0)). **Refuted** on 8 of the 23 witness circuits: m_1 > m_0 on
   the six twin trees (6 → 8.29) and on MATCH-C(7), MATCH-S(7) (15 → 16.75). It held on the 15 circuits with n ≤ 9
   only because the twin trees have n = 14. From level 1 on the means do decrease on all 23 (m_1 ≥ m_2 ≥ …), which
   says nothing about m_0.
2. *Convexity of Φ.* **Refuted**: Φ″ changes sign (− then +) on 19 of 23. The tangent at p = 1 is trivial.
3. *Acyclic matching / a path of non-increasing edges from ∅.* On the cubes ∅ has no non-increasing paying edge
   on the twin trees, so ∅ must be a critical cell and then needs slack(∅) ≥ 0 by another argument: **no gain**.
   On the mixed states the path exists on all data: this is `MixedStep` (§4).
4. *Lovász extension, sandwich m with H ≤ m ≤ G.* On the diagonal the Lovász extension is (1 − t) slack(∅): a
   restatement. A sandwich for a split slack = G − H is a per-circuit certificate; like the potential with
   circuit-specific end conditions (§5) it exists exactly when the count holds: **no gain**, not run.
5. *Negative dividends* (Σ_{|T|=k} m(T) ≤ 0 for k ≥ 1; these sums are the power-basis coefficients of Φ).
   **Refuted**: holds on 2 of 23; the twin trees have +32 at k = 1, and 13 others have a positive sum at k = 2, 3 or 4.

## 8. Files and commands (repository root, `python3 -I`)

- `one-not/tools/search/continuous.py phi | grad | mixed | lp | hunt SECONDS SEED [NMAX] | check` with arguments
  `F.json`, `F.jsonl[:COUNT]`, `corpus`. The Fano corpus is not in the repository: `cd one-not/tools/fano && python3 -I fano_corpus.py OUT.jsonl` (80,198 circuits, about 2 minutes); the sample is `awk 'NR%20==1'`.
- `one-not/lean/PEqualNP/W951/Continuous.lean`: `nonneg_of_descent_at_neg`, `slack_nonneg_of_cube_descent_at_neg`,
  `Phi_zero_nonneg_of_cube_descent_at_neg`, `Phi_zero_nonneg_of_mixed_descent`, `no_minCE_of_mixed_descent`,
  `nonneg_of_upLaplacian_le`, `Phi_nonneg_of_slack_nonneg`. No `sorry`. Build:
  `lake build PEqualNP.W951.Continuous`. `#print axioms` on all of them: `propext`, `Classical.choice`, `Quot.sound` only.
- Literature (main's Sonnet D): `one-not/board/agents/sonnet-continuous-lit.md`; its five ideas are answered in §7a.
