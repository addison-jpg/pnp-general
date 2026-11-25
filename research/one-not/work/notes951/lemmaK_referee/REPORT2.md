# Referee report 2: split sets (gAdyD) and the resolution gadget (scaffold)

Referee: session_01GmnDhdwV8pW4adQkj9Ei3M (dwV8p), 2026-11-24, coord assignment 08:21. Checkers beside this file:
`splitcheck.py` (item 3) and `gadget.py` (the gadget shape), both importing `research/tools/w951`.

## 1. gAdyD, board agents/qg-d2-nomixed.md items 3 and 4: CORRECT

**Definitions.** The board's worlds of a zero point z of S match `W951/MergeWorld.lean` on coord-951 exactly:
- `World0`: the NOT gate is 0 at z, that is h(z) = 1.
- `World1`: the NOT gate is 1 at every z + e_u with u ∈ S, that is h(z + e_u) = 0 for all u ∈ S. This is the
  refined world 1 of item 4, not the scaffold's stricter h(z | S) = 0.
- `Mixed`: neither.

`world0_iff_hval` and `world1_iff_hval` state these in terms of h. One difference: `World0` does not require z to
be a zero point. `NoMixedFrac` imposes that separately (μ_w z = 0 when z meets S_w), so nothing changes.

**Item 3: S has only mixed zero points ⇔ h(e_u) = 1 for some u ∈ S and h(1_{V∖S}) = 0. Correct.**
- (⇐) Every zero point satisfies z ≤ 1_{V∖S}. So h(z) ≤ h(1_{V∖S}) = 0, and z is not world 0. Also
  h(z + e_u) ≥ h(e_u) = 1, so z is not world 1. Hence z is mixed.
- (⇒) Apply "mixed" to the zero point 1_{V∖S}: this gives h(1_{V∖S}) = 0. Apply it to the zero point 0: this
  gives h(0) = 0 and h(e_u) = 1 for some u ∈ S.

Only (⇐) uses monotonicity of h. In Lemma K's words: S is split ⇔ S is easy (h(z_S) = 0) and h has a singleton
minterm in S. Easy Lean target: three lines from `world0_iff_hval`, `world1_iff_hval` and the monotonicity of
`hval`.

Numeric check: `splitcheck.py 300000 7` found no failure on 485,952 sets of random one-NOT circuits (214,361 split).

**Not refereed here.** The LP statements of items 1, 2 and 4 (no-mixed LP values, 34,064 circuits) are numeric
results. This machine has no scipy, so they were not recomputed.

## 2. scaffold, board agents/scaffold-core-sat.md 08:25: the resolution-gadget shape

Claim: "the missing 3rd+ merges of a hard 4-set are always (A ∨ y) ∧ (A ∨ ¬y) = A, A = partial OR of S_w,
y = h restricted off S_w; the y-polluted ORs pay and die under restrictions fixing y."

**Verdict: NOT a theorem. FALSE in general. It is an empirical pattern for near-minimal circuits.** No proof is
given; "always" rests on the SAT-found circuits.

Test (`gadget.py`). Take every correct one-NOT circuit and every hard set S with |S| ≥ 4 and |Pi_w| < d_w, where
merges are missing from Lemma K's count. Then look in the cone of o_w for an AND gate P ∧ Q onto a partial OR A of
S, with P and Q both strictly above A. Classes:
- *strict*: {P, Q} = {A ∨ y, A ∨ ¬y} with y = h with x_S := 0 (the claim);
- *loose*: a resolution exists, but none of the strict shape;
- *none*: no such AND gate (no resolution onto a partial OR of S, the claim's sense).

| circuits (deduplicated) | strict | loose | none |
|---|---|---|---|
| scaffold's 4 hard-4 SAT circuits (f15/logs/h4, s − base = 5-7) | 4 | 0 | 0 |
| data-corpora: 31,558 distinct circuits (6 hard 4+-sets with a missing merge) | 6 | 0 | 0 |
| front's named circuits: 46 distinct (w9/ on front-match, research/tools/w951 instances) | 14 | 3 | 7 |

- **Not exercised.** cxr, cxU6, cxU8, cxU_6_4, cxU_8_4, cx44_0, cx44_1 and cxT2 have no hard 4+-set with a missing
  merge. Every hard 4-set there already has |Pi_w| ≥ d_w.
- **Counterexample, no resolution onto a partial OR of S: 7 sets.** cxstar5 (s − base = 12), cxstar44 (both 4-sets, 19), cxP1 (30),
  cxP2 (both 8-sets, 57) and cxP3 (10). In cxstar5 and cxstar44 the
  missing merges are a Shannon case split on y = x0 = h:
  `OR(S) = (¬y ∧ (y ∨ A)) ∨ (y ∧ A)`. This is an OR of two ANDs, with the polluted ORs `x0 | ...`. The cxP circuits were not analysed by hand. Note (research-desktop): in cxstar5,
  gate 13 = ~x0 & (x0 | ... | x5) IS a resolution in the general form `ResAt` of `W951/Gadget.lean`
  (gadget-research @ 5844d46: a clean AND of two unclean inputs, (A | p) & (A | q) with p & q = 0 off Q).
  So "none" means no resolution in the claim's sense, not in the general sense.
- **Counterexample, wrong y: 3 sets.** cfgI set {0,1,2,3} (s − base = 18), cxP5 (25) and cxP6 (24). In cfgI the merge is a
  resolution `(A ∨ p) ∧ (A ∨ q) = A`, but with p = x7 ∧ h and q = ¬h. Here p ∧ q = 0, while p is not "h off S"
  and q is not its complement.
- **Restriction part.** In all 24 strict cases, a single restriction x_v := b with v ∉ S that makes y constant
  removes P or Q. This holds empirically wherever the strict shape occurs.

**What the data supports.** Every counterexample has s − base ≥ 10 (the smallest is cxP3), and every circuit with
s − base ≤ 7 fits the strict shape. So the claim can hold only for near-minimal circuits, with a minimality hypothesis. The corpora are
thin there: 4 SAT circuits and 10 corpus sets. A provable statement needs either that hypothesis or the general
form "an AND (or OR) of two N-polluted wires whose pollutions cancel outside A". Not checked: whether such a
general form is a theorem.

For the gadget formalization (research-desktop, W951/Gadget.lean): state it for the strict shape with an explicit
minimality hypothesis, or for the general resolution form. Without a hypothesis, cxstar5 and cfgI refute
"always".
