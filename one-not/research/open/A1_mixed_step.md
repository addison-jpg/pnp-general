# A1: the mixed step at states of negative slack — the exact obstacle

Seat A1, board `boards/tasks/open-one-not.md`, 2026-11-25. Result type (b): the exact obstacle, with one
checked equivalence and one tested counterexample in the relaxed (4-NOT) setting. No proof of `no_minCE`.

Words: **checked** = Lean accepted it; **tested** = computed; **paper** = argument written here.

## 0. Verdict

1. **The mixed step at negative states is not a local lemma.** For one gate list, "every mixed state of
   negative slack has a non-increasing 0-step or 1-step" is *equivalent* to "the mixed slack is ≥ 0 at every
   mixed state" (**checked**, `MixedSlack.stepNeg_iff_nonneg`). One direction is the max principle, the other
   is vacuity. So `MixedStepNeg` (A2's Prop) is exactly the F2 count at every restriction `x_Q = 1, x_D = 0`
   of a minimal counterexample (**checked**, `MixedSlack.mixedStepNeg_iff`). Restricting the step to negative
   states throws away all local content: no circuit can satisfy the hypothesis "slack < 0" and still be a
   witness for or against a *step*.
2. **The abstract form says even less.** The hypothesis of `Continuous.no_minCE_of_mixed_descent` with only
   `f ∅ ∅ = slack ∅` pinned is equivalent to `0 ≤ slack gates S ∅` (**checked**,
   `MixedSlack.abstract_descent_iff`; take `f` constant). Only a pinned `f = mslack` gives anything.
3. **Attack (before proof): with 4 NOT gates the step fails at negative states, and only there.**
   On `Cex.generalWitnessCountBelowBase` (`general_count_below_base_min.json`, n = 7, 10 gates, 4 NOT gates,
   sets {0,1,2,3}, {0,4,5,6}), with the OR-only F2 definition of the mixed slack: slack(∅,∅) = 4 − 6 = −2,
   248 of the 529 states with positive base are negative, and the mixed step fails at 146 of them. It fails at
   **0** states of nonnegative slack (**tested**, `one-not/research/open/A1_negstates.py`; same pattern for the
   t4/t5/t6 files: 146/248, 103/121, 103/121 negative states without a step, 0 nonnegative ones; with
   the any-gate witness: 40/69 and 20/23). The smallest failing state is D = {4}, Q = {1}:
   one alive set {0,5,6}, base 2, F2Mix = ∅, so slack −2, and every paying step gives −1. The restricted
   circuit there is a De Morgan block `¬(¬x0 ∧ ¬x5 ∧ ¬x6)`, which uses 4 NOT gates.
4. **Consequence for any proof.** `F2`, `F2Mix`, `baseDQ` and `mslack` do not mention the NOT gate. The step
   at negative states is false for correct circuits with 4 NOT gates. So a proof of it **must use
   `AtMostOneNot`** (or t ≤ 3), and by item 1 it must use it to prove the full count at every restriction. No
   NOT-blind step argument can work. That excludes every argument tested on the 72M states as a proof
   strategy, since all of them are NOT-blind.

## 1. Definitions used (Lean names)

- `F2WitMix gates R Q D i`, `F2Mix gates S Q D`, `mslack gates S Q D = |F2Mix| − baseDQ S D Q`, `MixedStepNeg`,
  `no_minCE_of_MixedStepNeg`: `one-not/lean/PEqualNP/W951/Open/MixedSlack.lean` (seat A2).
- `StepNeg gates S`, `MixedCount gates S`: `one-not/lean/PEqualNP/W951/Open/MixedStepNegIff.lean` (this seat).
- `Continuous.nonneg_of_descent_at_neg` (max principle), `slack`, `Phi`, `no_minCE_of_Phi_zero_nonneg`.

## 2. The proof route, arrow by arrow, and where it stops

| # | step | status |
|---|---|---|
| A | `MinCE` ⟹ `MixedCount gates S` (F2 count at every mixed state) | **missing**: this is the open problem |
| B | `MixedCount` ⟺ `StepNeg` | **checked** `stepNeg_iff_nonneg` |
| C | `StepNeg` for every MinCE ⟹ `no_minCE` | **checked** `no_minCE_of_MixedStepNeg` (A2) |

Arrow A, attempted.

*A.1 (paper).* A state (Q, D) is the empty cube of the restricted circuit `C|x_Q=1, x_D=0` for the system
{S_w \ D : S_w ∩ Q = ∅, |S_w \ D| ≥ 2}. The restricted circuit is correct, has at most one effective NOT gate,
and still has pairwise intersections ≤ 1. So `MixedCount` for C is the F2 count (`MUF2`) for each restriction.

*A.2 (paper). What minimality gives at a restriction.* If D ≠ ∅ or Q ≠ ∅ and the fixed point is read, constant
propagation gives a strictly shorter correct instance, so `MinCE.bound_lt` gives **gates' ≥ base'**. The
step needs **|F2'| ≥ base'**. Since |F2'| ≤ #OR' ≤ gates', the inequality inherited from minimality points
the wrong way. **The precise missing lemma** (call it *F2-transfer*): for a correct circuit with at most one
NOT gate, if every strictly shorter instance satisfies the gate bound, then |F2(∅)| ≥ base. Equivalently,
the minimality hypothesis would have to be strengthened from the gate count to the F2 count. That stronger
induction (`MUF2` for all shorter instances ⟹ `MUF2`) is itself unproved, and by item 3 its step must use the
NOT bound.

*A.3 (paper). Where NOT-sensitivity can enter.* Let p be the NOT gate and a its input (a monotone wire).
At a state where `a` is constant on the subcube, the restricted circuit is monotone up to constants. If the
F2 count were known for monotone circuits (rung 0 in F2 form; I found no general Lean theorem for it, only
kernel checks on fixed circuits), then every negative state would have `a` non-constant. That is
a necessary condition, not a step: by item 1 a negative state needs a *negative* successor, and every
state where `a` is constant would then be nonnegative. So the descent would have to stay inside the region
where the NOT gate is live, and terminate. It cannot terminate, because the full states have base 0. A
proof by descent is therefore a proof by contradiction that no negative state exists. That is the count, again.

## 3. Attack on the positive-state form (`MixedStep`, every state with positive base)

This is the only form with local content (72,106,627/72,106,627 tested, fable-continuous §4). Not broken
here. Two new observations:
- On the 4-NOT counterexamples, `MixedStep` holds at every state of nonnegative slack (0 failures among
  281 / 408 such states). So "MixedStep at nonnegative states" is not where the NOT bound enters either. On
  these circuits it holds with 4 NOT gates.
- So the split is clean: the step at nonnegative states looks NOT-blind (no failure at any t), and the step
  at negative states is the count (item 1) and fails at t = 4 (item 3). A proof of `no_minCE` along this
  route needs a NOT-sensitive argument showing that **no negative state exists**. The descent framework
  contributes only the max principle.

## 4. What would be worth trying instead (not done)

- The F2 count at t = 0 (monotone circuits) as a general Lean theorem. It is the base of any induction in A.3
  and is not in the repository as a general statement.
- A NOT-sensitive local quantity: e.g. slack plus a term for the liveness of the NOT input on the subcube,
  which must be ≥ 0 at full states and descend everywhere. Item 3 says any such potential must charge the
  De Morgan block; with one NOT gate a block `¬(∧ ¬x_i)` over ≥ 2 points is impossible (needs ≥ 2 NOTs below).
  That is the one place where t ≤ 1 visibly bites.

## 5. Files

- `one-not/lean/PEqualNP/W951/Open/MixedStepNegIff.lean`: `stepNeg_iff_nonneg`, `mixedStepNeg_iff`,
  `abstract_descent_iff`. Build: `cd one-not/lean && lake build PEqualNP.W951.Open.MixedStepNegIff` (6.5 s; no
  `sorry`, no `native_decide`).
- `one-not/research/open/A1_negstates.py`: `python3 -I one-not/research/open/A1_negstates.py
  one-not/data/witnesses/nonlocal/general_count_below_base_min.json` (from the repository root).
