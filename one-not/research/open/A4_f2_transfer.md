# A4: F2-transfer under one NOT gate: where the NOT gate enters

Seat A4, board `boards/tasks/open-one-not.md`, 2026-11-25. Result: a proved reduction and the exact
smaller obstacle. No proof of `no_minCE`.

Words: **checked** = Lean accepted it (`one-not/lean/PEqualNP/W951/Open/F2Transfer.lean`, build
`cd one-not/lean && lake build PEqualNP.W951.Open.F2Transfer`, no `sorry`, no `native_decide`);
**paper** = argument written here; **tested** = computed.

## 0. Verdict

1. **The F2 count holds at every mixed state with no DD set (paper; every step except the union-find
   bookkeeping is checked).** Let `h` be the wire the NOT gate reads. It is monotone. At a state `(Q, D)` let
   `P_u = 1_Q + e_u` (unit atoms) and `Z_w = Zof(S_w ∪ D)` (the top zero point of `w`). Call an alive set
   `w` **DD at (Q, D)** (`DDAt`) when `h(Z_w) = 1` and `h(P_t) = 0` for some `t ∈ S_w \ D`. If no alive set
   is DD, then `|F2Mix(Q, D)| ≥ baseDQ(S, D, Q)`. **No minimality is used.**
2. So **the NOT gate enters only through DD sets.** For a correct one-NOT circuit,
   `base' − |F2'| ≤ Σ_{w DD at (Q,D)} (|S_w \ D| − 1)` at every restriction. The deficit is 0 when the NOT gate
   is killed (`h` constant on the subcube: a dead NOT gate makes no set DD), and 0 when the NOT gate is alive
   but has no DD sign pattern.
3. **F2-transfer as stated contains the whole theorem.** At `(Q, D) = (∅, ∅)`, `|F2| ≥ base` together with
   `|F2| ≤ gates < base` is `no_minCE` (`no_minCE_of_MUF2`). A MinCE always has a DD set at the root
   (`MinCE.DD`; its output-DD implies `DDAt` at `(∅, ∅)`, paper: `C1(out)(Z_w) = 1 ≠ real` forces
   `h(Z_w) = 1`, and `C0(out)(e_u) = 0 ≠ real` forces `h(e_u) = 0`). So item 1 cannot close the root. The
   missing piece is the DD case.
4. **The exact smaller obstacle (DD-absorption).** At every mixed state, the F2 gates outside the unit
   merges of the non-DD sets must number at least `Σ_{w DD} (|S_w \ D| − 1)`. It holds at all 60,317 DD states
   of the 98 stored one-NOT circuits, and 8,942 of them are tight (**tested**, `A4_unit_merges.py --all`).
   The checked lemmas pin down what DD sets can do: their unit merges may overlap **only each other**
   (`overlap_needs_DD`), and only DD unit merges can fail to be F2 gates (2,428 such merges in the data).
   Minimality gives `gates' ≥ base'` only, and nothing in it mentions `h`. No arrow from minimality to
   DD-absorption was found.

## 1. Checked lemmas (`F2Transfer.lean`, namespace `…L_meta_951_aux.F2Transfer`)

| name | statement |
|---|---|
| `sign_of_drop` | one NOT gate, `x ≤ z`, a wire `1` at `x` and `0` at `z` ⇒ `h x = 0` and `h z = 1` |
| `unit_overlap`, `mixed_overlap` | a wire `0` at `Z_b` and `1` at two unit atoms of `S_a \ D` (`\|S_a ∩ S_b\| ≤ 1`) ⇒ some `t ∈ S_a \ (S_b ∪ D)` has `h(P_t) = 0`, `h(Z_b) = 1` |
| `overlap_needs_DD` | a wire that is a unit merge candidate for two sets `a ≠ b` ⇒ both are `DDAt` |
| `F2WitMix_of_unit_noDD` | a unit merge candidate of a non-DD set is an `F2WitMix` witness (at `Z = 1_Q` if `h(Z_w) = 0`, at `Z = Z_w` otherwise) |
| `goodT_of_noDD` | the unit test system `(Z_w, P, S_w \ D)` is `GoodT` for the real gates when `w` is not DD (the NOT gate adds no free merge) |
| `unit_count_of_noDD` | hence `\|S_w \ D\| − 1 ≤ \|DT(Z_w, P, S_w \ D)\|` |
| `unit_le_top`, `unit_testSystem`, `canonPt_le_top` | the points sit as claimed |

## 2. Paper proof of item 1

Fix `(Q, D)` with no DD set. For an alive `w` with `k_w = |S_w \ D| ≥ 2`, run the union-find of `merge_runT`
on the test system `(Z_w, P, S_w \ D)` (`unit_testSystem` gives `hT`, `goodT_of_noDD` gives `GoodT`). The
output of `w` is `0` at `Z_w` and `1` at every `P_u`, so the run makes at least `k_w − 1` merges. Each merge is
an OR gate: an AND gate `0` at `Z_w` has an input `0` at `Z_w` that is `1` at the same atoms, which are already
joined; the NOT gate merges nothing by `GoodT`. Each merging OR gate is `0` at `Z_w` and `1` at two atoms of
distinct points, so it is in `F2Mix(Q, D)` (`F2WitMix_of_unit_noDD`). The merge sets of two distinct
non-DD sets are disjoint (`overlap_needs_DD`). Summing gives `|F2Mix| ≥ Σ (k_w − 1) = baseDQ`. ∎

The unit form is the old monotone count (`count_world`: zero point `Zof S`, unit vectors), placed at
`(Q, D)`. The line form (`mergeSet`, atoms `Z + e_u`) has no NOT contribution for any set
(`mergeSet_card_ge`), but its merge sets of two different sets can overlap even in monotone circuits
(e.g. `g = (u ∧ t) ∨ (u' ∧ t')`, `u, u' ∈ S_a`, `t, t' ∈ S_b`). In the unit form, overlap and the NOT
gate's free merges both come from the same sign pattern of `h`. That pattern is DD.

Formalisation left open: the step "merges of `merge_runT` are OR gates and lie in `F2Mix`" is the unit-form
twin of `mergeSet_or` / `mergeSet_subset_F2`. It is bookkeeping and was not done here. `DT` (counted wires)
is not yet restricted to OR gates.

## 3. Attack first (stored instances)

- `A4_dd_test.py` (3,166 one-NOT circuits from the stored data and `f2lib` corpus, n ≤ 9, 2,539,674 mixed
  states): **no state has negative mixed slack**, so neither the no-DD claim nor the transfer can be broken on
  stored data. 8.3% of states have a DD set (only 1.0% have an output-DD set). Of the 265,657 tight or
  negative states with positive base, 28,992 have a DD set.
- `A4_unit_merges.py` checks the proof itself, a sharper test than the slack sign, at every state of the 98
  stored one-NOT circuits (533,790 states, 242,799 non-DD set runs). It finds 0 merges that are not OR,
  0 merges that are not F2, 0 overlaps, and 0 cases with fewer than `k_w − 1` merges. With `--all` (DD sets
  included) it finds 53,826 NOT-gate merges, 2,428 DD merges outside F2, 3,534 overlaps, all between two DD
  sets (none DD/non-DD, as `overlap_needs_DD` says), and 0 DD-absorption failures. The same check on the
  stored data plus the `f2lib` corpus (`A4_unit_merges.py --all`: 3,183 circuits, 2,856,789 states,
  1,454,402 non-DD set runs) also finds 0 merges that are not OR, 0 merges that are not F2 for non-DD sets,
  and 0 overlaps that are not DD/DD (5,174 DD/DD). It finds 0 DD-absorption failures at 242,296 DD states,
  29,459 of them tight.

## 4. What to try next

- DD-absorption at one DD set: a DD set `w` has a light point `t ∈ S_w` (`h(P_t) = 0`) and `h(Z_w) = 1`. The
  1-step `x_t := 1` kills `w` and every set through `t`. The 0-step `x_t := 0` keeps `w` with one point fewer.
  Track how `DDAt` changes under each step. A descent that never creates DD sets would close the count by
  item 1.
- The output-DD of `bound_of_noDD` is rarer than `DDAt` (1.0% against 8.3% of states). An F2 version of
  item 1 under "no output-DD" holds on all data, but the unit argument above does not prove it.
