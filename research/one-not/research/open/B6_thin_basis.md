# B6: the thin-basis lemma

Seat B6 (Opus), task board `boards/tasks/open-many-not.md`. Words as in `B5_flip_hall.md`: **paper** = proved
here, not in Lean; **exact SAT** = a solver answered UNSAT on a stated finite instance (computer-assisted, not
kernel-checked). Nothing here settles P versus NP.

Files: `B6_point_sat.py` (section 2). No Lean file this round (the seat-size rule: the Lean steps are written
as OPEN lines on the task board instead).

## 0. Answer

1. **A smaller relaxation that already decides the small cases.** Looking only at the one point `0` (a zero
   point of every set) turns the thin-basis lemma into a statement about finite sets: the *point lemma*
   (section 2). It implies the thin-basis lemma for the same family, so UNSAT for it is UNSAT for the
   thin-basis problem. It has `n` bits per line instead of `2^n`.
2. **Exact SAT, point lemma, `base − 1` lines:** UNSAT for Pasch (2.2 s), two 5-sets sharing a point
   (`two5`, 26.9 s), two disjoint 5-sets (`dis5`, 16.4 s). Controls with `base` lines: SAT on Pasch, Fano,
   two5, grid3. Fano: see section 3 for the run state.
   So **the thin-basis lemma, hence S3(b) in Hall form for every circuit with any number of NOT gates,
   holds for two 5-sets** (shared point or disjoint), one of the two first unsettled systems of B5.
3. **No counterexample.** Nothing found; every control behaves.
4. **Correction to the board line "B4 settles the acyclic case".** B4 bounds AND/OR *gates* (`n − comp`); the
   thin-basis lemma bounds *lines over free thin functions* (flip classes). B4's partition argument uses that
   every wire depends on one colour class; a thin function may depend on every input, so the argument does
   not carry over. The acyclic case of the thin-basis lemma is open beyond what SAT covers (two 5-sets above;
   B5's section 3 for two sets of size ≤ 3).

## 1. The statement

`W` a family of sets, pairwise intersections ≤ 1, `base(W) = Σ (|S_w| − 1)`. `f` is `W`-thin if for every
`S ∈ W` and every zero point `Z` of `S`, at most one `u ∈ S` has `f(Z + e_u) ≠ f(Z)`.

**Thin-basis lemma (B5 s5).** No straight-line program of `base(W) − 1` lines `F_i = L_i op_i R_i`
(`op ∈ {AND, OR}`, each of `L_i, R_i` a `W`-thin function or `±F_j`, `j < i`) has every `OR(S_w)` among the `±F_i`.

## 2. The point lemma (paper) and its SAT

For a function `f` let `sens(f) = {u : f(e_u) ≠ f(0)}` (at the all-zero point, a zero point of every set).

**Observation (paper).** For `F = L op R` with `op ∈ {AND, OR}` and any signs, `sens(F)` is one of
`sens(L) ∪ sens(R)`, `sens(L) ∩ sens(R)`, `sens(L) ∖ sens(R)`, `sens(R) ∖ sens(L)`.
*Proof.* Take OR (AND is dual). `L(0)=R(0)=0`: `F(e_u)=1` iff one of them flips: union. `L(0)=1, R(0)=0`:
`F(0)=1`, `F(e_u)=0` iff `L` flips and `R` does not: `sens(L) ∖ sens(R)`. `L(0)=R(0)=1`: `F` flips iff both flip:
intersection. Negating an input does not change its `sens`. ∎

A `W`-thin `f` has `|sens(f) ∩ S| ≤ 1` for every `S ∈ W` (a *partial transversal*); `sens(OR(S_w)) = S_w`.

**Point lemma (for a family `W`).** No program of `base(W) − 1` lines `X_i = A_i ∘_i B_i`,
`∘ ∈ {∪, ∩, ∖, reversed ∖}`, each of `A_i, B_i` a partial transversal of `W` or an earlier `X_j`, has every
`S_w` among the `X_i`.

**Point lemma for `W` ⟹ thin-basis lemma for `W` (paper).** Apply `sens` to every line of a thin program:
by the observation it becomes a point program with the same number of lines, and the outputs land on the
`S_w`. (Inputs outside every set: intersect every line with `⋃ S_w`; the four operations commute with that.) ∎

`B6_point_sat.py` encodes the point lemma (lines as `n` bit vectors, op one-hot over the four operations).

| system | n | sets | base | lines | result |
|---|---:|---:|---:|---:|---|
| pasch | 6 | 4 | 8 | 7 | UNSAT 2.2 s (B5 needed 213 s for the full family) |
| two5 (01234, 05678) | 9 | 2 | 8 | 7 | **UNSAT 26.9 s** |
| dis5 (01234, 56789) | 10 | 2 | 8 | 7 | **UNSAT 16.4 s** |
| fano | 7 | 7 | 14 | 13 | see section 3 |
| controls (`--control`, base lines): pasch, fano, two5, grid3 | | | | | all SAT (≤ 0.5 s) |

Only the full family is tested for two5/dis5; a subfamily of two sets is a single set (S3(a)), so that is
every subfamily. With B5's reduction (s4) this gives S3(b), Hall form, for every circuit on two 5-sets.

## 3. Fano and the cycles

The Fano point program (13 lines, 7 bits each) was still running after more than 10 minutes when this
note was written; its result goes on the task board when it ends. The point lemma is strictly weaker than
the thin-basis lemma (it sees one point), so a SAT answer on Fano would only mean the next relaxation (a few
points, e.g. `0` and the points `e_u`) is needed, not a counterexample.

**Attack on cycles (paper, no break).** The sharing that the per-point count (S3(a) at each zero point)
cannot exclude is real: `G = (x_a ∧ x_e) ∨ (x_b ∧ x_f)` (`a, b ∈ S`, `e, f ∈ T`) has two thin inputs, merges
for `S` at the zero point with `T ∖ S` all ones, and merges for `T` at the zero point with `S ∖ T` all ones.
So no proof can count merges at one chosen zero point per set; at the common point `0` such a `G` is a
`∪` of two transversals `{a,e} ∪ {b,f}`, and the point lemma has to show it cannot be split back into `S`
and `T` cheaply. That is the combinatorial core.

## 4. Remaining sub-lemmas (each an OPEN line on the task board)

* (L1) Lean: the observation of section 2 and the implication point lemma ⟹ thin-basis lemma.
* (L2) Paper/Lean: the point lemma for two sets of any sizes (`|S ∩ T| ≤ 1`). Exact SAT covers sizes ≤ 5.
* (L3) SAT: the point lemma on Fano, grid3 (rows and columns of 3×3), AG(2,3), PG(2,3).
* (L4) Scale note: the point lemma for all projective planes would give a superlinear lower bound for an
  explicit Boolean sum against all circuits with free NOT gates (B5 Remark 2). A proof for all `W` is not
  expected; for large designs a SAT hit in the point model is the place to look for a break.

## 5. Reproduce

```
python3 -I research/one-not/research/open/B6_point_sat.py two5            # UNSAT
python3 -I research/one-not/research/open/B6_point_sat.py two5 --control  # SAT
python3 -I research/one-not/research/open/B6_point_sat.py fano            # long
```
