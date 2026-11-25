# B9: the point lemma for two sets

Seat B9 (Opus), task board `boards/tasks/open-many-not.md`. Words as in `B6_thin_basis.md`: **paper** = proved
here, not in Lean; **exact SAT** = a solver answered UNSAT on a stated finite instance (computer-assisted, not
kernel-checked). Nothing here settles P versus NP.

Script: `B9_two_sets.py` (modes `lemma`, `xor`, `ruleR`, `r2`; section 5).

## 0. Answer

The full statement is **not proved**. What is settled:

1. **Paper proof when one set has at most 2 points** (section 2): for `|S| ≤ 2` and any `T` (shared point or
   disjoint), every program with `S` and `T` among its lines has at least `|S| + |T| − 2` lines.
2. **Exact SAT, `|S| + |T| − 3` lines, UNSAT** (section 4): sizes (4,6) and (3,7), shared and disjoint, are new.
   With B6 that covers every pair of sizes with `|S| + |T| ≤ 10` except (5,5), which B6 already has.
3. **Any proof must use that XOR is not an allowed operation** (section 3.1). With `△` added as a fifth
   operation the lemma is false: `|S| = |T| = 3` sharing a point in 3 lines, and two disjoint 4-sets in 5 lines.
   So no argument that only counts leaves, signatures or "which points can be told apart" can work.
4. **Exact smaller obstacle** (section 3.3): a gate-elimination rule, R2. R2 implies the lemma (paper, section 3.2).
   The simpler rule R (remove one point, one gate dies) is **false** for programs with extra lines: an explicit
   10-line program for `|S| = 3, |T| = 5` (section 3.3). R2 held on every program tested.

## 1. The statement

`S, T` finite sets, `|S ∩ T| ≤ 1`. A *leaf* is a set meeting `S` in at most one point and `T` in at most one
point (a partial transversal). A *program* is a list of lines `X_i = A ∘ B`, `∘ ∈ {∪, ∩, ∖, reversed ∖}`, each
of `A, B` a leaf or an earlier line.

**Point lemma for two sets.** If `S` and `T` are both among the lines, there are at least `|S| + |T| − 2` lines.

Conventions used below. Points outside `S ∪ T` are dropped (intersect every line with `S ∪ T`; the four
operations commute with that). All four operations send (out, out) to out, so a point in no leaf below a line is
not in that line ("0-preserving"). A set with at most one point of `S` and one of `T` is itself a leaf, so the
statement may be read with "`S`, `T` each a line or a leaf"; this changes nothing when `|S|, |T| ≥ 2`.

**Single-set bound (known, B5/B6).** If `T` is a line and `D` is the set of lines below `T` (including `T`), with
`g = |D|`, count each leaf slot of a line in `D` as its own node. Each line in `D` has 2 input slots, and each node
of `D` other than `T` feeds at least one line of `D`, so the number `λ` of leaf nodes satisfies
`2g ≥ (g − 1) + λ`, i.e. `λ ≤ g + 1`, with equality only if every line of `D` other than `T` feeds exactly one line
of `D` (a tree). Each point of `T` is in some leaf node of `D` (0-preserving), each leaf holds at most one point of
`T`, so `λ ≥ |T|` and `g ≥ |T| − 1`.

## 2. Paper: the case `|S| ≤ 2`

**Tight-tree lemma.** If `g = |T| − 1` in the single-set bound, then every line in `D` is a subset of `T`.

*Proof.* Equality everywhere: `λ = |T|`, `D` is a tree, every leaf node holds exactly one point of `T`, and these
points are distinct. In a tree the two inputs of a line have disjoint sets of leaf nodes below them. Claim: every
node `N` of `D` contains every `T`-point of the leaf nodes below it, and every line of `D` is a `∪`. Induction up
the tree. For `N = A ∘ B`, a `T`-point `t` below `A` is in `A` (induction) and not in `B` (no leaf below `B` holds
`t`; 0-preserving). So `t ∈ N` iff `∘ ∈ {∪, A ∖ B}`; symmetrically for `T`-points below `B`. Both sides have such
points. If `∘ ≠ ∪`, some `t` below `N` is not in `N`, and then not in any line above `N` (above `N`, `t` is in
neither input of each line on the way: it is in no leaf of the other side). So `t ∉ T`, a contradiction. Hence all
lines are `∪`, `T` is the union of the leaf nodes of `D`, and so every leaf node of `D`, and every line of `D`,
is a subset of `T`. ∎

**Theorem (paper).** `|S| ≤ 2`, any `T`, `|S ∩ T| ≤ 1`: at least `|S| + |T| − 2` lines.

*Proof.* `|S| ≤ 1`: the single-set bound gives `|T| − 1 ≥ |S| + |T| − 2`. `|S| = 2`: suppose `m ≤ |T| − 1`
lines. Then `g ≤ m ≤ |T| − 1 ≤ g`, so `g = m = |T| − 1` and every line is in `D`. `S` has two points of `S`, so it
is not a leaf, so it is a line, so `S ⊆ T` by the tight-tree lemma. But `|S ∩ T| ≤ 1 < 2 = |S|`. ∎

(The same pattern settles `|S| = 3` when `T` uses only `|T| − 1` lines: the one extra line is `A ∘ B` with `A, B`
leaves or subsets of `T`, so it has at most two points outside `T`, while `S` has at least two outside `T` and at
most one inside. The open part of `|S| = 3` is when `D` has `|T|` lines: one extra leaf, or one line read twice.
That case analysis is an OPEN line on the board.)

## 3. The general case: where it stops

### 3.1 XOR breaks it (exact, small)

Add `A △ B` as a fifth operation. Then `S = {0,1,2}`, `T = {0,3,4}` (shared point 0) have a 3-line program
(`|S| + |T| − 3 = 3`):

```
X0 = {0} ∪ {1,3}          = {0,1,3}
X1 = {1,4} △ X0           = {0,3,4} = T
X2 = {2,3} △ X0           = {0,1,2} = S
```

and the SAT (`B9_two_sets.py xor 4 4 d`) finds 5 lines for two disjoint 4-sets. One `△` with a leaf adds one point
and removes another; `∪, ∩, ∖` with a leaf only add, or only remove, at most one point of `S` and one of `T`.
Every argument that looks only at which leaves contain which points (leaf counts, signatures, separation of
`S`-points from `T`-points) is blind to the operation set, so it cannot prove the lemma. The proof has to use
that each operation is monotone or antitone in each input.

### 3.2 Gate elimination (paper reduction)

Call a line *redundant* if its value is a leaf, equals the value of one of its inputs, or equals an earlier line;
it can then be deleted (its readers read that leaf or line instead), and lines that no longer lie below `S` or `T`
are deleted too. Removing a point `u` from the universe keeps every leaf a leaf, commutes with the four
operations, and keeps a redundant line redundant. A point is *private* if it lies in exactly one of `S`, `T`.

**Rule R2.** Let `S, T` (`|S ∩ T| ≤ 1`, each with at least 2 points) be lines of a program of `m` lines. Then
either (a) for some private `u`, after removing `u` and deleting redundant and dead lines at most `m − 1` lines
remain, or (b) for some private `a ∈ S`, private `e ∈ T`, after removing `a` and `e` at most `m − 2` remain.

**R2 ⟹ point lemma for two sets (paper).** Induction on `|S| + |T|`. If `|S| ≤ 1` or `|T| ≤ 1`, the single-set
bound. Otherwise R2 gives a program for `(S − u, T)` (or `(S, T − u)`) with `m − 1` lines, or for
`(S − a, T − e)` with `m − 2` lines; these still meet in at most one point and the outputs are lines or leaves.
Induction: `m − 1 ≥ |S| + |T| − 3`, or `m − 2 ≥ |S| + |T| − 4`. ∎

**What the leaf lines give (paper).** Suppose (a) fails for every private `u`, disjoint case. Then:

* no line `A ∘ B` with both inputs leaves is `∩` or `∖` (its value is inside a leaf, so it is a leaf); it is
  `A ∪ B` with `A ∪ B` holding two points of `S` and two of `T` (with fewer than two on one side, removing a
  private one of the two on the other side leaves a leaf); so `A`, `B` are disjoint *edges* `{a, e}`, `a ∈ S`,
  `e ∈ T`.
* a line `X ∘ ℓ` with one leaf input `ℓ` is `X ∪ ℓ` with `ℓ` an edge disjoint from `X`, or `X ∖ ℓ` with `ℓ` an
  edge inside `X` (if `ℓ` adds, or removes, only one point `u`, removing `u` makes the line equal to `X`).

So every leaf enters as a whole edge that is added to, or cut from, a line. This is where monotonicity is used,
and it is exactly what `△` violates. It is not enough by itself (3.3).

### 3.3 The obstacle: rule R is false, R2 is open

**Rule R** (only part (a) of R2) is **false**. `B9_two_sets.py ruleR 3 5 d 10`: `S = {0,1,2}`, `T = {3,…,7}`,

```
X0 = {2,4} ∪ {0,7}    X1 = {2,7} ∪ {0,5}    X2 = {0,6} ∪ {2,3}    X3 = X2 ∪ X1     X4 = X3 ∖ X0
X5 = {1,4} ∪ X3       X6 = {0,5} ∪ {1,3}    X7 = {2,6} ∪ X6       X8 = X7 ∖ X4 = S  X9 = X5 ∖ X8 = T
```

has 10 lines (bound: 6), no dead line, and removing any single point of `S ∪ T` leaves all 10 lines needed
(checked by `needed` in the script). Removing a pair `a ∈ S, e ∈ T` leaves 8 lines for the pairs
`(0,3), (0,5), (0,7), (1,5), (1,7), (2,6), (2,7)`, so R2 holds here. Of these, `{0,7}, {0,5}, {2,6}, {2,7}` are
leaves and `(0,3), (1,5), (1,7)` are not; the leaves `{2,4}, {0,6}, {2,3}, {1,4}, {1,3}` give only one deletion.
Also false: rule R restricted to lines with a leaf input. With every leaf entering as a whole edge as in 3.2,
programs computing `S` and `T` exist (SAT, `|S| = 2, |T| = 3`, 9 lines), so the line that dies has two line inputs.

**Rule R2: tested, not proved.** Exact SAT, rule R (hence R2) holds for all programs (no dead line) with
`(|S|, |T|, lines)` = (2,2 disjoint, 4 and 8), (3,3 disjoint, 4, 6, 8, 12), (4,4 disjoint, 8),
(3,3 shared, 4 and 7), (2,3 shared, 6), (3,4 shared, 9), (4,4 shared, 10 and 12), (3,4 disjoint, 12). Where rule R fails (SAT: 4,4 disjoint at 11, 12, 13 lines; 3,5 disjoint at 10 and 12 lines),
R2 held on every sampled witness (60 random-phase SAT witnesses each at 4,4 disjoint with 11 and 12 lines and
3,5 disjoint with 10 and 12 lines; 0 failures).

**Exact smaller obstacle.** R2. A paper proof of R2 needs a rule for which pair to remove: in the example some
leaf pairs give two deletions and some give one, and some non-leaf pairs give two. Choosing the pair is the open
step.

## 4. Exact SAT, point lemma, `|S| + |T| − 3` lines

| sizes | shared | disjoint |
|---|---|---|
| (3,3) | UNSAT 0.0 s | UNSAT 0.0 s |
| (3,4) | UNSAT 0.0 s | UNSAT 0.0 s |
| (3,5) | UNSAT 0.2 s | UNSAT 0.3 s |
| (4,4) | UNSAT 0.2 s | UNSAT 0.1 s |
| (3,6) | UNSAT 3.2 s | UNSAT 3.3 s |
| (4,5) | UNSAT 1.8 s | UNSAT 1.3 s |
| (4,6) | **UNSAT 249.1 s** | **UNSAT 147.4 s** |
| (3,7) | **UNSAT 519.8 s** | **UNSAT 714.8 s** |
| (2, any) | paper (section 2) | paper (section 2) |
| (6,6) | unfinished, stopped after about 15 min | unfinished, stopped after about 15 min |

B6 has (5,5) shared and disjoint. With section 2 this gives the point lemma for two sets for every pair of sizes
with `|S| + |T| ≤ 10`, and for `min(|S|, |T|) ≤ 2` at every size.

## 5. Reproduce

```
python3 -I one-not/research/open/B9_two_sets.py lemma 4 6 d          # UNSAT
python3 -I one-not/research/open/B9_two_sets.py xor 3 3 s            # SAT: the bound needs the no-XOR basis
python3 -I one-not/research/open/B9_two_sets.py ruleR 3 5 d 10       # SAT: witness that rule R fails
python3 -I one-not/research/open/B9_two_sets.py ruleR 4 4 s 10       # UNSAT
python3 -I one-not/research/open/B9_two_sets.py r2 3 5 d 10 60       # R2 failures 0
```
