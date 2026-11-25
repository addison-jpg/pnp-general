# B10: the point lemma for two sets when |S| = 3

Seat B10 (Sonnet), board `boards/tasks/open-many-not.md`. Setting, words and the tight-tree lemma are those of
`B9_point_two_sets.md` (sections 1 and 2). **paper** = proved here, not in Lean. Nothing here settles P versus NP.

## 0. Answer

**Paper proof, complete (proved on paper, not checked in Lean).** `|S| = 3`, any `T`, `|S ∩ T| ≤ 1`: every program
with `S` and `T` among its lines has at least `|T| + 1 = |S| + |T| − 2` lines. For `|T| ≤ 2` this is B9 section 2
(roles swapped), so take `t = |T| ≥ 3`. Suppose a program has `m ≤ t` lines. Contradiction below.

## 1. Setup

`D` = lines below `T` (with `T`), `g = |D|`; `T` is a line (`t ≥ 2`), `S` is a line (3 points of `S`, no leaf has
more than 1). Single-set bound: `g ≥ t − 1`, and `g ≤ m ≤ t`.
Let `λ` = number of leaf slots of `D` and `e = Σ_{X ∈ D, X ≠ T} (readers of X in D − 1) ≥ 0` (a line read by the same
line twice counts 2). Slot count: `2g = λ + (g − 1) + e`, so `λ = g + 1 − e`. Each point of `T` is in a slot,
each slot holds ≤ 1 point of `T`, so `λ ≥ t`.
Put `Z = S ∖ T`; `|Z| ≥ 2`, and `S ⊄ T`.

Two facts used throughout (all four operations send (0,0) to 0, and a point lies in no slot ⇒ in no line):

* **(Sing)** A point `τ` of `T` lying in exactly one slot `ℓ` is a *singleton*. Evaluate the program at `τ`: slot `ℓ` is 1,
  every other slot 0. The value must be 1 at `T`, so every node on a path of 1s from `ℓ` to `T` has value 1; if a
  node `N = A ∘ B` on it has `A` (the path side) = 1 and `B` = 0 (in a tree `B` has no slot of `τ`), then `∘ ∈ {∪, A∖B}`.
* **(Forced ∪)** In a tree, a line with a singleton below each of its two inputs is `∪` (one side needs `∪ or A∖B`,
  the other `∪ or B∖A`). Consequently, if every line on the way from a node `N` to `T` is `∪`, then `N ⊆ T`.
* **(Kill)** `z ∈ Z`: evaluated at `z`, `S = 1` and `T = 0`; so on the path from `S` to `T` some line `N = A ∘ B`
  has path input `A = 1` and value 0, so `N` is not `∪`. If `N = Y ∖ ℓ` with `ℓ` a leaf, then `z ∈ ℓ`, and `ℓ` has at most
  one point of `S`: **one such line kills at most one point of `S`**.

## 2. Case g = t − 1

Then `λ = g + 1 − e ≥ t = g + 1` forces `e = 0`, `λ = t`: the single-set bound is tight, so by the tight-tree
lemma (B9 s2) every line of `D` is `⊆ T`. `S ⊄ T`, so `S ∉ D`, so `S` is the one remaining line, `m = t`, and its two
inputs are leaves or lines of `D`, each with at most one point of `S` (leaf, or `⊆ T`). `S ⊆ A ∪ B` gives
`|S| ≤ 2`. Contradiction.

## 3. Case g = t (so m = t, every line lies in D, S ∈ D, S ≠ T)

`λ = t + 1 − e ≥ t`, so `e ∈ {0, 1}`.

### 3.1 e = 0: D is a tree, λ = t + 1 slots

The `t` points of `T` fill `t` or `t + 1` slot-memberships, one per slot at most. Either (Ia) one slot `ℓ0` holds no
point of `T` and all `T`-points are singletons, or (Ib) every slot holds a `T`-point and exactly one `T`-point `u` is in
two slots `ℓ1, ℓ2` (the rest singletons).

**(Ia).** A line with a side having no singleton must have that side equal to the leaf `ℓ0` (a line has ≥ 2 slots, hence
a singleton). So all lines are `∪` (Forced) except possibly `P = ℓ0 ∘ Y`, and `Y` has a singleton, so `P ∈ {∪, Y∖ℓ0}`.
`S` is on the unique path to `T`, which has at most one non-`∪` line, killing at most one point of `S` (Kill).
But `|Z| ≥ 2` points need killing. Contradiction.

**(Ib1)** `ℓ1, ℓ2` are the two inputs of one line `Q`. Only `Q` and its reader `P = Q ∘ Y` may be non-`∪`. `u` lives only in
`ℓ1, ℓ2`, so `u ∈ Q` and `P` keeps `u`; `Y` has a singleton (all slots outside `ℓ1, ℓ2`), so `P = ∪`. All lines
strictly above `Q` are `∪`. `S` is not below `Q` (its inputs are leaves); `S = Q` gives `S ⊆ ℓ1 ∪ ℓ2`, `|S| ≤ 2`; `S` above
`Q` or elsewhere gives `S ⊆ T` by Forced. Contradiction.

**(Ib2)** `ℓ1, ℓ2` are not siblings. The only sides without a singleton are the leaves `ℓ1` and `ℓ2`, so only their
readers `P1 = ℓ1 ∘ Y1`, `P2 = ℓ2 ∘ Y2` can be non-`∪`, each of the form `Y_i ∖ ℓ_i` (`Y_i` has a singleton). By Kill,
each kills ≤ 1 point of `S`, and `|Z| ≥ 2`, so both lie on the path from `S` to `T`, so (tree) one is below the other,
say `P1` inside `Y2`. Then `u ∈ ℓ1` gives `u ∉ P1`, `u ∈ ℓ2` gives `u ∉ P2 = Y2 ∖ ℓ2`, nothing else holds `u`, so
`u ∉ T`. Contradiction.

### 3.2 e = 1: λ = t, every slot is a distinct singleton

Exactly one line `X ≠ T` is read twice. Every slot holds exactly one `T`-point, all distinct, so all `T`-points are singletons.

**(IIa) `P = X ∘ X`.** At a point `τ` below `X`, `P` must be 1, so `P` is `∪` or `∩` and `P = X` (as a set; `∖` gives `∅` and
loses `τ`). Delete `P` (its readers read `X`): a tree with `t − 1` lines, `t` slots, `t` distinct singleton points
(tight). By the tight-tree lemma all its lines are `⊆ T`. `S` is `P` (`= X`) or one of these lines, so `S ⊆ T`. Contradiction.

**(IIb) `X` is read by two different lines `P, Q`.** The cone of `X` is a tree (lines below `X` are read once). For a slot `ℓ`
in the cone, the point `τ_ℓ` evaluates 1 only at nodes above `ℓ`; those on the path to `X` must be 1 (a 0 stays 0 up to
`T`, since all other inputs are 0), and a line of the cone with a slot of `τ_ℓ` on one side and a slot `τ_ℓ'` on the other
is `∪` by Forced. So **the cone is all `∪`, `X` is the union of its slots, and `S ⊆ X` if `S` is in the cone.**
Now cut at `X`: `D_top` is a tree whose leaves are the `r` real slots outside the cone and two pseudo-leaves `X1` (read
by `P`) and `X2` (read by `Q`). `r ≥ 1` (else `P = Q`). By Forced, every line with real slots on both sides is `∪`;
a line with a side lacking real slots has that side `= X1` or `X2`. So only `P = X1 ∘ Y` and `Q = X2 ∘ Z'` can be non-`∪`;
`Y` and `Z'` contain a real slot, so (Sing) `P ∈ {∪, Y∖X1}`, `Q ∈ {∪, Z'∖X2}`.
At the point `τ` of a cone slot: `X = 1`, all real slots 0. In the incomparable case (`Y` has no `X2`, `Z'` no `X1`) `Y = Z' = 0`,
and `T = 1` needs `P = ∪` or `Q = ∪`. In the nested case (`Q` inside `Y`, say) `Y = Q`-value and `T = 1` needs `P = ∪`. So in
both cases some line `W ∈ {P, Q}` is `∪` with `X ⊆ W`, and everything above is `∪`: **`X ⊆ T`.**
A non-`∪` line here has the form `Y ∖ X1` or `Z' ∖ X2`; it removes only points of `X ⊆ T`. So no point of `Z` is killed
(a point of `Z` is not in `T`, hence not in `X`). Every line on any path from `S` to `T` then keeps the points of `Z` that
reach it, so `Z ⊆ T`, contradicting `|Z| ≥ 2`. (If `S` is in the cone, `S ⊆ X ⊆ T`.) Contradiction.

All cases end in a contradiction, so `m ≥ t + 1`. ∎

## 4. Where it was used, and tests

* Used: tight-tree lemma (case g = t − 1, IIa), monotonicity of the four operations through the singleton evaluations
  (so XOR is excluded, as B9 s3.1 requires), `|S ∩ T| ≤ 1` (only through `|Z| ≥ 2`), `|S| = 3` (only in `|S| ≤ 2` contradictions
  and `|Z| ≥ 2`). For `|S| = 2` the same proof's kill count is not enough (`|Z|` may be 1), as B9 expects.
* Exact SAT, `python3 -I research/one-not/research/open/B9_two_sets.py lemma 3 q s|d`, `q = 3..6`: all UNSAT at `q = |S|+|T|−3 = t`
  lines (shared 0.0, 0.0, 0.1, 2.1 s; disjoint 0.0, 0.0, 0.1, 1.9 s). These cover every case of section 3 at those sizes
  (the SAT allows any program of `t` lines, dead lines included). `q = 7` is in B9 s4 (UNSAT, 520 s and 715 s).
* Control, same encoding with `t + 1` lines (the lemma bound): SAT for `q = 3, 4, 5`, shared and disjoint, so the bound is tight.
* Not tested separately: the individual cases (the SAT has no case-restricted mode); they are only covered through the global UNSAT.

## 5. What this does and does not give

`|S| = 3` is settled on paper for every `T`. `|S| ≥ 4` is open: the kill count fails (a line can kill `|S|−1` points
across a long path, `X ∖ X1` kills any number when `X1` holds several points of `S`, and `e` can exceed 1 once
`m` is allowed to exceed `|T|`). The statement R2 of B9 s3.2 stays the route for `|S| ≥ 4`.
