# U1: one payment Hall condition for one-NOT and several-NOT; counting across circuits and quantum

Seat U1 (Opus), BOARD.md CURRENT STATE, 2026-11-25. Serves: open-one-not (BottomPay) and open-many-not (point lemma,
S3(b)); section 5 serves T9. Words: **paper** = argued here; **tested** = computed by `U1_payment_hall.py` (exhaustive
where it says so); **checked** = Lean accepted it (nothing new is checked here). Nothing here proves BottomPay, the point
lemma, `no_minCE`, or anything about P versus NP.

## 0. Answer

1. **Yes, one statement.** Both open statements are instances of a *payment Hall condition* (PHC, section 1): a
   matroid partition problem whose matroids `M_w` are induced (Rado) from graphic matroids on the points of each set.
   In both programs the per-set rank is already proved (the unit run: A10 item 1, the flip lemma S3(a)); what is open in
   both is only the **partition**: disjoint bases. Both programs refuted the same naive proof, "one zero point per set"
   (A10: 242 states; B6 §3: the gate `(x_a ∧ x_e) ∨ (x_b ∧ x_f)`), and both need exactly the re-choice that Edmonds'
   matroid partition theorem describes.
2. **Instances.** (a) BottomPay (A10 §3) *is* PHC at the single point `1_Q`, payers = OR gates outside `top`.
   (b) **PHC@0 for point programs** (new, section 2.2) is PHC at the common point `0` with payers = lines; it
   **implies** the point lemma for the same family (take `A = ∅`), hence the thin-basis lemma and S3(b) (B5, B6). It is a
   strict strengthening, not a restatement.
3. **Tested (section 3).** PHC@0 holds **exhaustively** (every value tuple) on point programs with `base` lines for
   (2,3), (3,3) shared and disjoint, (3,4) shared and disjoint, (4,4) shared and disjoint, (3,5) shared and disjoint,
   tri3, star3, and with `base + 1` lines for (2,3), (3,3) disjoint and shared, (2,4); sampled at (4,4) shared and (4,5)
   shared with `base + 1` (30,000 tuples each), Pasch at `base` (3,000), and on 60 random programs each at 9 more
   sizes up to 11 lines. It holds at point `0` and over all zero points on all 21 stored circuits (0 to 6 NOT gates,
   including the C4w circuits t4, t5, t6). BottomPay (one-NOT) rerun: 0 failures (A14 script, n ≤ 7). **0 failures.**
4. **What failed (refuted, exact).** The OR-only form of PHC@0 (payers = `∪`-lines only, as in BottomPay) is
   **false for free difference**: a 5-line program for `|S| = 2, |T| = 4` disjoint (section 3.2), found in the
   exhaustive enumeration (2 of 18,936 tuples). It holds on every monotone (`∪, ∩` only) program tested. The failing
   program cuts `T` with `∖ S`, a difference by a line that is `0` at the point; in a one-NOT circuit a difference can
   come only from the cone of the one NOT gate. So **the single NOT wire `h` is exactly what keeps OR-only payment
   alive**, and several NOT gates force AND-type lines to pay too.
5. **Which theorem.** If PHC holds, the disjoint bases follow from **Edmonds' matroid partition theorem**
   (equivalently Nash-Williams' matroid union theorem; Rado's theorem is the one-matroid transversal case, Hall's the
   free case). Submodularity is free: the `r_w` are matroid ranks. What is NOT free is the inequality itself, which
   says that the set of all payers minimises the submodular function `f(A) = Σ_w r_w(A) − |A|`. No gate property
   proving it is known (section 4).
6. **Counting (section 5).** Shannon (L002), Knill (L116, `approx_count_twoQubit`) and L119 (15k+1) share one shape:
   a per-gate increment of a subadditive potential (log-count, log-volume, dimension) against the size of the whole
   space. They give existence of hard objects (almost every function or unitary), never an explicit one. The base bound
   has the same per-gate shape (one merge per gate per set) but is explicit; the price is that additivity across sets is
   no longer automatic. **PHC is exactly that missing additivity.** Nothing more is shared.

## 1. The payment Hall condition

Data: a finite set `E` of **payers**; a family of sets `S_w` (pairwise `|S_a ∩ S_b| ≤ 1`), each with a partition of its
points into **classes**; for each payer `g` and set `w` a list `Φ_w(g)` of **flip sets** (subsets of `S_w`).

`M_w` = the matroid on `E` in which `I` is independent iff each `g ∈ I` can pick two classes that both meet one flip set
in `Φ_w(g)`, the picked pairs forming a forest on the classes of `w`. (`M_w` is the matroid induced from the graphic
matroid of the complete graph on the classes through the bipartite graph payer–pair; Rado–Perfect: induced matroids are
matroids. With one flip set per payer it is the hypergraphic matroid of Lorea; independence = every nonempty
`J ⊆ I` spans at least `|J| + 1` classes, as A14 uses.) `need_w = #classes_w − 1`.

**PHC.** There are pairwise disjoint `E_w ⊆ E` with `E_w` a basis of `M_w` and `|E_w| = need_w`.

**Equivalent form (Edmonds 1965, Nash-Williams 1966).** Given `r_w(E) = need_w` for every `w`, PHC holds iff
`∀ A ⊆ E : Σ_w (need_w − r_w(A)) ≤ |E \ A|`, i.e. iff `E` minimises `f(A) = Σ_w r_w(A) − |A|` (a submodular function).

**PHC@Y** is PHC with `Φ_w(g) = {D_w(g, Y)}`, `D_w(g, Y) = {u ∈ S_w : g(Y + e_u) ≠ g(Y)}`, at one point `Y` that is a
zero point of every set in the family.

## 2. Instances

### 2.1 One NOT gate: BottomPay = PHC@1_Q (A10 §3, A14)

At a DD state `(Q, D)`: payers `E` = OR gates outside `top` with `g(1_Q) = 0`; the sets are the DD sets; classes = the
heavy atoms `U_w` joined into one class plus the light atoms as singletons; `Φ_w(g)` = the atoms `u` with
`g(1_Q + e_u) = 1`. `r_w(E) = need_w` is A10 item 1 (paper, the bottom unit run), so BottomPay is exactly PHC@1_Q. The
non-DD sets are paid separately at their top points `Z_w` (A7); they are not part of this instance.

### 2.2 Several NOT gates: PHC@0 for point programs (new) ⟹ point lemma

Point program (B6 §2): lines `X_i = A ∘ B`, `∘ ∈ {∪, ∩, ∖, reversed ∖}`, leaves partial transversals. Payers = lines,
classes = points, `Φ_w(X_i) = {X_i ∩ S_w}` (the sens set at `0`; B6's observation maps every circuit wire to its line).

* `r_w(lines) = need_w` (paper): the flip-lemma run at the single point `0`. Process lines in order with a union-find
  on `S_w`; invariant: every processed line meets `S_w` inside one class. Leaves meet `S_w` in at most one point. For
  `X = A ∘ B` with all four operations `X ⊆ A ∪ B`; if `A ∩ S_w` and `B ∩ S_w` lie in different classes and `X` meets
  both, join them (the line pays one forest edge from its own flip set), otherwise `X` stays inside one class. `S_w`
  itself is a line meeting every point, so at the end there is one class: `need_w` joins.
* PHC@0 ⟹ point lemma: `A = ∅` in the equivalent form gives `Σ_w need_w ≤ |lines|`.
* PHC@0 for a family `W` ⟹ thin-basis lemma ⟹ S3(b) Hall form for `W` (B6 §2, B5 §4, unchanged).

### 2.3 Several NOT gates on circuits: the forest form of S3(b)

Payers = wire classes (function up to complement); `Φ_w(g) = {D_w(g, Z) : Z a zero point of S_w}` (all zero points).
PHC here implies S3(b) Hall form (each `E_w ⊆ C(w)`, disjoint, `|E_w| = |S_w| − 1`). Weaker than PHC@0 (more flip
sets), so it is the form circuits may need if PHC@0 ever fails on a real circuit.

### 2.4 What the two programs share, exactly

| | one NOT (BottomPay) | several NOT (point lemma) |
|---|---|---|
| point | `1_Q`, common to all DD sets | `0`, common to all sets |
| classes | heavy atoms joined, light singletons | singletons |
| payers | OR gates (`∪`-lines) outside `top`, `0` at `1_Q` | all lines |
| per-set rank = need | proved (A10 item 1) | proved (flip lemma at one point, §2.2) |
| one point per set | refuted (242 states, A10) | refuted (B6 §3) |
| open | the partition | the partition (PHC@0, stronger than the point lemma) |
| operations below the point | `∪, ∩`; difference only by the cone of `¬h` (heavy class) | `∪, ∩, ∖` free |

The last row is the difference. On `H0 = {h = 0}` the circuit is the monotone `C1`; a wire that is `1` at the point and
can act as a subtrahend comes only from `¬h`, and its flip set on a DD set is the heavy class, which BottomPay already
joins. That is the property of the single NOT wire that the OR-only payment uses (section 3.2 shows it is needed).

## 3. Evidence

### 3.1 Tables (`U1_payment_hall.py`; enum = every distinct tuple of line values, exhaustive when below the cap)

| instance | lines | tuples | PHC@0 failures |
|---|---:|---:|---:|
| (2,3) disjoint | 3 = base | 9 (all) | 0 |
| (2,3) disjoint | 4 | 1,074 (all) | 0 |
| (3,3) disjoint / shared | 4 = base | 54 / 54 (all) | 0 / 0 |
| (3,3) disjoint | 5 | 16,164 (all) | 0 |
| (3,3) shared | 5 | 7,580 (all) | 0 |
| (3,4) disjoint / shared | 5 = base | 540 / 540 (all) | 0 / 0 |
| (2,4) disjoint | 5 | 18,936 (all) | 0 |
| (4,4) disjoint / shared | 6 = base | 6,480 / 6,480 (all) | 0 / 0 |
| (3,5) disjoint / shared | 6 = base | 8,100 / 8,100 (all) | 0 / 0 |
| (4,4) shared, (4,5) shared | 7 | 30,000 each (cap) | 0 |
| tri3, star3 | 6 = base | 2,430 each (all) | 0 |
| Pasch | 8 = base | 3,000 (cap) | 0 |
| random programs (`prog`, 60 each): (2,3,d,3), (3,3,d,4), (3,3,d,6), (3,4,d,7), (3,5,d,6), (3,5,d,10), (4,4,d,6), (4,4,d,11), (4,5,d,8) | | 540 | 0 |
| stored circuits, PHC@0 (`circ0`) and all zero points (`circ`): 17 in `research/data/witnesses`, 4 C4w in `nonlocal` (4 to 6 NOT gates) | | 21 + 21 | 0 + 0 |
| BottomPay rerun (`A14_bottom_hall.py --maxn 7 --states 30`) | | 2,503 DD states | `union_fail 0` |

At `base` lines PHC@0 says more than the point lemma: every line is used exactly once, so a tight program **decomposes**
into one spanning forest per set.

### 3.2 The OR-only form fails with free difference (exact)

`python3 -I U1_payment_hall.py enum 2 4 d 5 20000 --union`, `S = {0,1}`, `T = {2,3,4,5}`:

```
X0 = {0,5} ∪ {1,3} = {0,1,3,5}     X1 = {1,4} ∪ {0,2} = {0,1,2,4}     X2 = X1 ∪ X0 = {0,...,5}
X3 = X0 ∩ X1 = {0,1} = S           X4 = X2 ∖ X3 = {2,3,4,5} = T
```

The `∪`-lines are `X0, X1, X2`; `T` needs 3 of them (forest `3–5`, `2–4`, then `X2`), `S` needs one more: 4 > 3. With all
lines as payers `S` takes `X3` and PHC@0 holds. Monotone programs (`∪, ∩` only; samples of 19,026 to 20,000 tuples at
(2,4) d, (3,3) d, (3,4) s with `base + 1` lines and tri3 with 7): OR-only PHC@0 0 failures. The failure uses `∖` by a
line that is `0` at the point (`X3 = S`), which a one-NOT circuit cannot do below `H0` (section 2.4). This is not a
BottomPay counterexample: in a one-NOT circuit with `h` the wire of `X3`, `S` is non-DD and is paid at its top point.

## 4. What property would prove it (honest)

* Submodularity is not the issue: PHC is a min-max statement about matroid ranks, so Edmonds' theorem applies as soon as
  the inequality `Σ_w (need_w − r_w(A)) ≤ |E \ A|` holds. The inequality is the whole content and is open in both programs.
* **Monotone circuits** supply it by a rigid choice: one top point `Z_w` per set whose runs are disjoint (A9,
  `heavy_overlap_false`). Both programs refuted the rigid choice at the bottom point, so a proof must produce the
  partition by exchange, not by a point choice.
* **One NOT gate**: A14 observes that every gate useful for two DD sets is `1` at their common point (177 of 177 pairs).
  A proof of BottomPay could try an exchange rule driven by the common point.
* **Several NOT gates**: PHC@0 is closed under deleting a point from the universe only in the weak sense of rule R2
  (B9 §3.2). A stronger induction hypothesis is the point of PHC@0: if a deletion argument can carry a partition (not only
  a count) from `(S − u, T)` back to `(S, T)`, R2 is no longer needed. Untested.
* Scale (B5 remark 2): PHC@0 for all projective planes would give an explicit superlinear lower bound on AND/OR gates
  for circuits with any number of NOT gates. That is not expected to follow from anything here; PHC is a target for
  fixed small families, and for large designs a failure is the place to look.

## 5. Counting across circuits and quantum

| statement | Lean | what is counted | per-gate increment | conclusion |
|---|---|---|---|---|
| Shannon (L002) | `PEqualNP.MetaComplexity.L002` | circuits of size `s` vs `2^{2^n}` functions | `O(log s)` bits | some `f` needs `2^n/(4n)` gates |
| Knill count (L116, `approx_count_twoQubit`) | `Open/ApproxCount.lean` | `ε`-balls around `k`-gate products (net) × ball measure (L115) | `log` net size `≈ 32 log(Ck/ε) + 2 log(n+1)` | the `ε`-reachable set has Haar measure `≤ (…)^k (cε)^{4^n}` |
| L119 (15k+1) | `Open/KnillParam15.lean::L119_fifteen` | real dimension of a differentiable cover | 15 parameters | `15k + 1 < 4^n` ⇒ reachable set is Haar-null |
| base (one NOT, several NOT) | per-set: `FlipLemma`, A10 item 1 | rank of the union of graphic matroids on the sets | 1 merge per set per gate | `gates ≥ base` **if** PHC |

Shared: a potential that grows by a bounded amount per gate (log-count, log-volume, dimension, rank), compared with what
the target requires. Not shared: Shannon, Knill and L119 compare the potential of **all** `k`-gate circuits with the size of
the **whole** space, so they prove that almost every function or unitary is hard and name none; additivity over gates is
automatic (a product of counts, a sum of dimensions). The base bound measures one **explicit** target, so it says which
function is hard, but additivity across the sets is not automatic: one gate can merge for several sets. PHC is precisely
the additivity statement. The counting side gives no information about PHC and PHC gives none about counting; L119 is not
an explicit lower bound for any unitary. No result connects them beyond this shape.

## 6. Next lines (written on the task boards, SEAT SIZE)

open-many-not:

- OPEN (Sonnet): SAT/enum, PHC@0 (U1 §2.2: lines split into disjoint spanning forests, one per set, each line paying one pair inside its own value) on point programs for Fano (13 and 14 lines) and two 5-sets (shared and disjoint, 8 and 9 lines): extend `U1_payment_hall.py enum` to a family argument, cap 10^5 tuples, record tuples, exhaustive or capped, failures; a failure at >= base lines refutes PHC@0, not the point lemma. -> research/one-not/research/open/U1_unify.md s3
- OPEN (Sonnet): paper proof, OR-only PHC@0 for monotone point programs: every program of union/intersection lines over partial transversals of W (pairwise |S cap T| <= 1) with every S_w among its lines has pairwise disjoint sets E_w of union-lines, |E_w| = |S_w| - 1, each E_w a spanning forest of S_w with each line's edge inside its own value. Start with two sets. -> research/one-not/research/open/U1_phc_monotone.md
- OPEN (Sonnet): PHC@0 under point deletion (U1 §4): on the exhaustive tuples of U1 s3.1, for each program and private point u, take a PHC@0 partition of the cleaned program for (S - u, T) and test whether it extends to a partition for (S, T) by adding lines; record extendable / not, and the smallest non-extendable program. -> research/one-not/research/open/U1_unify.md s4

open-one-not:

- OPEN (Sonnet): Lean, `PaymentHall` (U1 §1) as a Prop: payers a Finset, per set a hyperedge map payer -> Finset of points, disjoint per-set forests of size need_w; theorem `card_ge_of_paymentHall` (sum need_w <= card payers) and `bottomPay_of_paymentHall` stating BottomPay (Open/LightAbsorb.lean) as the instance at 1_Q. -> proofs/w951/PEqualNP/W951/Open/PaymentHall.lean

## 7. Reproduce

```
cd research/one-not/research/open
python3 -I U1_payment_hall.py enum 3 5 d 6 20000           # exhaustive at base: 0 failures
python3 -I U1_payment_hall.py enum 2 4 d 5 20000 --union   # OR-only: 2 failures (section 3.2)
python3 -I U1_payment_hall.py circ0 ../../data/witnesses/*.json ../../data/witnesses/nonlocal/general*.json
python3 -I U1_payment_hall.py prog 4 4 d 11 60
```
