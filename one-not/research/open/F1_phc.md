# F1: the payment Hall condition in deletion form; what the split between sets really is

Seat F1 (Fable), BOARD.md TEAM, 2026-11-25. Serves: open-one-not (BottomPay) and open-many-not (PHC@0, point lemma).
Words: **paper** = argued here step by step; **checked** = Lean accepted it (`Open/PHC.lean`, axioms propext,
Classical.choice, Quot.sound); **tested** = computed by `F1_phc_tight.py`; **cited** = a classical theorem, quoted
from memory, not reopened. Nothing here proves BottomPay, PHC@0, the point lemma, `no_minCE`, or anything about
P versus NP.

## 0. Answer

**No proof of PHC.** What is settled here:

1. **Lemma D, the deletion form (paper; necessity checked).** The matroid of U1 §1 is the hypergraphic matroid of
   the payers' hyperedges, and for it the Edmonds / Nash-Williams condition collapses to one inequality over one set:

   > PHC  ⟺  for every `J ⊆ E`:  `Σ_w (c_w(J) − 1) ≤ |E ∖ J|`,

   where `c_w(J)` is the number of connected components of the classes of `w` when two classes are joined whenever
   one payer of `J` has both in its hyperedge. No matroid rank is left in the statement: only connectivity.
   In words: *delete any `k` payers; the sets fall into at most `k` extra pieces in total.*
2. **Corollary F (paper): the split between sets is a count.** PHC for an instance is the conjunction, over all `J`,
   of the plain count "payers ≥ Σ (classes − 1)" for the instance in which the payers of `J` are made free
   (their hyperedges become part of the classes). So PHC@0 for all point programs is **equivalent** to the point
   lemma for programs with free lines, and BottomPay at a state is equivalent to the bottom count with free gates.
   U1's row "open: the partition" can be replaced by "open: the count, for the class of instances closed under
   freeing a payer". There is no separate exchange problem.
3. **Tightest subfamilies (tested, section 3).** The deletion sets `R = E ∖ J` with equality form a lattice (union,
   intersection). In **every** instance tested (BottomPay at all DD states of the stored circuits `n ≤ 9` with two or
   more DD sets, 60 switch circuits, and all enumerated point programs at `base` and `base + 1` lines) **every
   block of that lattice splits exactly one set** (0 blocks split two). Where the bound is tight, the split is
   forced block by block; a re-choice between two sets is needed only where there is slack.
4. **Peeling (section 4).** The local statement "from every `J ≠ E` some payer can be put back while `Σ_w c_w`
   drops by at most 1" implies PHC and is **false**, in both programs: a 5-line point program for two 3-sets with a
   common point (slack 1; 24 of the 7,580 tuples), a 7-line one for disjoint 3-sets, a 17-line monotone one, and 63
   BottomPay instances of the stored one-NOT circuits `n ≤ 9` (slack 2). So no order of putting payers back one
   by one proves PHC; the inequality is not local in `J`.
5. **A gap in the record (section 5).** U1 §2.1 and A10 item 1 are quoted as "per-set rank proved" for BottomPay.
   The run of A10 item 1 produces `need_w` OR gates, but the payers `E` exclude the top family, and that the run
   avoids `top` is only tested (0 states). Gates of `top` that are `0` at `1_Q` and useful for a DD set do exist
   (4,444 of the 136,843 DD states `n ≤ 9`); the rank without them is never short (0 states). Proved here (paper):
   the cases non-DD `v` with `h(Z_v) = 0`, and the heavy run of the same set. Open: a gate of the heavy run (or of
   an all-heavy non-DD run) of **another** set `v` that is `1` at a light atom outside `S_v`.
6. **Exact smallest obstacle (section 6).** The class point lemma for two sets.

## 1. Lemma D

**Setting (U1 §1 with one flip set per payer).** `E` finite; for each set `w` a finite set `K_w` of classes and for
each `g ∈ E` a hyperedge `V_w(g) ⊆ K_w`. `M_w`: `I ⊆ E` is independent iff every `g ∈ I` can pick a pair of distinct
classes inside `V_w(g)`, the picked pairs forming a forest. `need_w = |K_w| − 1`. PHC: pairwise disjoint `E_w`, each
a spanning tree of `K_w` in this sense. For `J ⊆ E` let `G_w(J)` be the graph on `K_w` with an edge for every pair
inside some `V_w(g)`, `g ∈ J`, and `c_w(J)` its number of components.

**Lemma D.** PHC ⟺ `∀ J ⊆ E : Σ_w (c_w(J) − 1) ≤ |E ∖ J|`. More exactly, the largest size of a disjoint union of
independent sets is `min_J ( |E ∖ J| + Σ_w (|K_w| − c_w(J)) )`.

*Proof of ⟹ (paper, and checked: `PHC.lean::deletion_of_forestPay`).*
Step 1. Fix `w` and `J`. Colour each class by its component in `G_w(J)`. A payer `g ∈ E_w ∩ J` picked a pair inside
`V_w(g)`, which is inside one component: its edge is one-coloured.
Step 2. A connected graph in which at most `k` edges are two-coloured has at most `k + 1` colours (induction on `k`:
recolour one end-colour of a two-coloured edge into the other; one colour disappears, no one-coloured edge becomes
two-coloured, that edge becomes one-coloured; `card_colours_le`).
Step 3. So `c_w(J) − 1 ≤ |E_w ∖ J|`. The `E_w` are disjoint, so `Σ_w (c_w(J) − 1) ≤ |∪_w E_w ∖ J| ≤ |E ∖ J|`. ∎

*Proof of ⟸ (paper, from two cited theorems).*
Step 1 (rank of an induced matroid; Rado 1942, Perfect 1969; cited). `M_w` is induced from the graphic matroid `N_w`
of the complete graph on `K_w` through the bipartite graph "payer `g` – pair inside `V_w(g)`". For an induced
matroid `r(A) = min_{J ⊆ A} ( |A ∖ J| + ρ(Γ(J)) )`, `Γ(J)` the neighbours of `J`, `ρ` the rank of `N_w`. Here `Γ(J)`
is the edge set of `G_w(J)` and `ρ(Γ(J)) = |K_w| − c_w(J)`. Hence

`r_w(A) = min_{J ⊆ A} ( |A ∖ J| + |K_w| − c_w(J) )`.

Step 2 (matroid union; Edmonds 1965, Nash-Williams 1966; cited). The largest disjoint union of independent sets has
size `min_{A ⊆ E} ( |E ∖ A| + Σ_w r_w(A) )`. As `r_w ≤ need_w`, PHC holds iff this minimum is `≥ Σ_w need_w`.
Step 3. Insert Step 1: PHC ⟺ for every `A` and every choice `J_w ⊆ A`:
`Σ_w (c_w(J_w) − 1) ≤ |E ∖ A| + Σ_w |A ∖ J_w|`.
Step 4 (one `J` is enough). Assume the deletion form. Given `A` and `J_w ⊆ A`, put `J = ∩_w J_w`. Fewer payers,
more components: `c_w(J_w) ≤ c_w(J)`. And `E ∖ J = ∪_w (E ∖ J_w) ⊆ (E ∖ A) ∪ ∪_w (A ∖ J_w)`. So
`Σ_w (c_w(J_w) − 1) ≤ Σ_w (c_w(J) − 1) ≤ |E ∖ J| ≤ |E ∖ A| + Σ_w |A ∖ J_w|`, which is Step 3. The formula for the
maximum follows the same way (the minimum over `A, (J_w)` is attained at `A = J_w = J`). ∎

Remarks. (a) `J = E` gives `c_w(E) = 1`: the per-set requirement is part of the one inequality. (b) The function
`J ↦ |E ∖ J| − Σ_w (c_w(J) − 1)` is submodular (modular plus graphic ranks), so the `J` with equality form a lattice.
(c) With several flip sets per payer (U1 §2.3) the same proof gives the form with `G_w(J)` built from all flip
sets of `g`, provided "pick a pair inside one flip set" is the independence rule. (d) Tested: on every instance of
section 3 the brute-force minimum over `J` equals `union − Σ need` from A14's Edmonds partition (0 mismatches).

## 2. Corollary F: freeing payers; the partition is a count

**Freed instance.** For `J ⊆ E` let `I/J` be the instance with payers `E ∖ J` and classes `K_w / J` = the components
of `G_w(J)`, each remaining payer keeping its hyperedge (as a set of components). The count for `I/J` reads
`|E ∖ J| ≥ Σ_w (c_w(J) − 1)`. So Lemma D says: **PHC(I) ⟺ the count holds for every `I/J`.**

**Point programs.** For a program `P` and a set `J` of its lines, `P/J` is the program whose lines are those outside
`J` and whose leaves are the thin leaves together with the values of the lines of `J`. Every leaf of `P/J` meets
every `S_w` inside one class of the partition `π_w` = components under `J`. Define

> **Class point lemma.** `π_w` a partition of `S_w` for each `w`; a *leaf* is any set meeting every `S_w` inside one
> class of `π_w`; lines `A ∘ B`, `∘ ∈ {∪, ∩, ∖, reversed ∖}`. If every `S_w` is a line, there are at least
> `Σ_w (|π_w| − 1)` lines.

With singleton classes it is the point lemma (B6, B9). By Lemma D:

* class point lemma for all leaf families ⟹ PHC@0 for all point programs ⟹ point lemma;
* PHC@0 for all point programs ⟺ class point lemma restricted to the leaf families `leaves ∪ values(J)` that come
  from programs.

So PHC@0 is not a second problem on top of the point lemma (U1 §0 item 2 calls it a strict strengthening): it is
the same counting statement, asked hereditarily. A proof of the point lemma by an induction that tolerates free
lines proves PHC@0 at once; a proof that cannot tolerate them proves only the root count.

**One NOT gate.** BottomPay at `(Q, D)` ⟺ for every set `J` of payers (OR gates outside `top`, `0` at `1_Q`):
`Σ_{w DD} (c_w(J) − 1) ≤ |E ∖ J|`, components taken among the heavy class and the light atoms of `w`.

**First cases, point programs (paper).** Write `R = E ∖ J`.
* Per set: `c_w(J) − 1 ≤ |R|` for every `J`. Run of U1 §2.2 started from the partition into components under `J`:
  a line of `J` lies in one class by definition; a line outside `J` is inside the union of its two inputs, which lie
  in one class each, so it joins at most two classes; `S_w` is a line, so the run ends with one class.
* A set `w` has `c_w(J) ≥ 2` only if every line whose value contains two classes, in particular every line with
  value `⊇ S_w`, is in `R`.
* `|R| = 1`: at most one set has its line in `R`; the inequality is the per-set bound.
* `|R| = 2`: if one set is split, per-set bound. If two sets `S, T` are split, `R` is their two lines;
  `S = A ∘ B ⊆ A ∪ B` where each of `A`, `B` is a leaf, a line of `J`, or the line `T` (which has at most one point
  of `S`), so `c_S(J) ≤ 2`; the same for `T`; `1 + 1 ≤ 2`.
* `|R| ≥ 3` with two split sets is the class point lemma with two sets and `|R|` lines: open.

## 3. Attack first: the tightest subfamilies (tested)

`F1_phc_tight.py` computes, by brute force over all deletion sets `R` of useful payers, `slack(J)`, the lattice of
tight `R` (slack 0), its inclusion-minimal nonempty members and its blocks (for a join-irreducible tight `R` with
largest tight proper subset `R'`, the block is `R ∖ R'`; it *splits* `w` when `c_w` rises from `R'` to `R`).

| instances | studied | min slack | blocks splitting 1 set / 2 or more | minimal tight `R` holding a shared payer | peeling fails |
|---|---:|---:|---:|---:|---:|
| BottomPay, stored one-NOT circuits `n ≤ 9`, every mixed state: 136,843 DD states, 105,631 with one DD set | 30,330 (882 more skipped: over 14 useful gates) | 0 | 56,625 / 0 | 564 of 40,830 | 63 (slack 2) |
| BottomPay, 60 switch circuits (`--gen 60`), every state: 252,927 DD states | 45,771 | 0 | 70,014 / 0 | 0 of 62,882 | 0 |
| programs (3,3) disjoint, 4 = base | 54 (all) | 0 | 216 / 0 | 0 | 0 |
| programs (3,4) disjoint, 5 = base | 540 (all) | 0 | 2,700 / 0 | 0 | 0 |
| programs (4,4) disjoint and shared, 6 = base | 6,480 each (all) | 0 | 38,880 / 0 each | 0 | 0 |
| programs (3,5) disjoint, 6 = base | 8,100 (all) | 0 | 48,600 / 0 | 0 | 0 |
| programs (3,3) disjoint, 5 | 16,164 (all) | 0 | 37,008 / 0 | 0 | 0 |
| programs (3,3) shared, 5 | 7,580 (all) | 0 | 17,448 / 0 | 0 | 24 (slack 1) |
| programs (2,4) disjoint, 5 | 18,936 (all) | 0 | 41,532 / 0 | 0 | 0 |
| programs (3,4) shared, 6 | 20,000 (cap) | 0 | 59,815 / 0 | 0 | 16 (slack 1) |

"min slack 0" is PHC (Lemma D); the minimum is attained at `R = ∅`. A single-DD-set state is the per-set run and
is not studied. Lemma D itself: 3,000 random instances (2,429 with PHC false), brute-force minimum against A14's
Edmonds partition, 0 mismatches (`lemmaD` mode).

Reading. At `base` lines every program has exactly `base` blocks, all single lines, each splitting one set: the
partition is unique and forced line by line. With one more line, and at the DD states, the tight part is still
made of single-set blocks, although a minimal tight set can hold a payer useful for two sets (564 cases). A tight
block splitting two sets never occurs. So on this data the re-choice that Edmonds' theorem allows is needed only
where there is slack, never where the inequality is tight.

Not a theorem. Stated as a target on the board (single-set blocks), with the warning that it does not imply the
inequality by itself.

## 4. Peeling: a local sufficient condition, and where it fails

**Peeling.** For every `J ≠ E` there is `g ∈ E ∖ J` with `Σ_w ( c_w(J) − c_w(J + g) ) ≤ 1`.

Peeling ⟹ PHC (paper): put payers back one at a time; `Σ_w (c_w − 1)` falls from its value at `J` to its value at
`E`, which is `0` when every set is connected under `E`, by at most 1 per step, in `|E ∖ J|` steps. The converse is false.

**Refuted (exact, section 3 table, last column).** Smallest: `S = {0,1,2}`, `T = {0,3,4}`, 5 lines (base 4):

```
X0 = {0} ∪ {1,3} = {0,1,3}   X1 = X0 ∪ {2}   X2 = X0 ∪ {4}   X3 = X2 ∖ {1} = T   X4 = X1 ∖ {3} = S
```

At `J = ∅` the costs of putting back one line are 2, 3, 3, 2, 2: peeling fails with slack 1. On one-NOT circuits:
63 of the 30,330 studied BottomPay instances have a `J` (slack 2) from which every payer costs at least 2. The
rule "put back the earliest payer" also fails (2,010 DD instances; 1,764 of 16,164 programs (3,3) disjoint with
5 lines) and holds at `base` lines in every program enumerated.

Disjoint sets, `S = {1,2,3}`, `T = {4,5,6}`, 7 lines (base 4):

```
X0 = {1,4} ∪ {2,5}   X1 = X0 ∪ {3}   X2 = X1 ∖ {4}   X3 = X2 ∖ {5} = S
Y1 = X0 ∪ {6}        Y2 = Y1 ∖ {1}   Y3 = Y2 ∖ {2} = T
```

At `J = ∅` every line holds at least two pairs in total, so every first step costs 2: peeling fails, with slack 3.
A monotone program does the same in 17 lines (cut `{1,2,3,4,5}` by `∩` with `{1,2,3,4,6}`, and so on), with all
lines or with only the `∪`-lines as payers. In everything seen peeling fails only at a `J` with slack at least 1;
it is not a route to PHC.

## 5. The per-set rank of BottomPay: what is proved and what is tested

Claim needed: `c_w(E) = 1` for every DD set `w`, i.e. the bottom run of `w` (A10 item 1) can be made of gates
outside `top`. A10 item 1 proves the run has `need_w` OR merges in `F2Mix`; A10 item 3 reports "never in `top`"
as data (0 states). Tested here at the 136,843 DD states `n ≤ 9`: an OR gate of `top` that is `0` at `1_Q` and
useful for a DD set exists at 4,444 states (253 of 252,927 on the switch circuits), and the DD sets are still
connected by `E` alone at every state (0 short).

Let `g` be an OR gate, `g(1_Q) = 0`, `g(P_t) = g(P_{t'}) = 1` with `t, t'` in different classes of the DD set `w`
(so one of them, say `t`, is light or they are a light and a heavy atom).

* (paper) `g ∉ M_v` for non-DD alive `v` with `h(Z_v) = 0`. At most one of `t, t'` is in `S_v`; say `t ∉ S_v ∪ D`.
  Then `P_t ≤ Z_v`, `h(Z_v) = 0` gives `h(P_t) = 0`, both points are in `H0` where every wire is monotone, so
  `g(Z_v) = 1`; a merge of `M_v` is `0` at `Z_v`.
* (paper) a merge of the bottom run of `w` is not in the heavy run `H_w` of the same set. A gate `g = a ∨ b` of `H_w`
  has heavy atoms `u` under `a` and `u'` under `b`; `g(1_Q) = 0` gives `a(1_Q) = b(1_Q) = 0`, so in the bottom run the
  `1`-atoms of `a` and of `b` each lie in one class, and both classes contain a heavy atom: the same class. No merge.
* (paper) in the remaining cases (`v ≠ w`, `h(Z_v) = 1`, `g ∈ H_v` or `v` non-DD with all atoms heavy) every atom
  `s ∉ S_v ∪ D` with `g(P_s) = 1` is light (`sign_of_drop`: `g` falls from `P_s` to `Z_v`).
* **Open.** Exclude: `g = a ∨ b ∈ H_v` (or `M_v`, all-heavy `v`), `0` at `1_Q` and at `Z_v`, `1` at heavy atoms
  `u, u'` of `v`, and `1` at a light atom `t ∈ S_w ∖ S_v` and at an atom `t'` in another class of `w`. Shape that
  monotonicity alone does not exclude: `a = x_u ∨ (¬h ∧ x_t)`, `b = x_{u'}` with `u' ∈ S_v ∩ S_w` heavy.

Until this is closed, "per-set rank proved" for BottomPay should read "proved up to the top exclusion (tested)".

## 6. The exact smallest obstacle

> **Class point lemma for two sets.** `S, T` with `|S ∩ T| ≤ 1`, partitions `π_S, π_T`, leaves = sets inside one
> class of each, operations `∪, ∩, ∖`. If `S` and `T` are lines there are at least `|π_S| + |π_T| − 2` lines.

* It is the point lemma for two sets when the classes are singletons (open; rule R2, seat O1), and it is PHC@0
  for two sets when the leaves come from a program (Corollary F). It is proved here for `|R| ≤ 2` lines and, by
  the per-set run, whenever one of the partitions is trivial.
* Its content beyond the per-set run is one sentence: *a line that joins two classes of `S` and two classes of `T`
  at once is followed by a line that joins nothing*. Peeling shows this cannot be decided at the line itself; the
  7-line program shows the paying lines can be differences far from it.
* One NOT gate: the same statement at `1_Q` with `∪`-payers, where a difference can only remove the heavy class.
  Before it: the top exclusion of section 5.

Which property supplies the inequality is still unknown. The data of section 3 says where to look: a proof may
assume a tight deletion set, and there every block is private to one set. Rule R2 (the gate-elimination route to
the point lemma) is refuted above base (O1, same day), so the induction that remains for two sets is the one of
Corollary F: free a line, keep the count.

## 6b. The class point lemma on small systems (exact, tested)

`F1_class_point.py`: exhaustive search over all sets of line values, leaves = every set inside one class of each
partition. For 120 two-set systems (classes of sizes from `[1,1]` to `[2,1,1,1]`, `[2,2,1]`, `[3,1,1]`, disjoint and
with a common point in every class position, at most 9 points) there is **no** program with
`|π_S| + |π_T| − 3` lines (`K ≤ 4`). So the class point lemma is not refuted by letting leaves split a class.

## 7. Reproduce

```
nice python3 -I one-not/research/open/F1_phc_tight.py dd --maxn 9          # BottomPay instances, every state
nice python3 -I one-not/research/open/F1_phc_tight.py dd --nostored --gen 60
nice python3 -I one-not/research/open/F1_phc_tight.py prog 4 4 d 6 20000   # point programs, exhaustive at base
nice python3 -I one-not/research/open/F1_phc_tight.py prog 3 3 s 5 20000   # peeling fails, slack 1
nice python3 -I one-not/research/open/F1_phc_tight.py lemmaD               # Lemma D on random instances
nice python3 -I one-not/research/open/F1_class_point.py                    # class point lemma, 120 systems
cd one-not/lean && lake build PEqualNP.W951.Open.PHC
```
