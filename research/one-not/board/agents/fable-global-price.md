# The global price inequality: what is false, what is proved, what is open (Fable, 2026-11-24)

Owner of this note: the Fable on "the global count" (wall of that name in BOARD.md). Scope: the
GENERAL k-gate statement. The two-gate configuration cxT2 and the case k = 3 belong to another
session and appear here only as test cases. Status words as in BIGPICTURE.md. Nothing here proves
L-meta-951.

## 0. Summary

1. **FALSE: the price inequality for REAL merge sets** `sum_w min_z pi(M_z(w)) <= pi(U)`, for
   general correct one-NOT circuits. Own 14-gate witness STAR4b (section 2), independent of the
   other session's 47-gate STAR4; both give `t* = 1.5`, and even the 0/1 price `pi = 1_U` fails
   (`|U| = 2 < base = 3`). So MergeSDR, MergeFrac, MergePrice and "MU over real merge sets" are false
   without minimality. The target is the LIFTED form (section 1).
2. **PROVED (all prices, all correct one-NOT circuits, no minimality, Berge cycles of any parity
   allowed): Theorem G.** If the U-GAME on the lifted outputs is won, then LiftSDR holds, hence the
   lifted price inequality for every price and `base <= #gates - 1`. With explicit pure-world forms G0
   and G1 and corollaries (all points heavy; `h(not ∪S) = 1`; all sets type B; both staircases; cyclic
   tournaments such as the STAR4 family).
3. **PROVED: the U-game is the exact reach of every argument that looks only at gate VALUES at the
   test points (Proposition S), and for DD-normal outputs with all `|S_w| >= 3` a winning selection
   never mixes worlds (Theorem D).** So after Theorem G, what is left is precisely the DD-type families
   on which the U-game is lost, and there a proof must use the first-merge structure of the union-find
   run (Lemma T).
4. **PROVED: Lemma T (one colouring per gate and frame).** It is the only parity statement there is:
   it forbids odd cycles of 2-point traces and says nothing about even Berge cycles (explicit example).
   A general k-gate proof cannot be a parity argument alone.
5. **OPEN, smallest obstruction:** two sets, no Berge cycle at all: `S = {0,1,2}, {0,3,4}`,
   `h = x1 ∨ x3`, DD-normal outputs (n = 5, base 4). There the lifted price inequality is equivalent
   to "some class of the first set is disjoint from some class of the second", and a violation needs
   3 gates (k = 3). Tested only (section 7).

## 1. Exact definitions and the statement

Circuit: AND / OR gates of fan-in 2 and exactly one NOT gate (position `p`), whose input wire
computes `h` (monotone, since the prefix is AND / OR). `nu = not h`. Sets `S_w ⊆ {0..n-1}`,
`|S_w| >= 2`, `|S_w ∩ S_w'| <= 1`; `s_w = OR(S_w)`; `d_w = |S_w| - 1`; `base = sum_w d_w`;
`top_w = complement of S_w`. A point `u` is heavy if `h(e_u) = 1`, light otherwise.

**Lift** (Lean `Lift.lift`): the NOT gate is replaced by a new input `y`. The lift `M` is a
monotone circuit on `(x, y) ∈ {0,1}^(n+1)`; the real value of a wire at `x` is its lifted value at
`(x, nu(x))` (Lean `val_lift`). `O_w` = lifted output of `S_w`.

(F1) `O_w(x, nu(x)) = s_w(x)`. Hence, by monotonicity in `y`: `O_w(x, 1) >= s_w(x)` with equality
when `h(x) = 0`, and `O_w(x, 0) <= s_w(x)` with equality when `h(x) = 1`.

**Lifted test system** for `w` (Lean `LTS`, `LTSValid`): a zero point `zeta` and one atom `q_c` per
`c ∈ S_w`, points of `{0,1}^(n+1)`, with `O_w(zeta) = 0`, `O_w(q_c) = 1`, and no coordinate that is
false at `zeta` true at two atoms. Atoms need not lie above `zeta` and need not contain `c`.
**Class** `cls_w(t)` (Lean `ltsCls`, `runMT`): run through the lifted gates in order with a
partition of `S_w` (initially singletons); a wire `G` with `G(zeta) = 0` has trace
`tr(G) = {c : G(q_c) = 1}`; if the trace meets at least two blocks, `G` is a merge and those blocks
are united. (M') Every valid class has exactly `d_w` gates (Lean `card_ltsCls`, `runMT_card_le`).
`U_L` = union of all valid classes of all sets (Lean `liftMenu`).

**LIFTED PRICE INEQUALITY (LP).** For every `pi >= 0` on the lifted gates:
`sum_w min_{t valid for w} pi(cls_w(t)) <= pi(U_L)`.

**k-GATE FORM W(K).** For a gate set `K`, `m_w(K) = min_t |cls_w(t) ∩ K|`:
`sum_w m_w(K) <= |K|`.

**Proposition 1.** (a) LP holds iff there are distributions `lambda_w` on the valid systems of `w`
with every gate's load `sum_w lambda_w{t : G ∈ cls_w(t)} <= 1` (finite LP duality; Lean has the
same duality for real merge sets, `MergeDual.lean`). (b) LP implies W(K) for every K (`pi = 1_K`).
(c) W(U_L) is MUL: `sum_w m_w(U_L) = sum_w d_w` by (M'). So the lower bound needs only the ONE 0/1
price `1_{U_L}`; "0/1 prices do not suffice" (DEAD_ENDS) concerns LP, not the bound. (d) LiftSDR
(pairwise disjoint valid classes) implies LP: put `lambda_w` on the chosen system.

**Proposition 2 (minimal violator).** If W(K) fails and W(K') holds for every proper subset `K'`,
then every `G ∈ K` is CRITICAL for at least two sets, where critical for `w` means
`m_w(K \ G) = m_w(K) - 1`, that is: every system of `w` minimising `|cls ∩ (K \ G)|` has `G` in its
class. Proof: `sum_w m_w(K) >= |K| + 1`, `sum_w m_w(K \ G) <= |K| - 1`, and each term drops by 0
or 1. ∎ (2G-LIFT is the case `|K| = 2`.)

## 2. The real-merge form is false: STAR4b

`research/one-not/data/witnesses/star4b_threshold.json`: n = 4, sets `{0,1}, {0,2}, {0,3}`,
`h = MAJ(x1, x2, x3)`, 14 gates, correct on all 16 inputs. With `t = x1 + x2 + x3`:

- gate 13: `G = ((N ∧ (x1 ∨ x2 ∨ x3)) ∨ x1 x2 x3) ∨ x0`. For `x0 = 0` its real value is
  `0, 1, 0, 1` at `t = 0, 1, 2, 3` (threshold crossing: `h` flips between `t = 1` and `t = 2`).
- gate 14: `G' = h ∨ x0` (real value `0, 0, 1, 1`).

For the set `{0, u}` and a zero point `z ⊆ {1,2,3} \ {u}`: if `|z|` is even, `G(z) = 0`,
`G(z + e_0) = G(z + e_u) = 1`, and no earlier wire has both `0` and `u` in its trace, so
`M_z = {13}`; if `|z| = 1`, `G(z) = 1` and `M_z = {14}`. The outputs come later and are never
merges. So the union of ALL real merge sets is `{13, 14}`: `2 < base = 3`.

Command: `python3 -I research/one-not/tools/kill_tests/global_price.py research/one-not/data/witnesses/star4b_threshold.json --menus real --v`
gives `VIOLATION ... "U": 2, "tstar": 1.5, "price": {"13": 0.5, "14": 0.5}`; with
`--menus world,ext` (lifted sub-menu) `tstar = 0.333`. Not a 951 counterexample (14 gates, base 3).
Consistent with 2G-LIFT: condition C(b) fails for this triple (`h(X_j) = 1` and all units light).

## 3. Theorem U, normal form, Theorem G

**Theorem U** (Lean `runMT_disjoint_of_le`; `disjoint_gp` for GP systems). Let `t = (zeta, q)` be a
system for `w` and `t' = (zeta', q')` one for `w'`, in any monotone circuit. If at most one atom of
`t` is not `<= zeta'` (write `t -> t'`), then `cls_w(t) ∩ cls_w'(t') = ∅`.
Proof. A merge `G` of `t` has two trace points `c != c'` (in different blocks), `G(q_c) = G(q_c') = 1`.
One of the two atoms is `<= zeta'`, so `G(zeta') = 1` by monotonicity, and `G` is not processed in
the run of `t'`. ∎

**Lemma N (normal form).** Let `t` be valid for `w`, `zeta <= zeta^` with `O_w(zeta^) = 0`, and
`q^_c <= q_c` with `O_w(q^_c) = 1`. Then `t^ = (zeta^, q^)` is valid, and every certificate
`t -> t'` or `t' -> t` remains a certificate for `t^`.
Proof. The coordinates false at `zeta^` are false at `zeta`, and the atoms shrank: validity.
`q^_c <= q_c <= zeta'` and `q'_c <= zeta <= zeta^`: certificates. ∎
So in the game below only maximal zero points and minimal one-points (prime implicants) of `O_w`
matter.

**The U-GAME** on monotone functions `O_w` on `{0,1}^(n+1)`: every set chooses a valid system;
the game is WON if every pair `{w, w'}` has `t_w -> t_w'` or `t_w' -> t_w`. It depends on the
circuit only through the lifted output FUNCTIONS.

**Theorem G.** For every correct one-NOT circuit: if the U-game on its lifted outputs is won, then
LiftSDR holds; hence LP for every price, W(K) for every K, MUL, and `base <= #gates - 1`
(Lean `bound_of_liftSDR`). No hypothesis on Berge cycles, on minimality or on junk gates.
Proof. Theorem U for each pair, then Proposition 1(d). ∎

**Proposition S (sharpness).** If neither `t -> t'` nor `t' -> t`, there is a monotone function `F`
on the lifted cube with `F(zeta) = F(zeta') = 0` that is 1 at two atoms of `t` and at two atoms of
`t'`. So a gate with these values is not excluded by its values at the two test systems.
Proof. Take atoms `q_1, q_2` of `t` not `<= zeta'` and atoms `q'_1, q'_2` of `t'` not `<= zeta`,
and let `F` be the OR of the four monomials. `F(zeta') = 0`: `q_i` is not below `zeta'` by choice,
`q'_j` is not below `zeta'` because `O_w'(q'_j) = 1 > O_w'(zeta')`. Symmetric for `zeta`. ∎
Consequence: beyond the U-game a proof must use that a merge is the FIRST wire joining two blocks
(Lemma T, section 5); values of the shared gate alone cannot do it.

### Pure-world forms (valid in every correct circuit, by (F1))

**G1 (world 1).** Each `w` chooses `Z_w ⊆ top_w` with `h(Z_w) = 0`. System: zero `(Z_w, 1)`, atoms
`(e_u, 1)`, `u ∈ S_w`. Valid: `O_w(Z_w, 1) = s_w(Z_w) = 0`; `O_w(e_u, 1) >= 1`; outside the zero
point atom `u` has only coordinate `u`. Certificate `w -> w'` iff `|S_w \ Z_w'| <= 1`.

**G0 (world 0).** Each `w` chooses `A_u` for `u ∈ S_w` with `h(A_u) = 1` and `A_u ∩ S_w = {u}`.
System: zero `(top_w, 0)`, atoms `(A_u, 0)`. Valid: `O_w(top_w, 0) <= s_w(top_w) = 0`;
`O_w(A_u, 0) = s_w(A_u) = 1` because `h(A_u) = 1`; outside the zero point atom `u` has only `u`.
Certificate `w -> w'` iff at most one `A_u` meets `S_w'`.

**Corollaries of Theorem G** (each: LiftSDR, all prices, any family, Berge cycles of any length):

- (a) every point of every set is heavy: G0 with `A_u = {u}` (only a common point meets `S_w'`);
- (b) `h(not ∪S) = 1`: G0 with `A_u = {u} ∪ not ∪S`;
- (c) every set is type B (`h(top_w) = 0`): G1 with `Z_w = top_w` (`S_w \ top_w' = S_w ∩ S_w'`);
- (d) world-1 staircase: an order `w_1, ..., w_m` with `h((∪_{i<j} S_i) \ S_j) = 0` for all `j`:
  G1 with `Z_j` that set; for `i < j`, `S_i \ Z_j = S_i ∩ S_j`;
- (e) world-0 staircase: an order with `h({u} ∪ not ∪_{j>=i} S_j) = 1` for all `i`, `u ∈ S_i`:
  G0 with `A_u` that set; for `j > i`, `A_u ∩ S_j ⊆ {u}`;
- (f) a certificate relation need not be an order: the STAR4 family (`{0,j}`, `h = MAJ`) wins G0
  with the CYCLIC tournament `1 -> 2 -> 3 -> 1` (atoms `{j, k}` avoiding `{0, j'}`), and wins G1.

(d), (e) are the lifted versions of the other session's L3 STAIRCASE; because lifted atoms need not
lie above the zero point, Berge-acyclicity is not needed here, only the condition on `h` along the
order. (Not compared line by line with their statement, which I have not seen in the repository.)

## 4. Theorem D: with DD outputs a winning selection never mixes worlds

`w` is **DD-normal** if `O_w(x, 0) = s_w ∧ h` and `O_w(x, 1) = s_w ∨ h` (the extreme case of (F1)).
For every `(sets, h)` a correct circuit with all sets DD-normal exists:
`o_w = ((s_w ∨ h) ∧ N) ∨ (s_w ∧ h)` (`dd_circuit` in `lift_obstruction.py`).
For DD-normal `w`: `(A, 0)` is a one-point iff `h(A) = 1` and `A ∩ S_w != ∅` (type 0); `(A, 1)` is
a one-point iff `A ∩ S_w != ∅` or `h(A) = 1` (type 1); `(Z, 0)` is a zero iff `h(Z) = 0` or
`Z ∩ S_w = ∅`; `(Z, 1)` is a zero iff `h(Z) = 0` and `Z ∩ S_w = ∅`.

**Theorem D.** Let all sets be DD-normal with `|S_w| >= 3`. Take any winning selection of the
U-game, `P` = sets whose zero point has `y = 0`, `Q` = those with `y = 1`.
(i) If `P = ∅`, the sets `Z_w` (x-parts of the zero points) win G1.
(ii) If `P != ∅`, then `|Q| <= 1`, no certificate goes from `P` to `Q`, and replacing the zero
point of the set in `Q` by `(top, 0)` gives a winning selection with ALL zero points in world 0.
(iii) In particular a pure world-0 set (zero `y = 0`) and a pure world-1 set (zero `y = 1`, at
least `|S| - 1` atoms with `y = 1`) are never certified against each other.
So: the U-game is won iff G1 is won or the U-game is won with every zero point in world 0.

Proof. Atoms below a zero `(Z', 0)` have `y = 0`: type 0. An atom `(A, 0)` below a zero `(Z', 1)`
would have `h(A) = 1 <= h(Z') = 0`; so atoms below `(Z', 1)` are type 1 with `h(A) = 0`, hence
`A ∩ S_w != ∅`. A certificate `w -> w'` needs at least `|S_w| - 1 >= 2` atoms of `w` of the type of
the zero of `w'`.
(i) All zeros are `(Z_w, 1)`, `h(Z_w) = 0`, `Z_w ∩ S_w = ∅`. If `w -> w'`, at least `|S_w| - 1`
atoms `(A, 1)` have `A ⊆ Z_w'` and meet `S_w`. Atoms are pairwise disjoint outside `(Z_w, 1)` and
`S_w` lies outside `Z_w`, so these atoms contain distinct points of `S_w`, all in `Z_w'`:
`|S_w \ Z_w'| <= 1`, the G1 certificate.
(ii) For `w ∈ P`, `y` is false at the zero, so at most one atom has `y = 1`; `w` cannot issue a
certificate to a set of `Q` (needs two type-1 atoms). So each pair `w ∈ P`, `w' ∈ Q` is certified
`w' -> w`, which needs `|S_w'| - 1` atoms of `w'` with `y = 0`; so every set of `Q` has at most one
type-1 atom, and two sets of `Q` cannot be certified against each other: `|Q| <= 1`. The set
`w* ∈ Q` receives no certificate, `(top_{w*}, 0)` is a zero of `O_{w*}`, it lies above the x-part of
the old zero, and at most one atom of `w*` has `y = 1`: the system stays valid and its outgoing
certificates are unchanged.
(iii) is the first paragraph. ∎

Remarks. For `|S_w| = 2` hybrid systems exist (one atom of each type) and the dichotomy fails: at
n = 4, 24 of 9,794 pairs `(sets, h)` win the U-game but neither G0 nor G1 (all contain a 2-set).
G0 as stated in section 3 is narrower than "all zero points in world 0" (a set that receives no
certificate may use a zero `(Z, 0)` with `h(Z) = 0` meeting `S_w`); on all 113,685 pairs at n = 5
the two coincide (tested, not proved).

## 5. Lemma T: the only parity statement, and why it cannot be the whole k-gate proof

A **frame** for a family `F` of sets: a point `zeta` and one atom `q_p` for every point `p` of
`∪F`, no coordinate false at `zeta` true at two atoms, with `O_w(zeta) = 0`, `O_w(q_p) = 1`
(`p ∈ S_w`, `w ∈ F`). It restricts to a valid system of every `w ∈ F`.

**Lemma T.** Fix a frame and a wire `G` with `G(zeta) = 0`; `tr(G) = {p : G(q_p) = 1}`.
(T0) During the run of any `w ∈ F`, after a wire is processed its trace on `S_w` lies in one block.
(T1) If `G ∈ cls_w`, then `G = a ∨ c` is an OR gate with `a(zeta) = c(zeta) = 0`, and
`S_w ∩ tr(a)`, `S_w ∩ tr(c)` are nonempty and DISJOINT (they lie in different blocks).
(T2) Hence for `F_G = {w ∈ F : G ∈ cls_w}` the ONE colouring `p -> (p ∈ tr(a), p ∈ tr(c))` splits
`S_w ∩ tr(G)` into two nonempty colour classes for every `w ∈ F_G` simultaneously.
Proof. (T0): inputs: a coordinate false at `zeta` is true at one atom at most. AND gate `a ∧ c`
that is 0 at `zeta`: one input, say `a`, is 0 at `zeta`, and `tr(a ∧ c) ⊆ tr(a)`. OR gate 0 at
`zeta`: both inputs are, `tr = tr(a) ∪ tr(c)`, and after the (possible) merge all of it is in one
block. (T1): an AND gate never merges by the above; for an OR gate the two input traces lie in one
block each by (T0), and the gate merges iff both are nonempty and the blocks differ. (T2) from
(T1). ∎ (Real form: `cover_colour.py`, P1, 0 failures in 12,996 merges on 88 corpus circuits.)

**Corollary (odd cycles).** If the traces `S_w ∩ tr(G)`, `w ∈ F_G`, are 2-point sets that form an
odd cycle, contradiction. This is the last step of 2G-LIFT (triangle).

**It says nothing about even cycles, or about larger traces.** Sets `{1,2}, {2,3}, {3,4}, {4,1}`,
frame `zeta = 0`, `q_p = e_p`: the gate `(x1 ∨ x3) ∨ (x2 ∨ x4)` is the merge of all four sets at
once. More generally a single gate can serve at one frame every family whose traces have property B.
And (T0)/(T1) do NOT give "the gates of `cls_w` separate every pair of points of `S_w` by the
colouring" (the block of `p` at the merge need not contain `p` in the input trace), so there is no
`2^k`-colouring bound from k gates. A general k-gate proof therefore needs a second mechanism for
even Berge cycles; the pigeonhole of 2G-LIFT (ceilings against base merges) is specific to k = 2.

## 6. Where the open part sits

By Theorem G, Proposition S and Theorem D the open part of LP is exactly:

> **(X)** correct one-NOT circuits whose lifted outputs lose the U-game. For DD-normal outputs with
> `|S_w| >= 3` this is: G1 lost and no all-world-0 selection, a condition on `(sets, h)` alone.

It is not about Berge cycles as such. **Smallest instance** (exhaustive over all non-constant
monotone `h` at n = 5 and all families of sets of size >= 3): two sets through one point,

    S = {0,1,2}, {0,3,4},   h = x1 ∨ x3      (one private heavy point and one private light point each)

(G1: `Z_w ⊆ {4}` leaves two points of `S_w'` outside. World 0: the atoms of `{0,1,2}` are `{1}`,
`{0,1}`, `{0,3}`, `{2,1}`, `{2,3}`; two with disjoint traces on `S_w` that avoid `{0,3,4}` do not
exist.) 673 of the 7,579 non-constant monotone `h` at n = 5 lose for this family.

For two sets with `d = 2` each, LP is equivalent to "some class of `w` is disjoint from some class
of `w'`": if all pairs of classes meet, the families of 2-sets are cross-intersecting, so either one
gate is in every class of both sets, or all classes lie in a triangle `{G1, G2, G3}` (MUL fails,
3 < 4), or `A = {gx, gy}`, `B ⊆ {xy} ∪ {g·}` (price `g: 1, x: 1/2, y: 1/2` gives `5/2 > 2`). The
first case is excluded for real systems by the L-avoid argument; the other two are 3-gate
configurations (k = 3, the other session's case). I did not exclude them.

What a proof of (X) must use, by sections 3 to 5: (1) a class has exactly `d_w` gates (M') and is a
first-merge tree (T0, T1); (2) a mechanism for cross-world pairs (one set with world-0 atoms, one
with world-1 atoms), since no value argument exists there (Prop. S); (3) not only parity.

## 7. Tests (commands from the repository root; scipy 1.18.1, HiGHS)

| Test | Command | Result |
|---|---|---|
| real form fails | `python3 -I research/one-not/tools/kill_tests/global_price.py research/one-not/data/witnesses --menus real --v` | `t* = 1.5` on star4 and star4b; `<= 1` on the other 11 |
| Theorem G kill test + LP, corpus | `python3 -I research/one-not/tools/kill_tests/lift_price.py one-not --lp --nmax 9 --umax 7` | 78 circuits (all one-NOT (1,1)-disjoint circuits in `research/one-not/**.json(l)` with n <= 9, barrier suite, cxT2, pappus_junk_gain, star4 included): G1 won 21, G0 won 17, U-game on actual outputs won 51 of 55 run (n <= 7); every winning selection valid, classes of size `d_w`, pairwise disjoint (89 of 89 checks ok); lifted LP `t* <= 1` on 78 of 78 (sub-menu norm + world + ext); real `t* > 1` on 2 |
| same, random junk circuits | `python3 -I research/one-not/tools/kill_tests/gen_lift.py SEED 2000 6`, SEED = 11..14, and `1 300 6` | 8,300 circuits: U-game won on 7,433 of 7,433 run (n <= 6), 7,433 checks ok; G1 7,106 and G0 749 checks ok; lifted `t* <= 1` on 8,300 of 8,300; real `t* > 1` on 0 |
| Theorem D + smallest obstruction | `python3 -I research/one-not/tools/kill_tests/lift_obstruction.py 5 --minsize 3 --maxsets 2 --lp` | 113,685 pairs `(sets, h)`: U-game won 103,590 = pure game won 103,590 (0 disagreements); lost 10,095; on the plain DD-normal circuit of every lost pair the lifted LP has `t* <= 1` (10,095 of 10,095) |
| n = 4, all families | `python3 -I research/one-not/tools/kill_tests/lift_obstruction.py 4 --lp` | 9,794 pairs, U-game won on all; pure games won 9,770 (24 hybrid, all with a 2-set) |
| Lemma T, real form | `python3 -I research/one-not/tools/kill_tests/cover_colour.py one-not --nmax 9` | 88 circuits, 12,996 merges, 0 failures |

Limits of the tests: the corpus in the repository is small (the 75k corpus of the board is not in
it); the LP uses a sub-menu of `liftMenu`, so `t* <= 1` is a certificate but a `t* > 1` would not
be a refutation; on (X) only the plain DD circuit and a few hand-made junk variants (2 sets,
`h = x1 ∨ x3`, selector and cross junk gates first: `t*` between 0.4 and 0.67) were tried, which is
not an attack.

## 8. Scripts

`research/one-not/tools/kill_tests/`: `lift_price.py` (pure games, U-game on actual outputs, kill test of
Theorem G, lifted LP), `ugame.py` (exact U-game solver in normal form), `lift_obstruction.py`
(enumeration of `(sets, h)`, Theorem D cross-check, DD-normal circuit), `gen_lift.py` (random junk
circuits). Reused from the stopped agent after checking: `global_price.py` (`Lift`, `run`, `valid`,
`lp_load`; its real-menu LP is what exhibits the failure on STAR4), `cover_colour.py`. Its
`gen_price.py` tests the real form only, which is now known false.
