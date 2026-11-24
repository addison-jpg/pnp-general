# research-desktop: lemma candidate D1 (D at every I1 point) — REFUTED as stated; per-atom D at top_w PROVED

Lean: `951/lean/PEqualNP/W951/CanonD1.lean` (new; imports CanonOneNot, CanonClass, Lift, LiftHelpers, Cases). No sorry.

## 1. Precise statement (Lean names)

Circuit `gates` on `n` inputs, one NOT gate at position `p` (`hp hg hU hN` as in CanonOneNot), lift `C = lift n p gates`
on `n+1` inputs (`y = Fin.last n`). NOT value at x is `val gates x (n+p) = ¬h(x)`.

* `K1Z gates p R Z` = real wires of the OR gates of `C` with `C(g)(Z,1) = 0` and `C(g)(e_u,1) = 1` for two `u ∈ R` or more.
  `K1Z gates p R (Zof R) = K1 gates p R` (`K1Z_top`, rfl).
* `K0of gates p R' m`, `m : Fin n → Finset (Fin n)` = OR gates with `C(g)(top_v,0) = 0` and `C(g)(m_{u'} + e_{u'}, 0) = 1`
  for two `u' ∈ R'` or more (per-atom bases; `K0of … (fun _ => m) = K0 … m`, `K0of_const`).

**D1 (`D1Stmt`).** For every such circuit with outputs computing `OR_R`, `OR_R'`, `|R ∩ R'| ≤ 1`; every I1 point `Z` of
`w` (`Z` false on `R`, `h(Z) = 0`, and `h(Z + e_c) = 1` for every `c ∉ R` with `Z c = 0`; equivalently `Z = top_w \ T`,
`T` a minimal transversal of `Min_w`); every I0 choice `m` of `v` (`m_{u'}` a minterm of `h`, `m_{u'} ∩ R' ⊆ {u'}`) with
all `m_{u'} ∩ R = ∅`: `Disjoint (K1Z gates p R Z) (K0of gates p R' m)`.

## 2. Result: D1 is FALSE (`not_D1Stmt : ¬ D1Stmt`, proved in Lean)

Counterexample (`ceGates`), n = 5, S_w = {0,1}, S_v = {2,3}, h = x_4:

    y = ¬x_4;  P = (y ∧ x_0) ∨ (x_4 ∧ x_2);  Q = (y ∧ x_1) ∨ (x_4 ∧ x_3);  g = P ∨ Q;  outputs x_0 ∨ x_1, x_2 ∨ x_3.

Min(h) = {{4}}, Min_w = {{4}}, T = {4}, Z = top_w \ {4} = {2,3} (h(Z) = 0, maximal); I0 choice m_2 = m_3 = {4}, avoiding
S_w. World 1 at Z: P(Z,1) = Q(Z,1) = 0, P(e_0,1) = Q(e_1,1) = 1, so g ∈ K_1(w; Z). World 0 at top_v = {0,1,4}: P = Q = 0
(x_2 = x_3 = 0), P({4,2},0) = Q({4,3},0) = 1, so g ∈ K_0(v; m). g is also a MERGE in both runs of Lemma M (the
outputs come last, so 0,1 and 2,3 are not yet merged): `python3 951/tools/kill_tests/typeA.py <dir> 10` on this circuit
reports `(iii) I1(w)-I0(v) Z=top_w:False all m_v avoid S_w:True COLLIDE 1`. So D1 also fails for merge sets.
The circuit is correct and (1,1)-disjoint but NOT gate-minimal: g, P, Q and their AND gates feed no output (junk).

## 3. Exactly where Z ≠ top_w breaks D's argument

D at top_w (`disjoint_K0_K1`, and the per-atom version `disjoint_K0of_K1` below) is `orClz_disjoint` with first system the
world-0 atoms `(m_{u'} + e_{u'}, 0)` and second zero point `(top_w, 1)`: an atom lies below `(top_w,1)` iff
`(m_{u'} ∪ {u'}) ∩ S_w = ∅`; with `m_{u'} ∩ S_w = ∅` this fails for at most one u' (the point of S_v ∩ S_w).

At `Z = top_w \ T` the atom lies below `(Z,1)` iff `(m_{u'} ∪ {u'}) ∩ (S_w ∪ T) = ∅`. But `m_{u'}` is a minterm avoiding
S_w, i.e. `m_{u'} ∈ Min_w`, and T is a transversal of Min_w, so **T meets every m_{u'}**: NO atom is below (Z,1).
Circuit-free form (`atom0_not_le_Z`): `h(Z) = 0`, `h(m) = 1` ⇒ `m ⊄ Z` (h monotone). The other orientation never works
either: a world-1 atom has y = 1 and is not below any `(Z', 0)` (`atom1_not_le_ext_false`). Hence (`D_hyp_fails`) the
D hypothesis is false for every I1 point when |S_v| ≥ 2 — the failure is total, not a corner case; the remaining
information (two monotone tables, different zero points, different y) is satisfiable by a single junk OR gate, which
is the counterexample. No extra hypothesis of the kind suggested (minimality of T, h(Z) = 0) helps: both hold in the
counterexample; h(Z) = 0 is precisely what kills the argument.

## 4. What is proved (positive)

* `disjoint_K0of_K1`: **D at top_w with per-atom I0 choices**: `|S_v ∩ S_w| ≤ 1`, every `m_{u'} ∩ S_w = ∅` ⇒
  `K_0(v; (m_{u'})) ∩ K_1(w) = ∅`. (CanonOneNot's `disjoint_K0_K1` assumes one common m.)
* `disjoint_K0of_K1Z_of_le`: D at an arbitrary Z, under the hypothesis "of any two distinct u, u' ∈ S_v, m_u ∪ {u} ⊆ Z or
  m_{u'} ∪ {u'} ⊆ Z" (vacuous for I1 points by §3; kept as the exact form of D's argument).

## 5. What remains / consequences

* The corpus pattern "0 collisions in 3,331 pairs with Z ≠ top_w and all m avoiding" is a property of the corpus
  circuits (essentially no such junk), not a monotonicity fact. Any true D1 must use gate-minimality (or that g lies
  on a path to an output) — e.g. as a statement about a minimal counterexample (`MinCE`). Open; not attempted here.
* So collision type (iii) does NOT reduce to the forced condition of (ii) by a D-type argument.
