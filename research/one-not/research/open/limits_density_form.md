# Density form of |F2|, base and slack (seat: density form)

Script: `limits_density_form.py` (run `python3 -I research/one-not/research/open/limits_density_form.py` from the repo root). Checked: tested on the 17 circuits in `research/one-not/data/witnesses` (n <= 14), exact integer equality, no sampling except Q on the two n = 14 circuits (150 random cubes).

## Definitions (Lean: `W951/F2Induct.lean`, `MUInduct.lean`, `ContinuousAttach.lean`)
- n points, sets S_1..S_m, a circuit with gates; wires < n are inputs.
- `baseDQ S ∅ Q = Σ_{w : S_w ∩ Q = ∅} (|S_w| - 1)`.
- `F2 Q` = OR gates g with a witness (R, Z, u, u'): R alive at Q (R ∩ Q = ∅), u ≠ u' in R, Z ∈ {0,1}^n with Z = 0 on R, Z = 1 on Q, g(Z) = 0, g(Z+u) = g(Z+u') = 1.
- `slack Q = |F2 Q| - baseDQ Q`; the circuit statement is slack(∅) >= 0 (gates >= |F2| >= base). `Φ(p) = E_{Q ~ μ_p} slack(Q)`.

## 1. Base: a pure pattern count, exact
Let N_k = number of sets of size k (pattern: one labelled set, k points). Then
base(∅) = Σ_k (k-1) N_k, and for the product measure E_p[base] = Σ_w (|S_w|-1)(1-p)^{|S_w|} = Σ_k (k-1) N_k (1-p)^k. Exact. Normalised: a_k = N_k / n, β = Σ_k (k-1) a_k. The sets need bounded size (or a tail condition on a_k) for the limit to exist. Gates (the count the circuit pays) is a plain gate count, normalised γ = |gates| / n.

## 2. |F2|: exact form, but the witness context Z is NOT a small pattern
Let 𝒵_g = set of all Z occurring in some witness tuple of OR gate g at Q = ∅. Then, exactly (checked on all Q, n <= 9; sampled n = 14):
- g ∈ F2(Q) ⇔ Q ⊆ Z for some Z ∈ 𝒵_g. So F2(Q) = Σ_g 1[Q ∈ D_g] with D_g a down-set (the heredity `F2_mono`), and Φ_F2(p) = Σ_g P_{μ_p}(Q ∈ D_g), exactly equal to the gate-wise union of subcubes (checked at p = 1/3 with Fractions on n <= 9).
- |F2(∅)| = Σ_g 1[𝒵_g ≠ ∅] = #{g : g has a witness}.

The tuple (g, R, u, u', Z) has a point Z of the whole cube in it. The pattern is therefore the cone of g, whose size is unbounded in n. This is not a labelled pattern of fixed size. I tried the obvious fix, Z = 0 (the pattern "g(0) = 0 and g(e_u) = g(e_{u'}) = 1", relations V0(g), E(g,u) that propagate wire by wire, NOT included: V0(¬a) = 1 - V0(a), E(¬a) = {u : a(e_u) = 0}). It is a lower bound only: it misses 7 of 12 gates already in the monotone circuit `c4mono_k3` (an AND gate needs its other input already on, so Z ≠ 0), 21 of 30 in `pasch_mono_k3_210`, 6 of 21 on both twin trees. It is exact only on some tight circuits (fano_formula, pasch_s14, tri_all, see_gap). So: no finite bounded-size pattern sum gives |F2| exactly. Bounded size needs either (a) a structure whose relation Wit(g; R, u, u') = "∃Z" is a primitive of the limit object (the cone is hidden in the relation), or (b) a bounded-depth restriction.

## 3. What IS a pattern sum, with the "exists" as the only non-linear step
Let m_g = number of sets R having a witness at g (some Z, some u ≠ u'). Pattern P1 = (g, R) with a witness, P2 = (g, R, R') two different sets sharing a gate witness. Then, exactly (all 17 circuits): F2 = Σ_g 1[m_g >= 1] (the non-linear step), and
  Σ_g (m_g - C(m_g,2)) = P1 - P2  <=  |F2|  <=  P1 = Σ_g m_g   (Bonferroni, exact integer inequalities, checked).
Normalised by n (π1 = P1/n, π2 = P2/n):
- necessary for slack >= 0:   π1 >= β   (since |F2| <= P1);
- sufficient for slack >= 0:  π1 - π2 >= β.
Both are linear in pattern densities with pattern size: 1 gate + 1 or 2 sets + 2 points each (+ the hidden context Z). On the stored circuits the sufficient form is only useful when tight (fano_formula 14 - 0 >= 14, pasch_s14 8 - 0 >= 8) and fails elsewhere (P2 often > P1: c4mono 31 - 37 < 4, twin trees 47 - 44 = 3 < 15), because gates serve many sets at once. The exact statement needs all orders: write d_j = #{g : m_g = j} / n; then slack(∅) >= 0 ⇔ Σ_{j>=1} d_j >= β, exactly, with Σ j d_j = π1. So the exact linear form is in the degree distribution (d_j) of the gate-set witness graph, not in a fixed pattern size.

## 4. Slack >= 0 as an inequality between densities
Per normalisation by n:  Σ_{j>=1} d_j  >=  Σ_k (k-1) a_k   (exact, no o(n) loss). The one-NOT circuit enters only through which gates have d-degree >= 1; the single NOT gate h shows in 𝒵_g only for gates in the cone above h (h-dependent gates: 1..27 per circuit), and h-dependent gates ARE among the gates the Z = 0 pattern misses. The inequality is exact at every finite n. It becomes asymptotic only when sequences are taken to a limit object: then (a_k), (d_j) are limit densities, and any proof by flag algebras gives gates >= (1 - o(1)) base at best, the exactness needing the stability step of BOARD.md.

## 5. Patterns needed (summary)
- set with k points: size k, exact base. One-NOT irrelevant.
- (gate, set, two points, context Z): the witness. Size unbounded as stated; bounded only with the relation Wit as primitive.
- (gate, set, set') for Bonferroni order 2; order j needs j sets on one gate.
- The NOT gate h and its input wire a: h-dependent gates form one cone; no pattern of its own is needed, but the cone must be a marked substructure (1 marked wire h), since gates not below h are monotone and gates below h are not.
- The p-version (Φ) adds nothing new: E_p slack = Σ_gates P(Q ∈ D_g) - Σ_k (k-1) N_k (1-p)^k.

## 6. Verdict (honest)
The base side is a clean pattern count. The |F2| side is exact as a sum over gates of an "exists a context Z" indicator and is not a bounded-size pattern sum; Z = 0 and Bonferroni truncations give one-sided bounds (necessary π1 >= β, sufficient π1 - π2 >= β) and the Z = 0 local form is a strict lower bound. The seat that attempts a flag-algebra certificate must treat Wit(g; R, u, u') as a primitive relation with its closure rules (heredity in Q, cone of h), which is the hard part, not the sets.
