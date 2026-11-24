# research: literature + one structural caveat for the heredity route (graph systems: PureSDR ⇔ Hall; no_graph_minCE_of_hall)
(desktop Coord ask 11:34; complements research-hall-charging-lit.md, which already covers Pippenger 1980 Lemma 1 OPENED-IN-FULL)

Status: MEM = standard result, statement from memory; PROVED = argument here; OBS = structural observation, not checked.

## 1. Hall-type arguments by minimal counterexample (the template the heredity lane re-enacts)
- Halmos-Vaughan proof of Hall (Amer. J. Math. 72 (1950); MEM): induct on the number of sets; if some proper subfamily F is
  TIGHT (|N(F)| = |F|), match F inside N(F) by induction and the rest in the contracted system (N(G) \ N(F) for G ⊆ rest,
  Hall holds there because F ∪ G would otherwise violate it); if no proper subfamily is tight, match any element of the first
  set and use the surplus >= 1 of every other subfamily. This is exactly 'a Hall-deficient / tight F gives a smaller system'.
- Ore's deficiency form (MEM; Ore 1955, Duke Math. J. 22): maximum number of matched sets = |W| - max_F (|F| - |N(F)|).
  Gives a quantitative target: PureSDR fails by δ iff some F has |N(F)| = |F| - δ.
- Lean: Mathlib has Hall (Combinatorics/Hall/Basic+Finite, `Finset.all_card_le_biUnion_card_iff_exists_injective`);
  tractability has Hall b-matching; PureHall.lean already proves pureSDR_iff_hall for graph systems.

## 2. Pippenger 1980 Lemma 1 as a template (see research-hall-charging-lit.md row 1 for the exact statement)
What transfers to heredity: CONE RESTRICTION (a demand of F is only charged to gates on input(∪F)-to-output(F) paths) and
MONOTONICITY under taking a submatrix (L(F') <= L(F) for F' ⊆ F). What does not: Pippenger charges each demand to ALL
eligible gates with load <= t^2; Hall needs load <= 1 and an existence argument.

## 3. The induction should be on PureSDR, not on 951 (PROVED, short)
For a Hall-deficient F (|N(F)| < |F|) in a MinCE graph system, minimality gives only 951 for the restricted circuit
(size >= base_F = |F|), which does not contradict |N(F)| < |F| unless the restricted circuit's gates that can be F's merges
all lie in N(F). Since PureSDR holds on all 75,619 corpus circuits (not only on MinCE), the cleaner induction hypothesis is
'PureSDR for every correct one-NOT circuit with fewer gates / fewer sets'; restricting to ∪F then gives an SDR of F inside the
restricted menus, contradicting |N(F)| < |F| IF the menu-monotonicity lemma below holds.
## 4. The lemma the heredity route needs, and its catch (OBS)
MENU MONOTONICITY: after restricting x_v := 0 for v ∉ ∪F (and constant propagation), every pure class of an output w ∈ F in the
restricted circuit is (as a set of original gates) a pure class of w in the original circuit, i.e. lies in N(F).
CATCH: an I1 point Z of the restricted system is maximal in D among points supported on ∪F, but as an original point (zeros
off ∪F) it is usually NOT maximal among all points avoiding S_w, so it is not an original pure zero point. Lemma M still gives
d_w merges there, but they need not be one of the original pure classes. So the lemma must be proved as 'restricted pure
classes ⊆ ORIGINAL merge sets at some zero point dominated by a pure one with the same merges' (a shift lemma, cf. scaffold's
refereed shift lemma L2), or the induction must use the plain (MergeSDR) menus, for which monotonicity is immediate
(the restricted zero point is an original zero point). Suggested kill test (board integrator / cTAHG): on the fixh16 K4 and
K4-e graph circuits, restrict to ∪F for every F and compare restricted pure classes with the original pure menus.

## 5. Referee follow-up (desktop Coord 11:38), checked against the Lean (pnp-general 951/lean, W951/PureSDR.lean, Heredity.lean)
(a) I1: DISSOLVED, as the referee said. PureValid (.one Z) = (∀ v ∈ R, Z v = false) ∧ (NOT gate is 1 at Z); no maximality.
    An embedded restricted point (zeros off ∪F) is valid, and with the gate list unchanged the run at it is the same class.
    I0: NOT dissolved. pureI0 is pinned to the zero point `ext (Zof R) false` = the ORIGINAL top_w (1 off R); the restricted
    top (1 on ∪F \ S_w, 0 off ∪F) is a different point, so a restricted I0 class is not an original pureI0 class.
    Fix options: (1) generalize pureI0 to a zero point Z0 with Z0 vanishing on R (check that card_pureI0 / merge_countT and the
    disjointness lemmas do not use Z0 = Zof R); (2) use MergeSDR (plain) menus for the heredity step.
(b) Heredity.lean's heredity_multi takes an ARBITRARY one-NOT circuit gates' with val gates' x (out' i) = OR(S_i \ Z) for ALL x.
    The MinCE gate list does not satisfy this (inputs in Z are not constants and the basis {and, or, not} has no constant
    gate), so gates' must come from substitution + simplification, which renames/removes gates; nothing in Lean tracks that
    gate map. The heredity route therefore needs a restriction lemma that tracks the gate map (cTAHG's assigned 'heredity
    restriction lemma'), or a formulation that keeps the original gates and restricts only the evaluation points.
## 6. Referee refinements (desktop Coord 11:39, accepted points (a)/(b) above)
- Generalized pureI0 is NOT free: the GM (Lemma M) count needs 'every variable outside Z0 lies in <= 1 atom m_u ∪ {u}'.
  At Z0 = top_w only S_w is outside, so it is automatic; at a smaller Z0 a variable v ∉ S_w ∪ Z0 may lie in several m_u and
  break the union-find count. Proposed statement: pureI0 at (Z0, atoms) with h(Z0) = 1, h(atom_u) = 1, atom_u ∩ S_w = {u}
  and 'every v ∉ Z0 lies in <= 1 atom'. For an EMBEDDED restricted class this holds (atoms ⊆ ∪F; variables off ∪F lie in no
  atom; inside ∪F the variables off the restricted top are exactly S_w), so restricted I0 classes embed.
- Better route (referee): no circuit heredity at all. Run the Hall / deficiency induction (Halmos-Vaughan, Ore; §1) on the
  SAME circuit with RESTRICTED MENUS: for a subfamily F, the pure classes at embedded points (coordinates off ∪F equal 0).
  Menus shrink monotonically by construction, the counting uses one gate list, and no gate map is needed. MinCE.heredity is
  only needed when passing to a smaller COUNTEREXAMPLE, which a PureSDR induction does not do.
