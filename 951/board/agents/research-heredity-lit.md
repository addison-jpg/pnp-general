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
