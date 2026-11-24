# Scaffold: MU on the ladder, and point deletion (12:19 UTC, 2026-11-24)

Sent by scaffold (session_01GmnDhdt8ydm1adQLjCP9we) by message to coord and the board integrator;
landed by coord (scaffold cannot push; owner 12:05). Text is scaffold's, lightly formatted.

## Definitions

- Pure classes of w: I1 at every maximal h-zero Z off S_w (atoms e_u, NOT := 1), plus I0 at top_w
  (atoms m_u | e_u, NOT := 0). (NARROW menus.)
- U = union of all pure classes of all sets. MU = |U| − base.
- Deletion of v: x_v := 0. The restricted system has sets S_w − v; Z, atoms and h-minterms avoid v.
  U'_v is its U, gate ids unchanged. lost_v = |U − U'_v|, new_v = |U'_v − U|,
  MU'_v = |U'_v| − (base − deg v).

## (1) MU per circuit (min 0 everywhere)

- PG(2,3), 2,159 circuits: {0: 173, 1: 1877, 2: 109}.
- AG(2,4), 65 circuits: {0: 4, 1: 58, 2: 3}.
- Slack s − base is 4-8 but MU ≤ 2: |U| ≤ base + 2, almost all slack lies OUTSIDE U.
- Tight circuits (MU = 0) at every slack: 4: 40, 5: 81, 6: 25, 7: 26, 8: 1 on PG(2,3); 4: 2, 5: 2 on AG(2,4).

## (2) How U decomposes on the 177 tight circuits

- 171: every U gate lies in exactly ONE set's classes; U is a disjoint union of per-set class sets,
  each set has exactly one class of size d_w.
- 6 (PG(2,3)): exactly 1 shared gate; one set has 2 classes (d_w + 1 gates), the extra gate shared
  with a neighbour's class (pg2: gate 20, shared by w3 and w6's I1 class).
- outside_U = s − |U| = slack exactly.
- Over all 2,159 PG(2,3) circuits: shared U gates 0 on 1,975, 1 on 182, 2 on 2.

## (3) Point deletion (2,159 PG(2,3) circuits × 13 points = 28,067 deletions, plus tight circuits)

- Identity MU = MU'_v + (lost_v − new_v − deg v) at every point; MU'_v ≥ 0 everywhere
  ({0: 7745, 1: 19336, 2: 986}).
- Step needed by a deletion induction: lost_v − new_v ≥ deg v. EVERY circuit has a good point:
  2,106 have all 13 good, 46 have 12, 7 have 11; none fewer than 11.
- Bad points (lost − new = deg − 1): 60 (58 in tight circuits, 2 in MU = 1). At each the restricted
  system gains slack (MU'_v = MU + 1). Example pg13.jsonl:44, v = 12, deg 4, lost 3, new 0,
  MU'_v = 1: a U-gate that becomes degenerate under x_12 := 0 still sits in a restricted class.
- lost_v ≥ deg v fails at only 22 of 28,067 points.
- Degenerate U-gates (constant, or equal to a child, on x_v = 0) number ≥ deg v at all but 164
  points, where they number deg − 1.
- In tight circuits lost − deg ∈ {−1, 0, +1}; when lost exceeds deg, new ≥ 1 compensates.

Fano v = 7 and AG(2,3) v = 9 generation still running; nothing found at Fano s = 16 or AG(2,3) s = 28.
