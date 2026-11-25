# Referee: front A2's h = x_p theorem (coord 13:10) — CORRECT

Referee session_01GmnDhdwV8pW4adQkj9Ei3M (dwV8p). Test: `research/one-not/work/notes951/lemmaK_referee/hxp.py` (own code, imports
research/one-not/tools/w951; lifted M(., y) = C_y; random correct one-NOT circuits n = 4-6; seed 3, 200,000 draws).

Claim: if h = x_p, one lifted class per set (star w ∋ p: zero point (top_w, 1), atoms (e_u, 1), u ∈ S_w \ p, and (e_p, 0);
non-star w': zero point (top_w' \ p, 1), atoms (e_c, 1)) has exactly d_w merges, the classes are pairwise disjoint, and
every merge is in F2(∅); hence |F2(∅)| ≥ base. Relative form: h = x_p on the cube x ⊇ Q gives |F2(Q)| ≥ base(alive at Q).

- Validity: CORRECT. Both zero points have x_p = 0, so h = 0, real = M(·, 1), and o_w = 0 there; C_1(o)(e_u) ≥ real = 1;
  real = C_0 at e_p (h(e_p) = 1), so M(e_p, 0) = 1.
- Exactly d_w merges: CORRECT. y = 1 at ζ, so the y wire is not a zero wire; for non-star classes x_p is a zero wire with
  an empty block (no atom has x_p = 1); the atoms are distinct points of S_w, o_w's block is all of them.
- Disjointness: CORRECT. The text treats "non-star w' vs any w" and "star vs star". Star vs non-star is NOT a separate
  case: showing that no merge of the non-star class is a merge of the star class already makes the two merge sets
  disjoint. Worth one sentence in the write-up, since the direct star-side argument fails (a block {(e_u,1), (e_p,0)}
  with u ∈ S_w ∩ S_w' has no atom below (top_w' \ p, 1)).
- F2: CORRECT. At Z = top_w (resp. top_w' \ p): real g(Z) = M_g(Z, 1) = 0; real g(Z + e_u) = M_g(Z + e_u, 1) ≥ 1 for u ≠ p;
  real g(Z + e_p) = M_g(Z + e_p, 0) ≥ M_g(e_p, 0) = 1.
- Relative form: CORRECT with atoms Q + e_u (resp. (Q + e_p, 0)) and the same zero points (both contain Q; p ∉ Q since h is
  not constant on the cube). The note should state the atoms Q + e_u explicitly.
- CHECKED: 149,445 plain instances (Q = ∅) and 68,234 relative instances. Validity, exactly d_w merges, disjointness,
  merges in F2(Q) and |F2(Q)| ≥ base(alive at Q) held on all of them.
