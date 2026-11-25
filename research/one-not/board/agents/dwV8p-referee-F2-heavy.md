# Referee: front A2's F2-step lemmas F1 and F2-desc (coord 12:54) — both CORRECT

Referee session_01GmnDhdwV8pW4adQkj9Ei3M (dwV8p). Test: `research/one-not/work/notes951/lemmaK_referee/f2heavy.py` (own code, imports
research/one-not/tools/w951; random correct one-NOT circuits, n = 4-6, random Q; seeds 31-34, 4 x 100,000 draws).

- (F1) v heavy (h(Q + e_v) = 1) => every g in F2(Q ∪ v) has real g(Q + e_v) = 0. CORRECT. On the half-cube x >= Q + e_v,
  h = 1 (monotone), so N = 0 and real = C_0 there. A witness Z' ⊇ Q ∪ v has real g(Z') = 0, so real g(Q + e_v) =
  C_0(g)(Q + e_v) <= C_0(g)(Z') = 0 (C_0 monotone). No minimality used. CHECKED: 510,936 (heavy v, g) tests, no failure.
  For LIGHT v it is false, as front says: 21,205 random failures; cxMU_clean2 (Q = ∅, v = 2: light) has gates 31 and 34.
- (F2-desc) CORRECT. A wire with a real separating triple (0 at Z, 1 at Z + e_u and Z + e_u', u != u'):
  - AND gate: a child that is 0 at Z exists, and it is 1 at both atoms because the AND is; descend into it.
  - NOT gate N = ~h: N(Z) = 0 gives h(Z) = 1, so h = 1 above Z and N(Z + e_u) = 0. No separation.
  - input x_k: x_k(Z + e_u) = x_k(Z + e_u') = 1 with x_k(Z) = 0 needs k = u = u'. No separation.
  So the descent ends at an OR gate with the same triple. An output o_w with u != u' in S_w and Z ⊇ Q avoiding S_w is
  separating (and w is alive, since Z ⊇ Q, Z ∩ S_w = ∅), so it yields an F2(Q) gate. A real merge gate of M_Z(w) has the
  triple itself (two units in different components), so it lies in F2(Q) with no descent.
  CHECKED: 8,540,410 separating triples descended to an OR gate; 2,869,580 output triples landed in F2(Q). No failure.
- Note: the descended OR gate need not differ between pairs or sets; F2-desc gives membership, not a count.
