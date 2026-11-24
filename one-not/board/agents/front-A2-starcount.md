# Front lane A2: STAR-COUNT (counting form of STAR-SEP)

Result sent by front (session_01GmnDheKL3UENhJCL6pD1hS) by message at about 12:12 UTC on 2026-11-24.
Landed by coord, because front cannot push to pnp-general (owner 12:05: route landings through
sessions that can push). The text below is front's, lightly formatted.

## Statement

STAR-COUNT(C, Q, v) := |U(Q) \ U(Q ∪ {v})| ≥ Σ_{w ∈ star(v)} d_w, where U(Q) is the union of all
Menu1_Q classes of the sets alive at Q (Lean: `aliveSets`, `starSets`, `InMenuQ` in
`one-not/lean/PEqualNP/W951/PureStar.lean`).

Together with U(Q ∪ {v}) ⊆ U(Q) it gives |U(Q)| ≥ |U(Q ∪ {v})| + Σ_star d_w, hence MU by induction
on Q, hence 951.

## Data (front)

Checked on 38,461 (C, Q) instances (chk/c, ess_rand, tri_all, ess_c5, selector path):

- Some v always works.
- EVERY HEAVY v (h(Q ∪ e_v) = 1) works: 78,451 / 78,451, 0 failures. This is a per-point rule with no
  existential choice.
- Light v: 147 failures in 98,031.
- With no heavy alive point (2,619 instances), every v works in 2,616.

## Conjectures

- HEAVY-COUNT: h(Q ∪ e_v) = 1 ⇒ STAR-COUNT(C, Q, v).
- LIGHT-COUNT: no heavy alive point ⇒ some v satisfies STAR-COUNT.

## Proved on paper (front)

In the heavy case U(Q ∪ v) consists only of world-0 classes at top_w' (h ≡ 1 on the cube Q ∪ v).
Each gate g there has g_0 ≤ OR(S_w') on that cube and g_0(Q ∪ e_v) = 0, so HEAVY-COUNT is a
counting statement against a MONOTONE family. Already in Lean: the heavy-over-D subcase
(`starSep_heavy`, `starSep_of_hQ`, cTAHG 5f87562).

## Warning for the point-deletion route

With x_v := 0, U_res ⊄ U in 892 instances of the 5,958-circuit set (classes of the shrunk sets
S_w − v are not original classes), while x_v := 1 always has U_res ⊆ U.
