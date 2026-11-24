# research / Fable K: Sokolov dag-like game form of lifted 951 (restart-safe log)
Code: research scratchpad fableK/ (to be copied to branch `workspace`, tools/research951/fableK/).
Status words: PROVED-PAPER / CHECKED (N cases) / CONJECTURE / REFUTED. Nothing here is in Lean.
Prior art read first: agents/coord-lateral.md (coord Fable D: translation, defect form, h = x_a ∨ x_b), front s_fable.md (S2.1-S2.3).
I do not repeat those; entries below are what is new relative to them.

## 0. Notation
M = lifted monotone circuit over (x,y), contains a y-free wire h. U1 = {h=1}, U0 = {h=0}. d_w = |S_w|-1, base = Σ d_w.
Alice points (p,l) ∈ U_w = {o_w(p)=1, l ∨ h(p) = 1}; Bob points (q,l') ∈ V_w = {o_w(q)=0, l' ∧ h(q) = 0}.

## 1. QUADRANT FORM of the multi-root game (PROVED-PAPER, elementary)
Split the root rectangle U_w × V_w by the levels (l, l') of Alice and Bob:
 (1,0) Alice level 1, Bob level 0: solved by the single leaf y.
 (0,1) Alice (p,0) with h(p)=1, Bob (q,1) with h(q)=0: solved by the single node h (its rectangle is a y-cylinder on both sides).
 (0,0) Alice (p,0), h(p)=1, o_w(p)=1; Bob (q,0), o_w(q)=0 (ALL such q): this is the monotone KW game of the partial
       function  P0_w(h): H_w ∈ [o_w ∧ h, o_w]   ("world 0": never above o_w, exact on U1).
 (1,1) Alice (p,1), o_w(p)=1 (ALL such p); Bob (q,1), o_w(q)=0, h(q)=0: the partial function
       P1_w(h): G_w ∈ [o_w, o_w ∨ h]   ("world 1": never below o_w, exact on U0).
So a lifted circuit is: one dag that contains (i) a node for h, (ii) a game for all P0_w(h), (iii) a game for all P1_w(h),
glued at the roots. Write C0(h), C1(h) for the monotone circuit sizes (Sokolov: = game sizes) of the families
{h} ∪ {P0_w(h)} and {h} ∪ {P1_w(h)} over x only. Then (set y := 0, y := 1 in M):
   s - 1 >= max(C0(h), C1(h)),   and   s - 1 <= C0(h) + C1(h) - size(h) + 2m  (multiplexer F_w = H_w ∨ (y ∧ G_w)).
Inputs used: all weights (the intervals are stated on all of {0,1}^n).
Plan: compute C0, C1 and the lifted optimum for all monotone h on small systems; look for the exact coupling statement.
