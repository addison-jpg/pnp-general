# j_cut_opus: two-world semantic Pippenger cut for one-NOT circuits (lead J)
Tools: w9/jcut/bt.py (bitset truth tables, real/C0/C1), cls2.py (classes), run3..run6.py. Data: 2559 circuits
(cx1-3, cxr, cfgI, fc/*, tw/*, badT 63, bad 160, chk/c 2321), 10621 sets. All verified correct.

## 0. Monotone baseline (PROVED, classical)
Semantic quantities (Jukna Ex 13.13 / Mehlhorn): L(g) = {v : x_v <= g}, K(g) = {w : g <= o_w}. 2-freeness:
|L(g)|>=2 and |K(g)|>=2 impossible (u,v in L, w,w' in K => u,v in S_w ∩ S_w'). In OR-only circuits L grows and K shrinks
along paths, so {g : |L(g)|>=2} ∩ cone(o_w) = D_w are private and the l>=2 subdag under o_w is a fan-in-2 dag with
>= |S_w| distinct single-variable leaves => >= |S_w|-1 gates (edges 2I >= (I-1)+Leaves). This is the EXACT count
(Pippenger counts wires; the gate count needs the per-output tree correction). With AND gates the cut is NOT monotone
along paths; Mehlhorn's 6.7 (c = a ∨ b, weight >= 2 point) removes AND gates. So in the one-NOT case the "cut" must be
replaced by semantic classes in each world.

## 1. Definitions (world classes). U0={h=0} (real = C1 there), U1={h=1} (real = C0 there). w hard iff h(z_{S_w})=1.
For a world (Dom, circuit) and gate g:  L(g) = {u : x_u <= g on Dom, nonvacuously},  "g <= o_w on Dom".
- Dr_w, Pr_w : T3 classes (real, all inputs): Dr = {g <= o_w, |L∩S_w|>=2}, Pr = {g >= o_w, g≢1, g ≱ o_j (j≠w)}.
- D0_w, P0_w (w hard only): same definitions with Dom = U1, circuit C0; P0 privacy only against hard j.
- D1_w : Dom = U0, circuit C1: g <= o_w on U0 and g(e_u)=1 for >= 2 LIGHT u in S_w.
- (P1_w, world-1 private-above, was also tried: it conflicts with everything (P1-D0 749, P1-Dr 652, P1-D1 367
  overlaps) and is NOT needed; dropped.)
Π*_w := Dr_w ∪ Pr_w ∪ D0_w ∪ P0_w ∪ D1_w.

## 2. CHECKED (2559 circuits, 10621 sets)
(C1) Matching: the bipartite matching sets->gates (demand d_w, gate cap 1, edges Π*_w) saturates base in 2559/2559.
     Dropping any one family: Dr+Pr only fails 17, without D0 fails 3 (cx1, cfgI x2), without Dr fails 330,
     without D1 fails 3. So all of Dr, D0, D1 are needed; Pr, P0 can be partly replaced.
(C2) Per-set: |Π*_w| >= d_w for EVERY set (0 short).  No single world suffices: cxT4 (d=5) has
     |Dr∪Pr|<5, |D0∪P0|<5, |D1|<5 but the union >= 5.
(C3) Disjointness: Π*_w ∩ Π*_j = ∅ for all pairs except ONE pair in all data (chk/c.jsonl:1718, unread junk gate
     13 = x3∨x4∨x5, S_2={3,5}, h=x0∨x5, 5 heavy: 13 ∈ D1_0 ∩ Pr_2 ∩ P0_2). That circuit is not live.
(C4) If all units of S_w are light, |D1_w| >= d_w (all rows of the data).

## 3. PROVED: relative Mehlhorn lemma (RM) and the world-1 exact count for easy sets
(RM) Let b be a world (Dom_1 = U0 with C1, Dom_0 = U1 with C0), w a set, and Λ a set of wires with o_w = ∨Λ on Dom
(as functions of C_b). Let G = s∧t ∈ Λ, R = ∨(Λ\{G}). If Dom is closed under a∨b for points a,b ∈ Dom that avoid S_w,
then o_w = R∨s on Dom or o_w = R∨t on Dom.
Proof: else a,b ∈ Dom, o_w(a)=o_w(b)=0, R(a)=R(b)=0, s(a)=1, t(b)=1; c=a∨b ∈ Dom avoids S_w, s(c)=t(c)=1 (C_b monotone),
so o_w(c)=1, contradiction (Mehlhorn 6.7 with a domain). Closure holds: Dom=U1 always (up-set); Dom=U0 iff w EASY
(c <= z_{S_w}, h monotone, h(z_{S_w})=0). The NOT breaks Mehlhorn exactly at crossing joins a,b ∈ U0, a∨b ∈ U1,
which forces w hard.

(E1) THEOREM (PROVED). For an easy set w let L_w = #light units of S_w (h(e_u)=0). Then
   #{OR gates g ∈ D1_w} >= L_w - 1,   D1_w = {g : g <= o_w on U0, g(e_u)=1 for >= 2 light u ∈ S_w}.
Proof. Exploration in C1 on U0: start Λ={o_w}; replace an OR leaf by both inputs, an AND leaf by the input given by RM;
every explored wire is <= o_w on U0; terminal leaves are variables or constant 0 (N=1 and constant 1 impossible since
0 ∈ U0, o_w(0)=0); variable leaves x_v <= o_w on U0 have v ∈ S_w or v heavy; every light u ∈ S_w is a leaf. Put
B(g) = {light u ∈ S_w : g(e_u)=1}; B(OR)=B(a)∪B(b), B(AND G) ⊆ B(chosen child). Let E2 = explored wires with |B|>=2
reachable from o_w through such wires. B(o_w) ⊆ ∪ B(boundary children), boundary children have |B|<=1, so >= L_w
boundary edges; edges out of E2 = 2#OR + #AND >= (|E2|-1) + L_w, hence #OR(E2) >= L_w - 1. ∎
(The fan-in-2 correction: wire count >= L_w + |E2| - 1, gate count follows.)
(E2) PROVED: D1_w ∩ D1_j = ∅ (light unit u ∈ S_w\S_j: g(e_u)=1 > o_j(e_u), e_u ∈ U0). D1_w ∩ Dr_j = ∅.
So: s >= Σ_{w easy} (L_w - 1)^+ + (anything private disjoint from all D1).
(E3) World 0 analogue, hard w: D0'_w = {g <= o_w on U1, g(z_{S_w}+e_u)=1 for >= 2 u ∈ S_w} has >= d_w OR gates (same
proof, atoms z_{S_w}+e_u ∈ U1, RM always valid on U1). PROVED. But D0' is NOT private (it is the R* class; R* refuted).
The private version D0 (g >= x_u on all of U1) is private among hard sets (PROVED) but can be short.
CHECKED (run7.py): RM exploration never fails (7552 hard sets in world 0, 3069 easy sets in world 1); E1, E3 hold on all.

## 4. Where the NOT breaks the cut (exact gap of the pure two-world cut)
Amano–Maruoka edge bookkeeping = our world split: a sensitive edge (z, z+e_u) of o_w (z avoiding S_w) is explained by
C1 if both ends in U0, by C0 if both in U1, by h only if crossing (z ∈ U0, z+e_u ∈ U1).
- Easy w: all z avoiding S_w lie in U0. Edges at heavy units u (h(e_u)=1, hence h(z+e_u)=1 for all z) are ALWAYS
  crossing: the world-1 union-find gets L_w - 1 merges, and the h-explained edges give the gap #heavy(S_w) ∩ ... =
  d_w - (L_w - 1). (E1 is exact: the base-point choice z cannot help, L_w(z) <= L_w.)
- Hard w: the cube above z_{S_w} lies in U1; all edges C0-explained; E3 gives d_w OR gates, but NOT privately.
  Why (PROVED, structural): shared g ∈ D0'_w ∩ D0'_j would need a point forcing g=1 (>= z_{S_w}+e_u) below a point
  forcing o_j=0 (<= z_{S_j}); z_{S_w}+e_u <= z_{S_j} is impossible, so the Pippenger "freeness" contradiction is
  unavailable. With base points z_w <= z_{S_w} in U1 and atoms z_w+e_u it IS available exactly when z_w avoids S_j and
  z_j avoids S_w (then z_w+e_u <= z_j for u ∉ S_j, C0 monotone): this is Theorem X / E0.1(c) / B4. So the world-0 cut
  is private iff a Theorem-X-type zero-set family exists, which the sorry case (hC) excludes. The cut argument reduces
  to the known open case; it does not cross it.
CHECKED (run8-run10.py):
- Pairwise conflicts: D1_w (easy) ∩ D0'_j (hard) = ∅ in all data (NOT proved: both witnesses are crossing pairs).
  D0'–D0' conflicts in 108 set pairs.
- Matching with easy->D1, hard->D0' only (rule A): short in 2317/2559 (heavy units of easy sets).
  Rule B (each set: D1(easy) ∪ D0'(hard) ∪ Dr ∪ Pr): short ONLY on cxe3, cxtw3, cxtw3c, cxtw4, cxtw4c (the coin-rule /
  two-world-Hall refuters), deficiency 2,2,2,3,3 (= t-1, the shared G = x0 ∨ T).
- In all 2559: deficiency(rule B) <= #{gates outside the B-classes, not N, with C0(g) ≠ C1(g)} (6,6,6,8,8 there).
  Hard-set world-0 deficiency def0 > 0 only on those same 5 circuits.
- Π* (section 1) with D1 for ALL sets (also hard) succeeds everywhere: the gates m_i = x_i ∨ (x_{i+t}∧N) of cxtw are in
  D1 of hard sets, i.e. the N-dependent gates in world 1 repay the world-0 sharing there.
CONJECTURE (J-repay): deficiency of rule B <= #(N-dependent gates outside the classes). Weak evidence: the 5
deficient circuits all have slack >= 27.
