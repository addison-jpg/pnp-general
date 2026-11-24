# front: heavy points (h >= x_v, v in a set) at a MinCE — answer to coord's 08:13 question (front main session, 08:30 UTC)

Notation: v heavy iff h(e_v) = 1. A = star of v = {w : v in S_w} (a sunflower: the petals S_w \ v are pairwise disjoint), B = other sets.
sigma = base - s >= 1 at a MinCE.

## 1. Answer: NOT excluded by any current lemma (status OPEN)
- What we have (PROVED, w9/twh_fableE.md): s >= 1 + sum_{w in B} d_w + sum_{w in A} |P_w| (P_w = private-above class, contains o_w).
  At a MinCE this only says sum_{w in A} (d_w - |P_w|) >= sigma + 1; it is satisfiable because |P_w| is typically 1.
- N2 at v: #removable(x_v := 0) <= deg(v) - sigma <= deg(v) - 1. Excluding heavy points this way needs
  "heavy v => #removable(x_v := 0) >= deg(v)", a SPECIAL CASE of G1's per-point statement (which for any single point would prove 951).
  CHECKED (w9/heavy/hv.py; removable = const/copy/function-duplicate/unread after x_v := 0): delta_v = #removable - deg(v) >= 0
  for EVERY point, heavy or not, on 2559 circuits (named cx*, cxe3, cxT2, cfgI, cx44_*, cxP*, hard4, bad, badT, chk/c.jsonl).
  So data cannot separate heavy points from light ones here; no heavy-specific mechanism found.
- Why it is not a shortcut: under x_v := 1 the circuit is pure C0 (monotone). A star merge at a zero point z (z_v = 0) can collide
  with a C0 merge of b in B only on an N-dependent gate g with g^{C1}(e_u) = 1 > g^{C0}(e_u), h(e_u) = 0, u in S_w \ S_b (a crossing
  at a unit, Lemma E0.1(b)). That IS the cross-world piece, in the special geometry "world 0 contains the half-cube {x_v = 1}".
- HARD4 has h = x4 with 4 in {0,4,5}: a heavy point (the gadget's y = h); but the gadget (A|y)&(A|~y) = A works for ANY y = h,
  so heavy-point exclusion would not by itself kill the gadget.

## 2. NEW (CHECKED): heavy SPLIT rule — with a heavy point only a sunflower floats
Rule: pin every b in B at its own point z_{S_b} (x_v = 1 there, so h = 1: pure C0 world, Wegener's monotone setting); let only the star
sets A choose fractionally among their zero points (z_v = 0 forced).  Code w9/heavy/split.py (BASE=zS), split2.py (BASE=ev).
- B pinned at z_{S_b}: max load <= 1 on ALL 4764 (circuit, heavy v) pairs (489 named/bad/badT + 4275 chk/c.jsonl);
  B's own pinned merge sets never collide (max fixed load 1.0).
- Integral version (star sets at z = 0): FAILS (load 2 on 9 + 9 pairs) -> the star needs fractional weights.
- B pinned at the COMMON base e_v instead: FAILS on chk/c.jsonl#264 (B-B collision, load 2; same circuit as gAdyD's variant-2 failure).
  So pin each b at its own z_{S_b}, not at e_v.
Consequence (proposal for lanes A/C): MergeFrac at a MinCE splits into
  Case I  (no heavy point in any set): gAdyD's refined form = no mixed points: two monotone worlds + cross-world conflicts (MergeWorld).
  Case II (heavy v in a set): B pinned at z_{S_b} (C0 merge sets, monotone); the fractional part is ONE SUNFLOWER (core v, disjoint petals),
          all of whose zero points are world-0 or mixed (no world-1 point: h(z + e_v) = 1).
Caveat: "B pinned" includes the claim that C0 merge sets at different bases z_{S_b} are disjoint. That is FALSE for junk-padded monotone
circuits (g = (x_u & x_a) | (x_u' & x_a'), u,u' in S_b \ S_b', a,a' in S_b' \ S_b, is a merge for both); data has none. A proof
must either use MinCE cleanliness/minimality there or let B float too (the full LP, still <= 1).
