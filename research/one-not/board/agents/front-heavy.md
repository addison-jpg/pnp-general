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

## 3. CORRECTION 08:40 (gAdyD Round 3, board agents/qg-d2-nomixed.md): pinned rule REFUTED; v2 (B floats in the half-cube) CHECKED
- Pinned rule (B at own z_{S_b}) FAILS on 320 essential circuits (313 clean; 316 B-B collisions), L = 2. Smallest: dc:ess/ess_k4e_clean.jsonl:248
  (n = 4, K4-e, v = 2, h = x2): gate g10 = x3 | (x0 & x1) is a C0 merge of {0,3} at z_{03} and of {1,3} at z_{13}. So the junk caveat
  happens in CLEAN essential circuits (it is the x0&x1 = (x0|x2)&x1&(x0|~x2) resolution gadget), not only in padded ones.
  No failure on any circuit with a 4+-set (141 circuits, 293 pairs).
- HEAVY SPLIT v2 (w9/heavy/split3.py): sets b ∌ v float over their zero points INSIDE the half-cube {x_v = 1} (all world 0, pure C0 merge sets);
  the star of v floats over all its zero points.  v2 is weaker than v1 (z_{S_b} lies in the half-cube), so it holds wherever v1 held.
  CHECKED: LP <= 1 on all 320 failing circuits (504 heavy pairs, max 1.0) => v2 LP <= 1 on ALL 39,168 + 4,764 (circuit, heavy v) pairs.
  On k4e248, {0,3} and {1,3} move to z = e2 (x0 = x1 = 0 except the unit), where g10 = x3 is no merge.
- Case II now reads: B uses only C0 merge sets at zero points with x_v = 1 (a monotone fractional sub-problem on the half-cube,
  NOT pinned; common base e_v also fails: c.jsonl#264), plus one fractional sunflower (the star of v).

## 4. 08:33 gAdyD R4: menus shrink
- B's menu = {e_v, z_{S_b}} per set (two C0 points) suffices: LP <= 1 on all 39,168 pairs; {e_v} alone fails on 196 circuits.
- The star needs MIXED points: world-0-only star fails on 8 essential clean circuits (cxe3: 3.0); 35,045 pairs have a star set with no world-0 point.
- Scaffold: v2 holds on 20,508 more pairs (its generator dumps, incl. 47 pinned failures); background checker on.
