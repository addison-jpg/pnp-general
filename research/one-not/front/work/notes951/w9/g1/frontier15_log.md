# frontier15_log.md — closing the base-15 frontier of cover2.py (restart-safe log)
Conventions as in g1_fable.md / pairrule_log.md: minimal counterexample F (all point deletions satisfy the bound, hence by
heredity every F|rho for a restriction rho does), clean minimum one-NOT circuit, sigma = base - s >= 1, l(u) = #lines (|S|>=3)
through u, P(u) = pair-partners, d = l + p.  For any restriction rho: dead(rho) <= loss(rho) - sigma.
Backup of the round-4 checker: cover2_round4_backup.py.

## 0. Status of the two named examples under 245pqr (from uncovered_after_pairs.json)
 #0 {0567},{034},{126},{145},{235},{247}+{01},{02}: only scenario sigma=1, B={0,1,2,4,5}, V1={3,6,7}; every T of every V1
    point has size >= 2 and no T is a TIGHT pair (0 and 2 have degree 4) -> no rule fires.
 #1 {0567},{034},{135},{146},{237},{245}+{01},{02}: sigma=1, B={0..5}, V1={6,7}; T's {1,4} (6) and {2,3} (7) are tight
    pairs, q passes because the pair-partner 0 of 1 (of 2) lies in the other T.

# CONTINUATION (second agent). NOTE: the first agent left an UNPROVED draft of a rule 'a' in cover2.py (no text in this log).
# It was unsound as coded (cap l-sigma-1 without the W-exception below); it has been REPLACED by the proved rule 'a' of section 1.

## 1. Rule 'a' = P-TIGHT PAIR LEMMA (generalises G1.7 / rules 4, 5, q to points with pair-sets). PROVED, encoded.
Definitions (sigma arbitrary). R_u = readers of x_u; pair-gate = x_u|x_w, w in P(u); G_u = {g_w : w in P(u) without pair-gate},
g_w = lowest gate restricting to x_w under x_u := 0 (a non-reader, rule p (b)). Rule p: |R_u| + |G_u| = nonpair(u) + p(u) <= d(u) - sigma.
u is P-TIGHT iff nonpair(u) = l(u) - sigma. Then dead0(u) = R_u ∪ G_u EXACTLY (N2 with equality).
 (T0) capL(u) = 0 (as computed in cover2) => u p-tight.  [u in V1: one reader, no pair-gate (P2), nonpair = 1 = l-sigma.
      u in B, pB = 0: no pair-gates, nonpair = readers >= 2 = l-sigma.  u in B, pB >= 1: l-sigma = 1 <= nonpair <= l-sigma.]
 (T1) AND-readers of a p-tight u.  If g = x_u & y (or g = N = ~x_u) reads x_u, then under x_u := 0 g is constant, every reader of g
      dies and is no reader of x_u (clean), so it lies in G_u: it is g_w = g | x_w (resp. N & x_w) for a w in P(u) without pair-gate
      [g_w = g o y', y' restricts to x_w and is below g_w, hence y' = x_w].  So EVERY reader of an AND-reader g of a p-tight u is
      g | x_w with w in P(u).
 (T2) v in V1 p-tight (l(v) = sigma+1) => its reader is OR-type r = x_v | c.  [~x_v: antitone argument G1.1(b). r = x_v & c: by (T1)
      all readers of r are r | x_w, w in P(v); at z = 1_{P(v)} toggling x_v moves only r (r <= x_v is no output), but OR(L) for a
      line L through v (L ∩ P(v) = ∅) moves.]  Then AL: c is a gate over A_j, c <= OR(T_S') for every set S' through v.
LEMMA A (sigma = 1). Let v in V1 be p-tight, S a set through v with T_S(v) = S ∩ A_j \ v = {a,b}, a and b p-tight, P(a) ∩ P(b) = ∅.
 (A0) a gate g1 = x_a | x_b exists, its ONLY reader is c = c_v, and c = g1 & y; x_a & x_b does not exist; c is no reader of x_a, x_b.
 (A1) a, b in B.
 (A2) no second set S' of v has a p-tight pair T_S'(v) = {a',b'} with P(a') ∩ P(b') = ∅.
 (A3) [superseded by (A3') in section 1b: k <= l(a) - 2; the first draft allowed k = l(a)-1 under a W-condition, which never holds]
Proof. Restriction x_a = x_b = 0. S is a line (contains v,a,b), a,b are not pair-partners, loss = d(a)+d(b) (|S|-1 drops by 2, every
 other set through a or b by 1), and F-{a,b} satisfies the bound (heredity, pairrule_log section 0): dead <= d(a)+d(b)-1.
 Dying gates: R_a ∪ G_a ∪ R_b ∪ G_b (g_w^a still restricts to x_w, w != b), c (constant 0: c <= x_a|x_b) and r (= x_v).
 - r is in none of the four sets: it reads x_v and the gate c; r|_{x_a=0} = x_v | c' is 1 at e_v, so != x_w (v not in P(a)).
 - c not in G_a: c|_{x_a=0} <= x_b & OR(T_S'), not x_w.  c not in R_a: c = x_a|y >= x_a contradicts c <= OR(T_S') (S' another set of v,
   a not in S'); c = ~x_a has c(0) = 1; c = x_a & y is an AND-reader of the p-tight a, so by (T1) its reader r = x_v|c would be c|x_w.
 - R_a ∩ G_b = ∅ (a reader x_a o y restricts under x_b := 0 to x_a o y' != x_w); G_a ∩ G_b = ∅ because g|_{a=0} = x_w and g|_{b=0} = x_w'
   give w = w' in P(a) ∩ P(b) = ∅.  R_a ∩ R_b = gates reading both, tau of them.
 Count: (d(a)-1) + (d(b)-1) - tau + 2 + extra <= d(a)+d(b)-1, i.e. tau >= 1 + extra.
 (A1): if a or b is in V1 then tau = 0 by P2. Contradiction.
 (A0): x_a & x_b is an AND-reader of both; by (T1) each of its readers is (x_a&x_b)|x_w with w in P(a) and in P(b): it has no reader,
   but it is not an output. So tau = 1, g1 = x_a|x_b exists and extra = 0. g1 becomes 0, all its readers die; a reader of g1 is not in
   R_a ∪ R_b (clean), not r (c != g1 since g1 >= x_a), not in G_a ∪ G_b ((x_b|y') and (x_b&y') are != x_w): it is c. c = g1|y >= x_a is
   impossible, so c = g1 & y.
 (A2): c reads g1 and g2 = x_a'|x_b' (both read only by c), c = g1 & g2. Under x_a' = x_b' = 0 the gates R_a' ∪ G_a' ∪ R_b' ∪ G_b'
   (d(a')+d(b')-3 gates, tau' = 1), c, r AND g1 die (g1 is unread, no output, not in the four sets since {a,b} ∩ {a',b'} = ∅ and
   g1 restricts to x_a|x_b): d(a')+d(b') > loss - 1. Contradiction.
 (A3'): see section 1b. (A pair {a,b} is used by at most one v: two users v, v' lie on the line through a,b and the later one has the
   earlier one in its T; so the feeders x_a|x_{b_i} are distinct non-pair readers of x_a.)  ∎
Weight >= 2 inputs: through AL (c <= OR(T_S') on the whole cube) and the full-subcube restrictions; (A3) uses z = 1_W.
Encoding (letter 'a', needs 'p'; sigma = 1, v in V1 with l(v) = 2): a T of size 2 with capL(a) = capL(b) = 0 and P(a) ∩ P(b) = ∅ is a
p-tight pair; (A1) reject if a or b in V1; (A2) reject two p-tight pairs of v; (A3') counter ('a',x) <= l(x)-2.
Base-15 frontier (33 systems): 245pqr 33 feasible -> 245pqra 9 feasible (with (A3'), section 1b).

### 1b. CORRECTION / STRENGTHENING of (A3) (the W-exception written above does NOT exist; the encoded form is the strong one)
 (A3') For a p-tight B-point a used in k p-tight pairs {a,b_i} (hypotheses of Lemma A; the pairs lie on k DISTINCT lines S_i through
  a, since b_j in S_i would be in T_{S_i}(v_i)):   k <= l(a) - 2.
 Proof. The k feeders x_a|x_{b_i} are distinct non-pair readers of x_a (A0), nonpair(a) = l(a)-1. If k = l(a)-1 the readers of x_a
  are exactly the feeders and the pair-gates x_a|x_w (w in W). Let L' be the line through a different from S_1..S_k and
  z = 1_W + sum_i e_{b_i}: every reader of x_a is 1 at z whatever x_a is, so no wire depends on x_a at z, but OR(L')(z) = 0
  (b_i not in L', W ∩ L' = ∅) and OR(L')(z+e_a) = 1. Contradiction. ∎  (weight-(|W|+k) input)
 Consequences: a p-tight pair of Lemma A consists of two B-points with l >= 3 (for sigma = 1: l = 3, no B pair-partner); a B-point
 with l = 2 is in NO p-tight pair (this subsumes rule q and its exception: comparing e_w+e_b with e_w+e_b+e_a kills it always).
 Encoding 'a': counter ('a',x) <= l(x) - sigma - 1 (sigma = 1).   [This is what the first agent's draft had; now proved.]
 Base-15 frontier: 245pqra leaves 9 of 33 feasible (ranks 2,3,4,7,10,14,15,18,28).

## 2. Rule 's' = ABSORPTION AT THE SINGLETON USER (closes the blocker of pairrule_log section 6). PROVED, encoded (needs 'r').
Statement (any sigma). If a point u (in B or V1) is used as singleton by at least one V1 point (through a line or a pair-set), then
      kL(u) <= l(u) - sigma - 2.        (rule r allowed kL = l - sigma - 1 for u in B with pB >= 1 under condition (R3); that mode is impossible)
Proof. u in V1: rule r (R2). u in B: by rule p, nonpair(u) + kL(u) + eps <= l(u) - sigma, eps = 1 iff some c_v (v in U(u)) is not a
 reader of x_u. If eps = 1 or nonpair >= 2 or kL <= l-sigma-2 we are done. Remaining mode: nonpair(u) = 1, kL = l-sigma-1, every c_v is
 the unique non-pair reader h_u, and N2 is TIGHT: dead0(u) = R_u ∪ G_u ∪ {r_v : v in UL(u)} exactly. (R3): h_u != N, so h_u = x_u & y
 and all r_v are OR-type r_v = x_v | h_u. Under x_u := 0, h_u = 0 and every reader of h_u dies; it is no reader of x_u (clean), so it is
 g_w = h_u | x_w (w in P(u), as in (T1)) or r_v (v in UL(u)). Let z = 1 on P(u) ∪ UL(u), 0 elsewhere. At z the pair-gates of u are 1,
 and every reader of h_u is 1 (x_w = 1 resp. x_v = 1) whatever x_u is: no output depends on x_u at z (h_u <= x_u is no output).
 But the users in UL(u) lie on at most kL = l-sigma-1 lines through u, so there is a line L through u with L ∩ UL(u) = ∅
 (and L ∩ P(u) = ∅): OR(L)(z) = 0 != OR(L)(z+e_u). Contradiction. ∎
 Uses the weight >= 2 input z (the user's own variable x_v = 1 absorbs the junk gate h_u), exact dead-gate accounting under x_u := 0.
 Encoding 's': in rule r, for u in B with k(u) >= 1 require kL(u) <= l(u)-sigma-2 (the (R3) alternative is switched off).
 Base-15 frontier: 245pqras leaves 7 of 33 feasible: ranks 2, 4, 7, 10, 15, 18, 28.

## 3. Rule 'b' = BOTTOM LEMMA with pair-gates (first V1 = ∅ rule; route (1) "second death under x_w := 1" + relative AL). PROVED, encoded.
U-TYPE points: t in B with l(t) = sigma+1. Facts (any sigma):
 (U1) nonpair(t) = 1 (rule p), t is p-tight, W_t := {w in P(t) : pair-gate x_t|x_w exists} is a non-empty subset of P(t) ∩ B
      (readers >= 2; P2), and W_t contains every w in P(t) ∩ B with d(w) = 2+sigma (w tight => G1.9).
 (U2) the unique non-pair reader is OR-type: h_t = x_t | c_t.  [h_t = N: (R3) monotonicity on Q = {x_W = 1}.  h_t = x_t & c: by (T1) every
      reader of h_t is h_t | x_w', w' in P(t); at z = 1_{P(t)} the pair-gates and all readers of h_t are 1, no output depends on x_t, but a
      line through t does.]
 (U3) relative AL: for every set S through t with S ∩ W = ∅ (all lines, and pair-sets {t,w'} without pair-gate) and every z in Q vanishing
      on S\t: c_t(z) = 0.  [the readers of x_t are pair-gates (= 1 on Q) and h_t; c_t is below h_t, so c_t(z) = c_t(z+e_t); if it were 1,
      no wire would move.]  Hence c_t is not a variable x_s (s would lie on >= 2 lines through t), and h_t is not an output
      (h_t = OR(S): z = 1_W + e_e, e in S\t, contradicts (U3) for another line S' through t).
BOTTOM LEMMA. U = U-type points, N' = B \ U. Let g* be the LOWEST gate among the readers r_v (v in V1) and the h_t (t in U).
 Every gate strictly below g* that reads a variable x_u has u in N', or u in U and the gate is a pair-gate of u. So the other input c of g*
 (a gate, by AL resp. (U3)) is a function of key(x) := (x restricted to N', values of the pair-gates having an endpoint in U).
 (B-V) g* = r_v, v in V1 is impossible if every x in {0,1}^B has the same key as some x'' vanishing on (S\v) ∩ B for some set S through v:
       OR-type gives c == 0 (AL: c <= OR(S\v), c does not depend on V1 variables), AND-type gives c == 1; not clean.
 (B-U) g* = h_t, t in U, W = W_t is impossible if
       (R) every x in Q = {x_W = 1} has the same key as some x'' in Q vanishing on (S\t) ∩ B for some set S through t with S ∩ W = ∅
           [key taken with all pair-sets inside B having an endpoint in U, except {t,w'} for w' not in W: a superset of the real
           pair-gates, hence a finer equivalence], and
       (C) 2 + m_W + |W ∩ U| > loss(W) - sigma,   m_W = #sets meeting W,  loss(W) = sum_{S ∩ W != ∅} (|S|-1).
       Proof: (R) and (U3) give c|_Q == 0. Restriction x_W := 1 leaves a correct circuit for F' = F minus the sets meeting W
       (bound holds by heredity: point deletions then set deletions), base loss = loss(W), so dead <= loss(W) - sigma. Dying gates:
       c (== 0), h_t (== x_t), the m_W outputs of the sets meeting W (== 1), and h_w = x_w|c_w for w in W ∩ U (== 1, not an output
       by (U3)); all distinct (different restrictions; outputs of different sets differ; h_w has one variable). That is (C) violated.
 If V1 ∪ U != ∅ and every v in V1 satisfies (B-V) and every t in U satisfies (B-U) for EVERY admissible W (forced partners ⊆ W ⊆ P(t) ∩ B,
 W != ∅), the scenario (sigma, B) is impossible.  ∎
 Encoding 'b': bottom_rule() in cover2.py, brute force over {0,1}^B for (B-V) and (R); applied to scenarios that survive the DFS.
 Hand check #28 = {4567},{014},{025},{136},{237}+{06},{17},{24},{35}, B = all (V1 = ∅): all points strictly tight, U-type; first h_t has
 c_t = phi(pair-gates), == 0 on {x_w = 1} (w = partner of t); x_w := 1 kills c_t, h_t, x_t|x_w, h_w and the two line outputs through w:
 6 deaths > loss - 1 = 5 (w in the 4-line) resp. 4.  #18 (V1 = {7}) and both scenarios of #10 die the same way.
 Base-15 frontier: 245pqrasb leaves 4 of 33: ranks 2, 4, 7 (2 scenarios), 15.

## 4. Recount after rules a, s, b (pure DFS; cover2.py, snapshot cover2_round5_wip.py)
 rules          skel n=8 (4)  n=9 (50)  n=10 (1538) | pairs n=8 (262)  n=9 sample (2178) | base-15 frontier (33)
 245pqr [before]     4           36         734      |      58              354           |   33 open
 245pqra             4           37         787      |     122               -            |    9
 245pqras            4           37         789      |     124               -            |    7
 245pqrasb           4           37         792      |     130              713           |    4  (ranks 2, 4, 7, 15)
 n=8 pairs by #pairs under 245pqrasb: 1:8/9 2:22/27 3:29/44 4:35/59 5:25/52 6:10/39 7:1/20 >=8: 0/12.
 n=9 sample by #pairs: 1:84/151 2:207/439 3:204/540 4:135/499 5:57/330 6:21/137 7:4/60 8:1/20.

## 5. FINAL STATE of this round (cover2.py default rules now '245pqrasb'; backups: cover2_round4_backup.py = before, cover2_round5_wip.py)
New frontier file: uncovered_after_round5.json (mkjson5.py; frontier_245pqrasb_*.pkl): 1204 minimal uncovered systems (was 1279),
 by base 15:4 16:30 17:155 18:338 19:379 20:181 21:86 22:23 23:6 25:2 (before 15:33 16:71 17:322 ...); n=8 part (complete):
 15:4 16:30 17:47 18:32 19:15 20:3 21:1. Every surviving scenario still has sigma = 1.
Base-15 frontier NOT closed: 4 of 33 remain (new ranks 0-3):
 R0 {2367},{016},{035},{124},{157},{456}+{02},{13}   B={0,1,2,3,5,6}
 R1 {2367},{017},{034},{056},{125},{146}+{02},{13}   B={0,1,2,3,6}
 R2 {2367},{034},{056},{125},{146},{457}+{02},{13}   B={0..5} and B={0..6}
 R3 {1456},{2357},{012},{036},{047}+{05},{13},{24}   B={0..5}
Exact obstructions (worked by hand, all end in EQUALITY of a death count, i.e. one death short):
 (o1) SLACK points: a B-point with l = 3 and one B pair-partner (d = 4; point 1 in R0, 0 and 1 in R1, 0 in R3). Case nonpair = 2: it is
      p-tight and Lemma A applies (R0 dies in this case). Case nonpair = 1: unique reader h_u with relative AL but N2 has slack 1, AND-type
      h_u is not excluded. In R3 with g* = h_0: x_5 := 1 kills c_0, h_0, x0|x5, h_5, o_1456, o_2357 = 6 = loss - 1 exactly.
      In R0 (nonpair(1) = 1): bottom + cascade gives c_7 <= x5&x6 (dies by N2 at 5), but g* = h_0 gives c_0|_{x2=1} <= x5&x6 and the
      combined restriction x_2 := 1, x_5 := 0 has dead = 8 = loss - 1 exactly (route (3) is one death short).
 (o2) STRICT l=3 B-points without pair-gates (4, 5, 6 in R2): two OR-readers, no relative structure. In R2 (B = {0..6}) Lemma A makes
      g1 = x4|x5 a pseudo pair-gate and 4, 5 U-like; the bottom argument then closes every case except "g* is a reader of x_6",
      g6 = x6 | phi(x0|x2, x1|x3). phi = AND dies (x_0 = x_2 = 0 kills 5 > 4 gates); phi = OR / N-dependent phi stay open.
 Natural next rules (not proved/encoded): refined scenarios with nonpair(u) enumerated for slack points; feeders of Lemma A as pseudo
 pair-gates in rule b; "bottom + cascade" (c <= x_u from the key analysis => N2 at u); a surcharge for single-reader points in the
 near-minimal restricted circuit C|_{x_W=1} (conjecture H+), which is exactly what the equalities above are missing.
Reproduce: python3 cover2.py none 245pqr,245pqra,245pqras,245pqrasb 8 9 10 (23 s); python3 pairrun.py eval 8|9 none 245pqr,245pqrasb (1 s, 9 s);
 python3 frontier.py 245pqrasb skel8|skel9|skel10|pair8|pair9 ; python3 mkjson5.py ; python3 f15test.py RULES 0 33 (old base-15 list).

# ROUND 6 (continuation on coordinator's request; referee_asb.md not present yet when this was written)
## 6. Rule 'n' = REFINED SCENARIOS (nonpair classes) + refined bottom lemma with the equality case (E). PROVED, encoded (needs a, s, b).
Refinement. For u in B put m = l(u)-sigma (rule p: 1 <= nonpair(u) <= m). Classes: U (m = 1; needs pB >= 1), and for m >= 2:
 T: nonpair = m (p-tight, capL 0);  M: 2 <= nonpair <= m-1 (only m >= 3; capL = m-2);  S: nonpair = 1 (only pB >= 1; "slack U-like": unique
 non-pair reader h_u, W_u != ∅, capL = m-1, N2 has slack m-1). Every minimal counterexample realises one class vector, so a scenario
 (sigma,B) is impossible iff every class vector is impossible; DFS and rule a use capL / p-tightness of the class vector.
Facts for class S (t with unique non-pair reader, not p-tight): h_t != N (R3 monotonicity, needs only nonpair = 1). h_t = x_t|c: (U3)
 holds verbatim. h_t = x_t&c: for z in Q = {x_W=1} vanishing on S\t (S ∩ W = ∅) sensitivity of o_S gives c(z) = 1; so c is a gate or
 c = x_w with w in W; the latter is an AND-reader of x_w, impossible if w is of class U ((U2)) or tight by degree (G1.5).
LEMMA N-O (any minimal counterexample, any point w with a line): some non-pair reader of x_w is NOT an output.
 Proof: an output reading x_w is o_S = x_w|c with w in S. If all non-pair readers are outputs o_{S_i} (at most l-sigma < l lines among the
 S_i, rule p), put z = 1 on P(w) ∪ U(S_i\w): every reader of x_w is 1 at z, but a line through w outside the S_i vanishes. ∎
REFINED BOTTOM LEMMA. U' = classes U ∪ S, N' = B \ U'; g* = lowest gate among V1-readers and h_t (t in U'); its other input c is a function
 of key = (x on N', pair-gates touching U') exactly as in section 3; (B-V) unchanged. For g* = h_t, W = W_t (for t of class S require every
 w in W of class U or tight by degree, else no conclusion), under (R): c|_Q == 0 (OR-type) or == 1 (AND-type, class S only), and x_W := 1
 kills: h_t (== x_t); c, counted if t is of class U, or if every w in W has P(w) ∩ B ⊆ {t} and (w in U' or no line through w inside N')
 [then c is no output through W: a pair output x_w|x_b needs a second B-partner b, a line output that is a function of the key lies in
 N']; the m_W outputs; h_w for w in W of class U; ONE h_w for w in W of class S (two of them could be the same gate x_w&x_w'; an S-class
 h_w dies whatever its type and is no output: OR-type by (U3), AND-type is <= x_w); and, if t is of class U, ONE non-output reader of a
 w in W ∩ N' of class T (Lemma N-O; see section 9 for class T and for 'max' instead of sum with the S-bonus; it is OR-type, so it is not c (c|_Q == 0), it is
 not h_t (which reads x_t and the gate c) and not an h_w' (h_w' = x_w'|x_w has a variable input, x_w'&x_w is an AND-reader of the tight w)).
 Count: dead > loss(W) - sigma excludes (t,W).
 (E) EQUALITY CASE = the missing one-death surcharge. If dead = loss(W) - sigma, W = {w}, w of class U and P(w) ∩ B = {t}, then (t,W) is
  excluded as well. Proof. x_w enters the cone of c only through the pair-gate p = x_t|x_w; c is not constant but c|_{x_w=1} is, so some
  gate of the cone or c reads p. Under x_w := 1 EVERY reader of p dies (p == 1: OR -> 1, AND -> its other input, NOT -> 0), and a reader
  of p is not h_t (c != p: OR-type c|_Q = 0; AND-type h_t = x_t&p = x_t), not h_w (x_w|p = p), not an output through w (p|y = OR(S)
  forces S = {t,w}; p&y <= x_t|x_w). By equality there is no further death, so the ONLY reader of p is c.
   OR-type: c = p&y has y|_Q == 0, y a gate of the cone (no variable, no pair-gate), a further death; c = p|y is 1 on Q; so c = ~p = N and
    h_t = x_t | ~(x_t|x_w) = x_t | ~x_w.  Under x_w := 0 the gate h_t becomes constant 1: a death that is no reader of x_w and not in G_w,
    so dead0(w) >= d(w)-sigma+1 for the p-tight w. Contradiction (N2 at w).
   AND-type: c = p|y gives h_t = x_t&(x_t|x_w|y) = x_t (not clean); c = ~p is 0 on Q; c = p&y has y|_Q == 1, y a gate of the cone, not an
    output through w (a line output through the U-type w is no function of the key: e_t vs e_t+e_w; pair outputs of w: only p), so a
    further death. Contradiction. ∎   (two-sided restriction x_w := 1 / x_w := 0 with exact accounting: route (3))
 Hand checks. old #15 = {1456},{2357},{012},{036},{047}+{05},{13},{24}, B = {0..5}: class T for 0 dies in the DFS (Lemma A: T = {0,3} would
  be a p-tight pair with the l = 2 point 3); class S: every g* is excluded, g* = h_0 by (E) with w = 5 (6 deaths = loss-1, then
  h_0 = x_0|~x_5 dies under x_5 := 0). old #4 = {2367},{017},{034},{056},{125},{146}+{02},{13}, B = {0,1,2,3,6}, classes SSUUT: all four
  h_t excluded by the count (h_w of the S-class partner is the extra death).
Encoding 'n': class loop in feasible(), bottom_rule(..., cls=...). Results (rules 245pqrasbn):
 [before the additions of section 7] base-15 frontier: 2 of 33 remain (old ranks 2 and 7). skeleton n=8/9/10: 4, 37, 794 (b: 792);
 pairs n=8: 133 (130); n=9 sample: 717 (713).

## 7. Additions to rule 'n': (P) Lemma-A feeders as PSEUDO PAIR-GATES in the bottom lemma, (K) BOTTOM + CASCADE. PROVED, encoded.
(P) Setting (sigma = 1, fixed class vector): v in V1 with l(v) = 2, a line S through v with S ∩ V1 = {v}, S ∩ B = {a,b}, a and b of class T
 with l = 3 and NO pair-set (d = 3, strictly tight, exactly two readers, both OR-type). Then T_S(v) = {a,b} in every peeling order and
 Lemma A (A0) gives the feeder g1 = x_a|x_b (read only by c_v). So the readers of x_a are g1 and g_a = x_a|c_a, of x_b: g1 and g_b.
 (P1) relative AL: for the two lines S' through a avoiding b and z in Q_b = {x_b = 1} vanishing on S'\a: c_a(z) = 0 (g1 = 1 on Q_b, c_a
      is below g_a). Hence c_a is a gate, and g_a is no output (g_a = OR(L), b not in L: z = e_b+e_e, e in L\a; L = S: z = e_b).
 (P2) (A3') gives: a point is in at most one such pair. g1 is no output ({a,b} is not a set).
 Bottom lemma with pseudo pairs: g* = lowest gate among V1-readers, h_t (t in U') and the g_a (a pseudo point). Below g* a variable x_a
 of a pseudo point is read only by g1; so c is a function of key = (x on N' minus pseudo points, pair-gates touching U', pseudo gates).
 (B-V), (B-U), (E) hold verbatim with this key (their proofs use only that c is a function of the key; in (E) the gate y is not a pseudo
 gate, which is not constant on Q since pseudo points have no pair-partner).
 (B-P) g* = g_a is impossible if (R) every x in Q_b has the key of some x'' in Q_b vanishing on (S'\a) ∩ B for a line S' through a
 avoiding b, and 4 + m_b > loss(b) - 1 (m_b = #sets through b = 3): then c_a|_{Q_b} == 0 and x_b := 1 kills c_a (== 0), g_a (== x_a),
 g1 (== 1, no output), g_b (== 1, no output by (P1) for b) and the m_b outputs through b; all distinct. ∎
(K) BOTTOM + CASCADE for g* = r_v, v in V1 with l(v) = sigma+1 (OR-type, c_v <= OR(S\v) for all S): c_v(x) = 1 only if key(x) is BAD
 (not the key of any x'' vanishing on some (S\v) ∩ B). If some u in N' of class T (p-tight), v not in P(u), has x_u = 1 in every bad key,
 then c_v <= x_u on the whole cube; x_u := 0 kills c_v and r_v; r_v is no reader of x_u and not in G_u (it restricts to x_v, v not in
 P(u)), so dead0(u) >= d(u)-sigma+1. Contradiction (this is G1.3 (ii) fed by the key analysis). ∎
Hand checks (the last two base-15 systems):
 old #2 = {2367},{016},{035},{124},{157},{456}+{02},{13}, B = {0,1,2,3,5,6}, classes U S U U T T (class T for 1 dies by Lemma A):
  pseudo pair {5,6} (user 4, line {456}); key = (x0|x2, x1|x3, x5|x6). r_4, r_7: c == 0 (zero {1,2} resp. {1,5}); h_0: x_2 := 1, 6 > 5;
  h_1 (S): x_3 := 1, 6 > 5; h_2: x_0 := 1, 6 > 4; h_3: x_1 := 1, 7 > 6 (h_1 is the extra); g_5: x_6 := 1, 7 > 6; g_6: x_5 := 1, 7 > 5.
 old #7 = {2367},{034},{056},{125},{146},{457}+{02},{13}: pseudo pair {4,5} (user 7, line {457}).
  B = {0..5}: key = (p02, p13, x4|x5); r_6, r_7 constant (zero {2,3}); h_0..h_3: 6 > 5, 6 > 5, 6 > 4, 6 > 4; g_4, g_5: 7 > 5.
  B = {0..6}: key = (x6, p02, p13, x4|x5); r_7: bad keys have x6 = 1 -> (K) with u = 6; the h_t and g_4, g_5 as before.

## 8. STATE after round 6 (cover2.py default rules '245pqrasbn'; backups cover2_round5_final.py = rules up to b, cover2_round4_backup.py)
 rules          skel n=8 (4)  n=9 (50)  n=10 (1538) | pairs n=8 (262)  n=9 sample (2178) | old base-15 frontier (33)
 245pqr              4           36         734      |      58              354           |   33 open
 245pqrasb           4           37         792      |     130              713           |    4
 245pqrasbn          4           38         799      |     135              726           |    0   <-- BASE-15 FRONTIER CLOSED
 n=8 pairs by #pairs: 1:8/9 2:25/27 3:30/44 4:36/59 5:25/52 6:10/39 7:1/20 >=8: 0/12.  All runs < 15 s.
 New frontier file uncovered_after_round6.json (mkjson6.py, frontier_245pqrasbn_*.pkl): 1221 minimal uncovered systems,
 by base 16:29 17:133 18:357 19:402 20:182 21:87 22:23 23:6 25:2; n=8 part (complete): 16:29 17:47 18:32 19:15 20:3 21:1.
 (The total grew from 1204 because newly covered systems expose larger minimal uncovered ones.) Every surviving scenario has sigma = 1.
 Smallest uncovered: 29 systems at base 16, all n = 8 (1 with one pair-set, 28 with three or more), e.g.
  {1567},{025},{036},{047},{123},{246},{345}+{01}                 5 scenarios
  {0467},{035},{124},{136},{237},{256}+{01},{02},{34}             B = {0,1,2,3,4,6}
  {2347},{017},{046},{125},{136},{567}+{02},{03},{14}             B = {0,1,2,3,4,6,7}

## 9. Further proved additions to 'n' (made while attacking base 16; they SUPERSEDE the numbers of section 8)
(K') (K) holds for every p-tight u (class U or T), v not in P(u): c_v <= x_u, x_u := 0 kills c_v and r_v. c_v is no reader of x_u
 (x_u|y is not <= x_u unless equal to x_u; x_u&y is an AND-reader, by (T1) its reader r_v = x_v|c_v would be c_v|x_w', v in P(u); ~x_u
 is 1 at 0), not in G_u (restricts to 0); r_v is not in R_u ∪ G_u (v not in P(u)). dead0(u) >= d(u)-sigma+2. ∎
(K2) (sigma = 1) g* = r_v, l(v) = 2, every bad x has x_u|x_w = 1 for a pair-set {u,w} of p-tight B-points with P(u) ∩ P(w) = ∅,
 v not in P(u) ∪ P(w), and d(u) = 3 or d(w) = 3 (then the pair-gate p = x_u|x_w EXISTS, G1.9). Then c_v <= x_u|x_w and the restriction
 x_u = x_w = 0 (loss d(u)+d(w)-1) kills R_u ∪ G_u ∪ R_w ∪ G_w, whose only common gate is p [x_u&x_w has no reader by (T1); a reader
 of x_u does not restrict to a variable x_w''; G_u ∩ G_w needs a common partner; with p present neither G contains a gate for the other
 point], i.e. d(u)+d(w)-3 gates, plus c_v and r_v (not among them, as in (K') and since c_v|_{x_u=0} <= x_w is no x_w', w' != w):
 d(u)+d(w)-1 > loss - 1. ∎   [Without the pair-gate the overlap can be 2 and the count is not contradictory; not encoded.]
(N-O for class T) In the refined count the Lemma N-O death is granted for every w in W ∩ N' of class T when t is of class U: c is no
 reader of x_w (x_w|y is 1 on Q; x_w&y or ~x_w would be an AND/NOT-reader of the p-tight w whose reader h_t = x_t|c restricts to x_t
 under x_w := 0 and is neither a reader of x_w nor in G_w, because the pair-gate {t,w} exists: one death too many). The bonus for an
 S-class h_w and the N-O bonus are not added (the two gates could coincide): max of the two.
FINAL STATE (cover2.py = cover2_round6.py, default rules '245pqrasbn'):
 rules          skel n=8 (4)  n=9 (50)  n=10 (1538) | pairs n=8 (262)  n=9 sample (2178) | old base-15 frontier (33)
 245pqr              4           36         734      |      58              354           |   33 open
 245pqrasb           4           37         792      |     130              713           |    4
 245pqrasbn          4           38         799      |     141              729           |    0
 n=8 pairs by #pairs: 1:8/9 2:25/27 3:31/44 4:37/59 5:28/52 6:11/39 7:1/20 >=8: 0/12.
 uncovered_after_round6.json: 1230 minimal uncovered systems, by base 16:24 17:132 18:357 19:410 20:186 21:90 22:23 23:6 25:2;
 n=8 (complete): 16:24 17:46 18:32 19:15 20:3 21:1.  No uncovered system of base <= 15 is left; all surviving scenarios have sigma = 1.
 Base 16 (24 systems, all n = 8; was 30 after round 5): what blocks (f16_explain.txt lists scenario, class vector, first failing g*):
  - (B-V) for a V1 point whose two T's both contain non-realizable keys through CHAINS of pair-gates (u-w-w'), e.g.
    {0347},{1257},{056},{146},{236}+{01},{02},{13},{45}: zeroing {1,2,5} forces x0|x1 = x0|x2;
  - (B-U) with |W| = 2 (a U-type point with two B-partners, e.g. W = (1,3)): x_W := 1 has large loss; count is short by >= 2;
  - V1 points with l = 3 (not p-tight, reader type unknown) as first users; class S points as W of an S-class t (h_t = x_t&x_w open).
 Reproduce: python3 cover2.py none 245pqrasbn 8 9 10 ; python3 pairrun.py eval 8|9 none 245pqrasbn ;
  python3 frontier.py 245pqrasbn skel8|skel9|skel10|pair8|pair9 ; python3 mkjson6.py ; python3 f15test.py 245pqrasbn 0 33 (-> 0 feasible).

# ROUND 7 (base 16; general lemmas; referee_asb.md still absent at the time of writing)
## 10. General lemmas added to rule 'n' (bottom_rule, refined mode). All PROVED; notation of sections 3, 6, 7.
Throughout: g* = lowest gate among V1-readers, h_t (t in U'), pseudo g_a; c = other input of g*, a function of the key.
"bad" = inputs x (in Q_W for g* = h_t; all x for g* = r_v) whose key is not the key of an x'' vanishing on an admissible S\t.
For OR-type g* (t of class U; v in V1 with l(v) = sigma+1):  c(x) = 1  =>  x bad.
(PG) PAIR-ZERO LEMMA (sigma = 1). Let {w,w'} be a pair-set of p-tight B-points whose pair-gate p exists, P(w) ∩ P(w') = ∅. Under
 x_w = x_w' = 0 (loss d(w)+d(w')-1) the gates R_w ∪ G_w ∪ R_w' ∪ G_w' are d(w)+d(w')-3 dying gates (only common gate: p, section 9 (K2)),
 so AT MOST ONE further gate dies. Consequences: p has at most one reader; N = ~p is impossible when N has a reader that also dies
 (N -> 1 and all readers of N die: two further deaths).
(E+) SURCHARGE LEMMA (any sigma for the count; the exception uses (PG), sigma = 1). Let O be a set of class-U points (t not in O for
 g* = h_t; O ⊇ W_t) such that c|_{x_O=1} == 0 (no bad x with x_O = 1; O != ∅). Then under x_O := 1, besides c, g* (== x_t resp. x_v), the
 m_O outputs through O and the |O| gates h_w (w in O), ONE MORE gate dies:   3 + m_O + |O| <= loss(O) - sigma   must hold.
 Proof. Pi_O = existing pair-gates touching O; all are == 1 on Q_O, so EVERY reader of a Pi_O gate dies under x_O := 1; such a reader
 is no h_w (U3: x_w|p_{ww'} = p, x_w''|p is 1 on a line-vanishing point of Q_w''), no output through O (p|y = OR(S) forces S = the pair-set,
 p&y is below x_w|x_w'), and it is not g* (c is no pair-gate: c|_{Q_O} = 0). c is not constant and c|_{Q_O} == 0, so c depends on some x_w,
 w in O, and x_w enters the cone only through Pi_O (w of class U). So a gate of cone ∪ {c} reads a Pi_O gate p. If it is not c: one
 more death. If only c reads Pi_O gates: c = p|y is 1 on Q_O; c = p&p' is 1 on Q_O; c = p&y needs y|_{Q_O} == 0 with y a cone gate
 (variables of N', pair- and pseudo-gates are not == 0 on Q_O), y not constant, so y depends on x_O and a gate of cone(y) ∪ {y} reads a
 Pi_O gate: again a reader other than c. Remaining case c = ~p = N, p = x_w|x_w', w in O:
   w' = t: g* = h_t = x_t|~x_w becomes constant under x_w := 0: a death outside R_w ∪ G_w for the p-tight w (as in (E));
   w' != t (or g* = r_v): by (PG) for {w,w'} (encoded hypothesis: w' p-tight, P(w) ∩ P(w') = ∅, sigma = 1) x_w = x_w' = 0 kills N and
   its reader g* (== 1): two further deaths. Contradiction in both cases. ∎
(K0) forced zeros: if every bad x has x_u = 0 for class-U points u in E, then O = W ∪ E satisfies the hypothesis of (E+).
(K-U+) ones + one zero: O as above but only c|_{Q_O} <= x_u0 (every bad x with x_O = 1 has x_u0 = 1), u0 p-tight (class U or T), u0 not
 in O ∪ {t}, t (resp. v) not in P(u0), no set through O contains u0 (so loss = loss(O) + d(u0)). Restriction x_O := 1, x_u0 := 0: dying
 gates: R_u0 ∪ G_u0 (d(u0)-sigma), g*, the m_O outputs, the |O| gates h_w, and, IF u0 IS OF CLASS U (then no cone gate reads x_u0
 except pair-gates of u0, so c and the extra reader are outside R_u0), c and one more by the (E+) argument:
   3 + m_O + |O| <= loss(O) (u0 of class U),   1 + m_O + |O| <= loss(O) (u0 of class T)   must hold.
 Proof of the extra death here: if c does not depend on x_O then c <= x_u0 on the whole cube and N2 at u0 alone fails (c or g* is a death
 outside R_u0 ∪ G_u0; g* restricts to x_t, t not in P(u0)). Otherwise a gate of cone ∪ {c} reads a Pi_O gate p; if only c does:
 c = ~p is the exception above; c = p|y is 1 on Q_O; c = p&y with y independent of x_O gives y <= x_u0 globally, hence c <= x_u0
 globally (N2 at u0 fails as before); y depending on x_O gives another reader. Distinctness as in section 7 (K-U): readers of x_u0
 are no outputs through O (u0 in no such set), no h_w; G_u0 gates restrict to variables x_u', u' not in O. ∎
(E) for |W| >= 2: the equality case of section 6 holds for every W all of whose points are of class U with P(w) ∩ B = {t}
 (c reads every p_{tw} it depends on; two of them: c = p&p' is 1 on Q, c = p|p' also; exactly one: as before).
Encoding: for class-U t with W ⊆ class U, and for V1 points with l = sigma+1: search O = W ∪ E (|E| <= 2; V1: |O| <= 3) and optional u0;
 exception hypothesis checked for all pair-sets {w,w'}, w in O, w' != t.

REFEREE (referee_asb.md, sections 0-4): rules a, s, b CORRECT, encodings match. One cosmetic gap in (A2), fix adopted here:
 "g1 dies (unread)" - g1 could survive as canonical representative of a LATER gate with the same restriction x_a|x_b. Let j0 be the
 lowest gate != g1 restricting to x_a|x_b under x_a' = x_b' = 0; j0 is a duplicate (dead), not c, not r, not in G, and not a reader
 x_a'|q of a'/b' (q would be g1, making j0 a reader of g1, i.e. c, or a lower such gate). So g1 or j0 is one more death; count stands.
 Referee caveat on rule s (Lean hypothesis must be "T_S(v) = {u} for some set S, line OR pair-set"): for the coordinator.

## 11. STATE after round 7 (cover2.py = cover2_round7.py, rules '245pqrasbn')
 rules / round       skel n=8 (4)  n=9 (50)  n=10 (1538) | pairs n=8 (262)  n=9 sample (2178) | base-15 open | base-16 open (n=8)
 245pqr                   4           36         734      |      58              354           |     33       |
 245pqrasb  (round 5)     4           37         792      |     130              713           |      4       |    30
 245pqrasbn (round 6)     4           38         799      |     141              729           |      0       |    24
 245pqrasbn (round 7)     4           38         799      |     204              778           |      0       |    14
 n=8 pairs by #pairs (round 7): 1:8/9 2:25/27 3:31/44 4:39/59 5:37/52 6:34/39 7:18/20 8:9/9 9:2/2 10:1/1.
 uncovered_after_round7.json (mkjson7.py; round-6 pickles kept in fr6/): 1317 minimal uncovered systems, by base
 16:14 17:106 18:343 19:438 20:231 21:124 22:44 23:15 25:2;  n=8 (complete): 16:14 17:23 18:14 19:6 20:1 (58 systems; was 121).
 Base 16: 14 systems, all n = 8 (1 with one pair-set, 12 with three, 1 with four); f16_explain.txt / f16_diag.txt (f16explain.py,
 f16diag.py) give per surviving class vector the first g* that is not excluded, the bad set (forced coordinates), loss and m_W.
 Remaining blockers (general statements still missing):
  (r1) an S-class point as the partner w of a U-type t (W = {w}, w of class S): h_w has slack, (E+) needs O inside class U because
       x_w must enter the cone only through pair-gates AND N2 at w must be tight for the exception c = ~p;
  (r2) V1 points with l = 3 (reader type unknown) as g*, and V1 points whose bad set has no forced coordinate (system
       {2367},{034},{056},{125},{146},{457}+{01},{02},{13}: 57 of 128 inputs bad);
  (r3) class-T points without pair-set (two OR-readers, no relative structure) inside N' when no Lemma-A user makes them a pseudo pair.

## 12. Referee on rule 'n' (referee_asb.md section N, refereed file cover2_round6.py): CORRECT; two write-up gaps, fixed here
 GAP 1 (section 6, N-O bonus): the parenthesis "it is OR-type, so it is not c" is unjustified; the valid argument is the one of
  section 9 "(N-O for class T)": c is no reader of x_w because an OR-reader is 1 on Q and an AND/NOT-reader of the p-tight w would have
  the reader h_t = x_t|c, which contradicts (T1) since the pair-gate {t,w} exists. Code unaffected.
 GAP 2 (section 9, (K2)): "c_v is no reader of x_u, as in (K')" does not transfer (only c_v <= x_u|x_w is known). Correct argument:
  AL gives c_v <= OR(S\v) for BOTH lines S of v, so c_v >= x_u (c_v = x_u|y, e.g. the pair-gate) would put u on both lines; c_v = x_u&y
  is an AND-reader of the p-tight u whose reader r_v is not of the form c_v|x_w' (v not in P(u)); c_v = ~x_u is 1 at 0. Same for w.
  Also in (E), AND-type: y = x_w would give c = (x_t|x_w)&x_w = x_w (not clean).
 NOT YET REFEREED: section 10 ((PG), (E+), (K0), (K-U+), (E) for |W| >= 2 [the referee checked the widened (E) himself: holds]) and the
  corresponding code in cover2_round7.py. The jump pairs n=8 141 -> 204 comes entirely from section 10, so it deserves a referee pass.

# ROUND 8 (base 16 continued; cover2_round7.py frozen as referee baseline; proofs written BEFORE encoding)
## 13. Four general lemmas (all inside rule 'n'; notation of sections 6, 10)
(L1) AND-READER OF A PAIR-GATE (sigma = 1). Let w, w' be pair-partners, both of class U, P(w) ∩ P(w') = ∅, pair-gate p = x_w|x_w'
 existing, and let t be an S-class point, t not in {w,w'}. Then the unique non-pair reader of x_t is NOT h_t = x_t & p.
 Proof. (PG): under x_w = x_w' = 0 at most one gate outside D = R_w ∪ G_w ∪ R_w' ∪ G_w' dies. h_t becomes 0: it is outside D (it reads
 x_t and the gate p; it restricts to a constant). h_t <= x_t is no output, so it has a reader q; q becomes a constant or its other
 input, so q dies; q is not h_t. q in G is impossible (q = h_t o y restricts under x_w := 0 to (x_t&x_w') o y', which is no variable).
 q in R_w: q reads x_w and the gate h_t, so q is the non-pair reader h_w = x_w | h_t (class U, (U2)); but w' is in W_w (p exists), so on
 Q_w we have p = 1 and c_w = h_t = x_t; (U3) demands c_w(z) = 0 at a point z of Q_w vanishing on a line L of w; if t is in W_w then
 x_t = 1 on Q_w, otherwise choose L not through t (w has >= 2 lines) and z_t = 1. Contradiction; same for w'. So q is a second death
 outside D. ∎
 USE: in the refined count for an S-class t (AND-type, c|_Q == 1) the gate c is counted unless it could be an output through W; a pair
 output x_w|x_b (w in W, b != t) is now excluded as well when w and b are of class U with P(w) ∩ P(b) = ∅ (sigma = 1).
(L2) (E+) / (K-U+) WITH S-CLASS POINTS IN O. Let O ⊆ U' = U ∪ S (t not in O; O ⊇ W_t for g* = h_t) with c|_{Q_O} == 0, g* OR-type
 (t of class U, or v in V1 with l(v) = sigma+1). Assume every S-class w in O has P(w) ∩ B ⊆ {t} and, as before, for class-U w in O and
 w2 in P(w) ∩ B, w2 != t: w2 p-tight, P(w) ∩ P(w2) = ∅, sigma = 1. Then
        3 + m_O + |O ∩ U| + min(1, |O ∩ S|)  <=  loss(O) - sigma       must hold.
 Proof. Counted deaths under x_O := 1: c, g*, m_O outputs, h_w (w in O ∩ U), ONE h_w for w in O ∩ S (section 6: it dies whatever its
 type, is no output; two of them could be the same gate). Extra death: as in (E+), a gate of cone ∪ {c} reads a pair-gate p touching O
 (x_w enters the cone only through pair-gates for every w in U'); all readers of p die; such a reader inside the cone is none of the
 counted gates (the h_w are not below g*; outputs: as in (E+)). If only c reads such gates: c = p|y, p&p' are 1 on Q_O; c = p&y gives
 another reader below y; c = ~p = N with p = x_w|x_w', w in O:
   w' != t: then w is of class U (an S-class w in O has no B-partner other than t) and (PG) applies as in (E+);
   w' = t (g* = h_t = x_t|N): suppose no further death is allowed (i.e. the inequality fails); then N is the ONLY reader of p (every
   reader of p dies). On the subcube x_w = 0, x_{W_t \ w} = 1 the readers of x_t are: pair-gates {t,w''}, w'' != w (== 1), p (= x_t,
   read only by N = ~x_t) and h_t = x_t|~x_t == 1. So x_t acts only through N, antitonically (all wires are monotone in (x,N)): no
   output can rise with x_t, but a line through t does at z = 1_{W_t \ w}. Contradiction.   [replaces "N2 at w", so w may be of class S]
 (K-U+) with such O: same proof; count 3 + m_O + |O ∩ U| + min(1,|O ∩ S|) <= loss(O) for u0 of class U. ∎
(L3) (K-U+) FOR u0 OF CLASS T: c IS COUNTED. In (K-U+) (c|_{Q_O} <= x_u0, t resp. v not in P(u0)) the gate c is no reader of x_u0 also
 when u0 is of class T: c = x_u0&y is an AND-reader of the p-tight u0 whose reader g* is not of the form c|x_w' with w' in P(u0) (T1);
 c = ~x_u0 likewise; c = x_u0|y >= x_u0 contradicts (U3) for t (a point z of Q_W vanishing on a line of t that avoids u0, with
 z_u0 = 1) resp. AL for v (c_v <= OR(S\v) on both lines of v). So the count for class T is 2 + m_O + |O ∩ U| + min(1,|O ∩ S|) <= loss(O)
 (the extra reader of (E+) may be a reader p o x_u0 of x_u0 and is NOT added for class T).  For O = ∅ (plain (K)) nothing changes. ∎
(L4) (K), (K2) FOR ANY V1 POINT (reader type unknown, l(v) >= sigma+2). If every bad x has x_u = 1, then on {x_u = 0} every x is good,
 so c_v == 0 there (OR-type) or c_v == 1 there (AND-type: c_v = 1 wherever some S\v vanishes, and c_v is a function of the key). In both
 cases x_u := 0 makes c_v constant and r_v equal to x_v: r_v is a death outside R_u ∪ G_u (v not in P(u)) for the p-tight u (class U or
 T). Contradiction: (K) holds for every V1 point.  (K2) for AND-type needs c_v outside R_u ∪ R_w as well: c_v(0) = 1 excludes x_u&y;
 ~x_u is excluded by (T1) (its reader r_v = x_v&N, v not in P(u)); c_v = x_u|y is excluded when u is of class U (below g* the only readers
 of x_u are pair-gates, and a pair-gate is 0 at 0). So (K2) is used for l(v) >= sigma+2 only when u and w are both of class U. ∎

## 14. Round 8: one correction to section 10 (K-U+), one relaxation, results
(L6) CORRECTION to (K-U+) (section 10; affects the frozen cover2_round7.py in principle, NOT in its numbers). The extra reader q of
 (E+) (a cone gate q = p o y, p a pair-gate {w,w'} touching O) was counted besides R_u0 ∪ G_u0 for u0 of class U. q is not in R_u0, but
 q in G_u0 was not excluded: q could be the lowest gate restricting to x_w' under x_u0 := 0 for a partner w' of u0 WITHOUT pair-gate,
 when w' is an endpoint of p, i.e. w' in P(u0) ∩ P(w), w in O (q = p&y with y >= x_w' ...). Corrected hypothesis for the "+1":
 P(u0) ∩ (O ∪ P(w)) = ∅ for every w in O ("far"); otherwise the count is 2 + m_O + n_O (c and g* only). CHECK: cover2_round7.py with
 only this correction applied gives the same numbers as section 11 (pairs n=8 204, n=9 778, skeleton 38 / 799): no result depended on it.
(L5) RELAXATION of (K-U+): u0 may lie on sets through O and may be a pair-partner of points of O (except: not a partner of an
 S-class point of O, whose AND-type h_w = x_w&x_u0 would be a reader of x_u0). Let j = #sets through u0 that meet O. Then
 loss = loss(O) + d(u0) - j, and among the d(u0)-sigma gates of R_u0 ∪ G_u0 at most j are already counted (each is then the output of one
 of these j sets: a reader of x_u0 that is an output is the output of a set through u0; a gate of G_u0 belonging to a partner w' in O is
 == 1 under x_O := 1 and can only coincide with the output of {u0,w'}; h_w reads one variable x_w and a gate). So the inequality
 X + m_O + n_O <= loss(O) is unchanged, X = 3 if u0 is of class U and far, else 2.  ∎
Encoding (cover2.py = cover2_round8.py): (L1) cg condition; (L2) O inside U' with n_O = |O ∩ U| + min(1,|O ∩ S|) and the S-class exception
 hypothesis; (L3) X = 2 for class T; (L4) (K)/(K2) for all V1 points; (L5), (L6).
RESULTS (rules 245pqrasbn, round 8):  skeleton n=8/9/10: 4, 38, 799 (unchanged);  pairs n=8: 206 (204);  n=9 sample: 806 (778);
 base 15: 0 open;  base 16: 13 open (14).  uncovered_after_round8.json (mkjson8.py; round-7 pickles in fr7/): 1286 systems, by base
 16:13 17:96 18:331 19:433 20:228 21:124 22:44 23:15 25:2;  n=8 (complete): 16:13 17:22 18:14 19:6 20:1.
 n=8 pairs by #pairs: 1:8/9 2:25/27 3:31/44 4:40/59 5:38/52 6:34/39 7:18/20 8:9/9 9:2/2 10:1/1.
WHAT BLOCKS THE 13 (f16_diag.txt, regenerated): in 25 of 26 failing (class vector, g*) the bottom gate is h_t and c|_Q <= x_u0 x_u1 ..
 with ALL forced points of class T (no pair-gate structure) or partners of t; the cascade count is short by exactly one
 (2 + m_O + n_O = loss(O)), because the surcharge reader q of (E+) may be a reader q = x_u0 | p of the class-T point u0.
 Open lemma that would close most of them: "a strictly tight point u0 (two OR-readers, no pair-set) has no reader x_u0 | p with p a
 pair-gate"; equivalently handle readers of class-T points as bottom gates (then (a) x_u|x_s feeders without Lemma-A user and
 (b) x_u | phi(pair-gates) must be excluded or classified). Also open: S-class t as bottom gate with forced coordinates (AND-type gives
 no surcharge), |W| = 2 with one S-class partner having a second B-partner.
