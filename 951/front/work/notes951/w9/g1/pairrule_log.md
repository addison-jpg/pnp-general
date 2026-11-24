# pairrule_log.md — round 4 of G1: pair-set rules in the coverage checker (restart-safe log)
Files (all in w9/g1/): cover2.py (checker, rules '2','4','5' + NEW 'p','q','r'; round-2 version kept as cover2_round2_backup.py),
pairrun.py (pair-core data: `gen N` rebuilds EXACTLY the paircores.py list -> pairsys{8,9}.pkl; `eval` = tables by #pairs),
frontier.py (collects minimal uncovered systems met in the recursion), mkjson.py (-> uncovered_after_pairs.json),
qexample.py (finds systems where q is decisive), satcheck14.py (SAT consistency check).
Conventions as in g1_fable.md: minimal counterexample (all point deletions covered), clean minimum circuit, sigma = base - s >= 1,
l(u) = #lines (|S| >= 3) through u, p(u) = #pair-sets {u,w} through u, P(u) = pair-partners, d = l + p.

## 0. Heredity (PROVED; justifies every multi-point restriction x_Z := 0 used by rules 4, 5, q)
bound(F) => bound(F - b): from a circuit for F - b add o_S := o_{S-b} | x_b (one gate per S through b; for S-b = {w} the gate x_w|x_b),
so s(F) <= s(F-b) + deg(b) and base(F) = base(F-b) + deg(b). Same for deleting a whole set S (cost |S|-1). Hence "all single point
deletions covered" gives the bound for EVERY F - Z, as G1.7 needs (covered() establishes only single deletions recursively).

## 1. Rule 'p' = PAIR-N2 (G1.9 in counting form). PROVED, encoded.
Statement. For every point u:   nonpair(u) + kL(u) <= l(u) - sigma   and   nonpair(u) >= 1,
 nonpair(u) = #readers of x_u that are not a pair-gate x_u|x_w (w in P(u)); kL(u) = #V1 points v that use u as singleton through a
 LINE (S ∩ A_j(v) \ v = {u}, |S| >= 3).
Proof. Under x_u := 0 (N2: dead0(u) <= d(u) - sigma) the following gates die:
 (a) all readers of x_u (|R_u| = nonpair(u) + pg(u), pg = #existing pair-gates x_u|x_w);
 (b) for every w in P(u) the LOWEST gate g_w whose restriction is x_w (exists: o_{uw} restricts to x_w). If g_w reads x_u then
     g_w = x_u | c (x_u & c -> 0, ~x_u -> 1, x_u o x_u -> 0) with c restricting to x_w; c is not a gate (it would be a lower g_w), so
     c = x_w: g_w is the pair-gate. So the p(u) - pg(u) partners without pair-gate give non-reader deaths;
 (c) r_v for every line-singleton user v (G1.3 (ii): c_v becomes constant, r_v becomes x_v); r_v is not a reader of x_u (c_v is a gate).
 Distinct: g_w restricts to x_w, r_v to x_v with v ∉ P(u) (v shares a line with u). Total >= nonpair + pg + (p - pg) + kL.
 nonpair(u) >= 1 (l(u) >= 1): if all readers are pair-gates x_u|x_w, w in W, take z = 1_W: toggling x_u changes no wire, but
 OR(L) for a line L through u (L ∩ W = ∅) changes.  A pair-gate x_u|x_w is impossible if u or w is in V1 (P2: a line through that
 point avoids the other one).
Consequences encoded (cover2.py, letter 'p'):
 * sigma <= min_u l(u) - 1 (every point, also every V1 point, needs l(u) >= 1 + sigma: "count lines, not sets");
 * u in V1: capL(u) = l(u) - sigma - 1 line-singleton users; u in B (readers = nonpair + pg >= 2, pg <= pB(u) = |P(u) ∩ B|):
   capL(u) = l(u) - sigma - 2 + min(1, pB(u)); a scenario with some capL(u) < 0 is discarded;
 * singleton uses through PAIR-sets are free (the dying r_v is the g_v of (b), already counted).
 This implies the old capacity (ii') (kL + kP <= d - sigma - 2 resp. d - sigma - 1), so it is a strict strengthening.
Equality case = G1.9: tight u (readers = d - sigma) forces pg = p (all pair-gates exist), kL = 0, nonpair = l - sigma; a V1 point
 with a pair-set is never tight; a tight point has no V1 pair-partner.

## 2. Rule 'q' (G1.7 step 1 + G1.9). PROVED, encoded.
Setting: sigma = 1, v in V1 of degree 2 (tight, OR-reader r = x_v|c), T_i = {a,b} a tight pair (both known tight), T_o = the T of
v's other set; a in B with d(a) = 3 and exactly one pair-set {a,w}.
Claim: w ∈ T_o.  Proof: G1.7 step 1 (valid with pairs: pair outputs of a,b are among their readers by G1.9, loss = d(a)+d(b))
 gives g1 = x_a|x_b read only by c = g1 & y, c <= OR(T_o) pointwise (c depends on A_j only).  G1.9: x_a|x_w exists.
 readers(a) = d(a) - 1 = 2 = {x_a|x_w, g1}.  Compare z = e_w and z' = e_w + e_a: x_a|x_w = 1 at both, g1 goes 0 -> 1 (b != w),
 its only reader c is <= OR(T_o)(z) = OR(T_o)(z') = [w ∈ T_o] (a ∉ T_o). If w ∉ T_o no other wire changes, but
 OR(S_i)(z) = 0 != 1 = OR(S_i)(z') (w ∉ S_i, S_i a line through a) and o_{S_i} is not x_a or g1.  Contradiction.
 (With p(a) = 0 this is G1.7 step 3 = rule 5; rule q is its one-pair-set version.)
Hand check (qexample.py): {034},{012},{357},{2467},{156} + pairs {14},{06},{05},{13}: only 245p scenario sigma=1, B={0,1,3,4,5,6};
 order 7-first dies by rule 4 (both T tight pairs), order 2,7: v=7, T_1={3,5}, T_o={2,4,6}, P(3)={1} ∉ T_o -> killed by q. Verified
 by hand: readers(3) = {x3|x1, x3|x5}, c_7 <= x2|x4|x6; z = e_1 vs e_1+e_3 moves only x3|x5 and OR(357).

## 2b. Rule 'r' (c-death + relative absorbing lemma). PROVED, encoded (needs 'p').
U(u) = V1 points v using u as singleton through a line or a pair-set S0(v); k(u) = |U(u)|. Under x_u := 0 also c_v dies (constant);
it restricts to a constant, so it is distinct from every death counted in rule p; it is a reader of x_u or ONE MORE death.
 (R2) u ∈ V1 => c_v != r_u.  OR-type r_v: c_v <= x_u, so c_v = r_u forces r_u = x_u & c_u; AL gives c_u(0) = 1, so
      c_v(e_u) = r_u(e_u) = c_u(0) = 1, but c_v <= OR(T_S'(v)) for v's other set S' and u ∉ S'. AND-type r_v: c_v = 1 on {x_u = 0},
      impossible for r_u (x_u&c_u is 0 there; x_u|c_u needs c_u(0) = 1 against AL). Hence k(u) >= 1 => 1 + kL(u) + 1 <= l(u) - sigma
      (strengthens G1.3 (ii) for V1 singletons from d >= 2+sigma to d >= 3+sigma).
 (R3) u ∈ B, every c_v (v ∈ U(u)) a reader of x_u, nonpair(u) = 1: c_v <= x_u makes c_v = x_u & y (OR-type r_v) or N = ~x_u
      (AND-type r_v), not a pair-gate, so every c_v = h_u, the unique non-pair reader. W = partners with pair-gate, Q = {x_W = 1}.
      h_u = N: on Q every wire is monotone in (x, N) and x_u enters only through N: toggling x_u up cannot raise o_L (L ∩ W = ∅).
      h_u = x_u & y: y is x_u-free on Q; at z = 1_W toggling x_u must move h_u (OR(L)(z) = 0), so y(z) = 1, h_u(z + e_u) = 1, hence
      c_v(z + e_u) = 1 <= OR(T_S'(v))(z + e_u): for every other set S' of v, T_S'(v) ∩ W != ∅ (checked with W ⊆ P(u) ∩ B).
 Encoding: if k(u) >= 1: u ∈ V1: kL(u) <= l(u) - sigma - 2;
           u ∈ B: kL(u) <= l(u) - sigma - 2, or [pB(u) >= 1, kL(u) <= l(u) - sigma - 1 and every user v satisfies (R3)]
           (the mode "c_v extra death" gives kL <= l - sigma - 1 - max(1, 2-pB) and is dominated).
 Effect is small (n=9 pair sample +6), but it is sound and applies to skeleton cores too.

## 3. Soundness of the DFS itself (re-derived; round-2 greedy is SOUND, now with proof)
Round-2 cover2.dfs places every "free" V1 point (status = no consumption) greedily. Exchange argument: if some valid order pi
exists from state P, moving a free v to the front only enlarges the T's of the points placed before v in pi; that removes singleton
and tight-pair consumption and only helps rules q and r. The ONLY possible harm: a line-singleton T = {u} of a later point y becomes
{u, v} and is then a tight pair containing the V1 point v (forbidden by rule 4). That needs u tight; but a singleton use of a tight u
is already rejected by (ii) (cap1(u) = 0; under 'p' capL(u) <= 0), so it does not occur in pi. Hence greedy is sound.
cover2.py keeps three modes: greedy='none' (pure DFS with memo; DEFAULT, fast enough), 'safe' (greedy except in the (impossible)
harmful configuration), 'old' (round-2). CHECKED: identical covered sets on every data set below (counts equal; greedy can only
cover more), so the round-2 numbers stand.
Also not encoded / not encodable:
 * G1.8 relative AL, monotone case: needs "c2 is not downstream of N", which the scenario abstraction (sigma, B, order, capacities)
   does not see; the non-monotone branch gives no death (G1.8 "general case"), so a case split excludes nothing. Not encoded.
 * G1.10 (N3 route), G1.11 (H+), (Psi1): conjectures or no rule. Tight T of size >= 3: no rule (G1 round 3). Not encoded.

## 4. COVERAGE TABLES (pure DFS; "before" = round-2 rules 245)
Skeleton cores (all):
 rules            n=8 (4)   n=9 (50)   n=10 (1538)
 (i),(ii)           3         30          516
 2                  3         30          523
 24                 4         35          603
 245  [before]      4         36          657
 245p               4         36          657
 245pq              4         36          734     (+77: deletions = 9-point systems with pairs become covered)
 245pqr [after]     4         36          734
Cores with pair-sets (n=8: all 262 up to iso; n=9: the random sample of paircores.py, 2178 systems, rebuilt identically):
 rules            n=8 (262)   n=9 sample (2178)
 245  [before]       37            202
 245p                49            237
 245pq               58            348
 245pqr [after]      58            354
 by #pairs (covered/total), n=8:  245: 1:8/9 2:14/27 3:14/44 4:1/59 5:0/52 6:0/39 7:0/20 8:0/9 9:0/2 10:0/1
                                  245pqr: 1:8/9 2:15/27 3:18/44 4:16/59 5:1/52, >=6: 0
 by #pairs, n=9 sample:           245: 1:63/151 2:86/439 3:46/540 4:6/499 5:1/330 >=6:0/219
                                  245p: 63, 93, 60, 16, 4, 1(6)   245pq: 65, 135, 91, 42, 13, 2(6)
                                  245pqr: 1:66/151 2:138/439 3:93/540 4:42/499 5:13/330 6:2/137 >=7: 0/82
Times: every run < 25 s.

## 5. FRONTIER = minimal uncovered systems (uncovered, no R0 point, not small3, all point deletions covered)
uncovered_after_pairs.json: 1279 systems (canonical labels), sorted by base, n, #pairs; per system: sets, degrees, lines per point,
surviving scenarios (sigma, B) under 245pqr, sources, whether it was already frontier under 245.
 count by base  after (245pqr): 15:33 16:71 17:322 18:348 19:272 20:138 21:65 22:22 23:6 25:2
                before (245):   14:4 15:49 16:88 17:448 18:337 19:223 20:130 21:55 22:22 23:6 25:2
No cores exist on <= 7 points (enumcores: n=6,7 -> 0), so every frontier system has >= 8 points and the n=8 part of the list is
COMPLETE (n=8 after: 15:33 16:61 17:58 18:33 19:15 20:3 21:1; before: 14:4 15:49 16:62 ...). The four base-14 systems of round 2 are
now covered (all by rule p, e.g. {2367},{034},{056},{124},{157}+{01},{02},{13}: sigma=1, all l=2, B={0,1,2,3} has capL = 0 everywhere,
so 5 and 6 each need the other placed first). 20 round-2 frontier systems of base <= 15 are gone.
Smallest uncovered now: base 15, 33 systems, all n = 8 with 2 (10), 3 (6) or 4 (17) pair-sets, <= 3 surviving scenarios each;
 EVERY surviving scenario of the whole frontier (4332) has sigma = 1. Examples:
 #0 {0567},{034},{126},{145},{235},{247} + {01},{02}        scenario B = {0,1,2,4,5}
 #1 {0567},{034},{135},{146},{237},{245} + {01},{02}        B = {0,1,2,3,4,5}
 #3 {2367},{016},{035},{125},{147},{456} + {02},{13}        B = {0,1,2,3,5,6}; order 7 (uses 1 as singleton, W-cond ok via 3), 4
Skeleton (no pair) frontier: 45 systems, smallest = the n=9 core of round 2 (base 17, rank 162), then base-19 10-point cores.

## 6. What still blocks (the surviving scenarios)
Typical survivor (#3 above): sigma = 1, a degree-4 B point u (l = 3, one B pair-partner w) used once as line-singleton; rule r forces
its unique non-pair reader h_u = x_u & y = c_v with y = 1 on {x_w = 1, OR(S\u) = 0}; consistent as long as w lies in v's other T.
Closing it needs either a second death under x_w := 1 (N3 has large slack) or a relative peeling lemma (open, G1.8).

## 7. Consistency check / reproduction
SAT (satcheck14.py: base-14 system {2367},{034},{056},{124},{157}+{01},{02},{13}, one NOT, s = 13, h(0)=0 NOT assumed): did not
finish inside the 5-minute budget -> inconclusive (no counter-evidence). Rule soundness rests on the proofs above.
Reproduce: python3 cover2.py none -,2,24,245,245p,245pq,245pqr 8 9 10 ; python3 pairrun.py gen 8|9 ;
 python3 pairrun.py eval 8|9 none 245,245p,245pq,245pqr ; python3 frontier.py RULES skel8|skel9|skel10|pair8|pair9 ; python3 mkjson.py
 (all runs < 45 s). paircores.py still works and now uses the default rules '245pqr'.
