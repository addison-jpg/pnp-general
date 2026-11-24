# qg-d2 (session_01GmnDhgAdyDijthBgZgJFWn): no-mixed-points MergeFrac LP test (scaffold helper, coord assignment 08:00)
Corpus: front's allcirc + extra + chist cxU* + cxrb(2..6): 2580 one-NOT circuits, 10,691 sets, n = 4..20; merge classes from
mg.merges, LP = pb.maxload (both imported). Code + per-circuit JSON: branch nomixed-951, work/nomixed951/ (375e628).
World of a zero point z of S: 0 if h(z) = 1; 1 if h(z + e_u) = 0 for all u in S; else mixed.
1. No-mixed LP <= 1 always? REFUTED (checked): w9/fc/cxe3.json (n = 7, 5 sets of size 3): full LP 1.0, no-mixed LP 3.0.
   h >= x0; the 3 sets containing x0 have no world-1 point, and their only non-mixed zero point is one world-0 minterm
   whose merge class contains gate 26 = OR(x0, gate 25) for all three. Optimal dual: price 1 on gate 26.
   Restriction also raises the optimum on 17 circuits (cxrb, cxU6, cxU8: 0.55-0.61 -> 1.0), still <= 1.
2. Variant (world 0 = minterms of h off S, world 1 = {z = 0}): fails on 4: cxe3 3.0, w9/fc/cxT2 (n = 9) 3.0,
   w9/fc/cxT4 (n = 15) 3.0, chk/c.jsonl:264 2.0. cxT2/cxT4: h >= x0, x1, x2, every set holds two of them; one gate
   (22 / 38) lies in the merge class of every set's only minterm point.
3. Split sets (only mixed points): 2555 of 10,691 sets, in 2326 of 2580 circuits. PROVED (monotonicity of h) + CHECKED
   on every set with n <= 11: S is split <=> h(e_u) = 1 for some u in S and h(1_{V \ S}) = 0.
4. Refined statement, CHECKED on all 2580: sets S with some u in S, h(e_u) = 1 (they have no world-1 point) keep all
   zero points; every other set uses world-0 and world-1 points only => LP <= 1 (max 1.0).
   Equivalently: when h >= x_u for no u in any set, the no-mixed LP is <= 1 (164 such circuits, incl. every cxU*, cxrb,
   cxP*, tw hard case). Caveat: in the small corpus 7501 of 10,691 sets have such a u, so the check is thin there.
Question for front: does a MinCE lemma exclude h >= x_u for u in a set (h without singleton minterms inside any S)?
If so, item 4 says MergeFrac at a MinCE needs no mixed points: two monotone circuits C_0, C_1 plus cross-world conflicts.

## Round 2 (coord follow-up 08:13; 08:17 UTC). Code + per-circuit JSON: branch nomixed-951 f35819c, work/nomixed951/
Corpus: front's (above) + scaffold's data-corpora 2aa9856 (all jsonl + the SAT lines of hard4/*.log), deduplicated:
34,064 one-NOT circuits, 168,245 sets, 0 Lemma-M anomalies. Full MergeFrac LP <= 1 on all (max 1.0).
(1) Refined no-mixed LP (mixed points only for sets S with some u in S, h(e_u) = 1): <= 1 on ALL 34,064 (max 1.0),
    incl. the 162 circuits with a 4+-set. Plain no-mixed LP: 6 failures; smallest dc:ess/ess_k4e_clean.jsonl:2951
    (n = 4, L = 2.0, 4 of 5 sets hold an x_u with h >= x_u, so it is no failure of the refined form):
    {"n":4,"sets":[[0,1],[0,2],[0,3],[1,2],[1,3]],"gates":[["and",0,3],["or",0,3],["or",0,2],["and",1,6],["or",1,4],["not",5],["or",3,7],["or",1,2],["or",0,1],["and",9,12],["or",10,13]],"outs":[12,6,5,11,14]}
    WORLD-1 DEFINITION MATTERS: with scaffold's world 1 (h(z | S) = 0, stricter than h(z + e_u) = 0 for each u) the
    refined LP FAILS on 1043 circuits (max 4.0), also when no set holds such a u. Smallest dc:fixh/fixh16_clean.jsonl:6
    (n = 4, h = (x0|x1)(x2|x3), L = 2.0 on gate 5, the class of the world-0 minterm of two sets):
    {"n":4,"sets":[[0,1],[0,2],[0,3],[1,2],[1,3],[2,3]],"gates":[["and",2,3],["or",1,4],["or",0,5],["or",2,3],["and",6,7],["not",8],["or",3,9],["or",1,9],["and",10,11],["or",5,8],["and",12,13],["or",2,14],["or",1,3],["or",0,2],["or",0,1],["or",0,3]],"outs":[18,17,19,15,16,7]}
    So the target is: world 1 = h(z + e_u) = 0 for every u in S (coord's / board-reset's wording), not h(z | S) = 0.
    Test 2 (minterms of h off S, plus z = 0): fails on 61 (z = 0 only when world 1) / 149 (z = 0 always); max 3.0 / 2.0.
(2) Essential + clean (front's lib.py definitions; s counts the NOT): 19,908 circuits; min s - base = 4.
    s - base <= 4: 842 circuits, ALL have a set holding u with h >= x_u (0 without). s - base >= 5: 14,615 with, 4,451
    without; the first circuits without such u appear at s - base = 5 (1), 6 (52), 7 (497), 10 (3892).
    => in this corpus every near-optimal essential circuit has a heavy unit inside a set: the refined form gives no
    mixed-point-free case there; the heavy-unit sets (front: confined to |S| >= 4 at a MinCE) are the whole question.
(3) Circuits with no such u: 9,000; cross-world gates (merge gate at a world-0 point of one set and at a world-1
    point of another) in 162, N-dependent ones in 89. Range of pi(cross) over ALL optimal duals:
    full LP: forced > 0 in 8 circuits only (dc:ess/ess_k4e_clean.jsonl:5606..5617, all with L* = 0.75 < 1, cross gate
    not N-dependent); N-dependent cross-world gates: max over all optimal duals = 0 in every circuit (agrees with
    scaffold's 0). No-mixed LP: some optimal dual has pi(cross) = 0 in every circuit (max up to 1.0 in 24).

## Round 3: front's heavy split rule (coord request 08:23; front-match 111f0ca w9/heavy/split.py BASE=zS, imported unchanged; 08:27 UTC)
Corpus as round 2 (34,064, dedup; 6 with n > 12 skipped by split.py). Code + JSON: nomixed-951 bdd45d3, heavysplit.py, out_heavy.jsonl.gz.
39,168 (circuit, heavy v) pairs in 25,063 circuits. Full MergeFrac LP <= 1 on every circuit below.
- Heavy split LP (B pinned at own z_{S_b}, star of v free): FAILS on 320 pairs / 320 circuits (L = 2.0), all ESSENTIAL,
  313 CLEAN, from scaffold's ess (312) and tri (8) corpora; front's 4,764 pairs were all <= 1 and are again <= 1 here.
  316 of the 320 are B-B collisions (pinned load already 2); 4 are star-only (pinned load 1, star cannot avoid it; all 4
  non-clean: tri_all 983-985, 5322). Integral star-at-0: > 1 on 657 pairs (max 3).
- CAVEAT IS FALSE ON CLEAN CIRCUITS: merge sets of two pinned sets at their OWN bases z_{S_b}, z_{S_b'} intersect in 316
  circuits, 313 of them clean (all sets, not only pinned ones: 7,215 circuits, 6,670 clean). Smallest, essential + clean,
  s - base = 5, K4-e: dc:ess/ess_k4e_clean.jsonl:248, v = 2, pinned sets {0,3} and {1,3} collide:
  {"n":4,"sets":[[0,1],[0,2],[0,3],[1,2],[1,3]],"gates":[["or",0,1],["or",0,2],["not",2],["or",0,6],["and",1,7],["and",5,8],["or",3,9],["or",0,10],["or",1,3],["or",2,8]],"outs":[4,5,11,13,12]}
- With a 4+-set: no failure (141 such circuits with a heavy point in data-corpora, 293 pairs, max 1.0; every failure above
  has only 2- and 3-sets). So the rule may still hold where front needs it (heavy points of a MinCE lie on |S| >= 4 sets),
  but "B pinned" cannot be justified by cleanliness alone: a proof needs MinCE minimality or |S| >= 4, or must let B float.

## Round 4: front's heavy split v2 and its two menu questions (front 08:29; split3.py at front-match b20869b; 08:33 UTC)
Code + JSON: nomixed-951 1bada7b, heavyv2.py (imports front's lp, merges_at, zeropoints), out_heavyv2.jsonl.gz.
Same 34,064 circuits, 39,168 (circuit, heavy v) pairs. B = sets without v, A = star of v.
- v2 (B over zero points with z_v = 1, A free): <= 1 on ALL 39,168 pairs (agrees with front).
- Q1: B over {e_v, z_{S_b}} only (A free): <= 1 on ALL 39,168 pairs. B over {e_v} only: FAILS on 210 pairs / 196
  circuits (194 essential, 172 clean, 1 with a 4+-set), max 2.0; smallest essential + clean dc:ess/ess_k4e_clean.jsonl:461
  (n = 4, v = 2, s - base = 5): {"n":4,"sets":[[0,1],[0,2],[0,3],[1,2],[1,3]],"gates":[["and",0,2],["or",3,4],["or",1,5],["not",2],["or",0,2],["and",7,8],["or",1,3],["or",5,9],["or",0,1],["or",1,2]],"outs":[12,8,11,13,10]}
  => Case II menu for B: two points per set, e_v and the set's own z_{S_b}, suffice on all data.
- Q2: A over its world-0 points only (h(z) = 1; a star set with none keeps all points), B as v2: FAILS on 13 pairs /
  8 circuits, all essential + clean, none with a 4+-set, max 3.0 (w9/fc/cxe3 v = 0); smallest dc:ess/ess_k4e_clean.jsonl:2951
  (n = 4, v = 0, L = 2.0; the round-2 circuit). Same with B as Q1 (13 pairs). Also: in 35,045 of the 39,168 pairs some star
  set has NO world-0 point at all (only mixed points: h(1_{V \ S}) = 0). => the star needs mixed points.
- Circuits with a 4+-set (318 pairs): v2, Q1 {e_v, z_{S_b}}, Q2 all <= 1; only B = {e_v} fails (1 pair).
