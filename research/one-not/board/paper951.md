# One negation and Boolean sums: working draft

Living draft for the owner (addison-jpg). coord keeps it current. Status words are used strictly:
**proved in Lean** (compiles, no sorry, only propext / Classical.choice / Quot.sound),
**proved on paper** (written argument, not machine-checked), **checked on N cases** (computer search),
**open**, **refuted**.

## 1. The question

Let S_1, ..., S_m be subsets of n input variables, each of size at least 2, any two sharing at most one
variable ((1,1)-disjoint Boolean sums). A circuit of fan-in-two AND, OR and NOT gates with **at most one NOT
gate** computes, for every i, the OR of the variables in S_i.

**Claim (951).** Such a circuit has at least sum_i (|S_i| - 1) gates.

That is exactly the size of the obvious circuit with no NOT gate. So the claim says one NOT gate saves nothing.
- Without NOT gates the bound is classical: Wegener, *The Complexity of Boolean Functions*, section 6.6.
  Cite Wegener section 6.6, Theorem 6.2 / Corollary 6.1 (verified against the book by the tractability session);
  attributed there to Mehlhorn (1979), with related work by Nechiporuk and Pippenger.
- With unboundedly many NOT gates, no comparable bound is known.
- Status of 951: **open, and apparently novel.** Literature pass (tractability, full texts of Wegener; Jukna-Lingas,
  ECCC TR18-154; arXiv 1708.03486): not known, not implied, not refuted. Jukna-Lingas covers only negated inputs
  and loses a multiplicative factor; Wegener's proof needs exact sums. Details: agents/tractability-lit.md.
- **Partial bound (proved in Lean, `partial_bound`, PartialBound.lean, coord-951 2cc4b77; idea: tractability).**
  If the NOT reads a wire h and some variable k satisfies: whenever x_k = 1, h covers every output whose set avoids k,
  then size >= 1 + sum over sets not containing k of (|S|-1). Holds e.g. when x_k alone switches h on.
  So in those cases one NOT saves at most the contribution of the sets through one point.
- Corollary (952): the line-ORs of a projective plane of order q need at least q(q^2+q+1) gates with one NOT.

## 2. What is proved in Lean
Everything is on branch `coord-951` of the private repo, modules in `proofs/main/PEqualNP/W951/` (map: `work/W951.md`).

| Result | Module | Status |
|---|---|---|
| Full theorem 951 from one open lemma `hard_case_core` | Eval ... Main (front, split by coord) | proved in Lean except that lemma |
| Monotone-style count per set, cone-restricted counting, special cases (dead NOT, at most one hard set, removable NOT) | Count, Cone, Cases, Cleanup | proved in Lean |
| Two-World reduction: if no set is "DD", the bound holds (any number of NOT gates) | TwoWorld (coord; math by front's agent) | proved in Lean |
| The open statement shrinks to the hard case with a DD set (`HardCaseDD`) | Hard | proved in Lean |
| Frame Lemma (counting with general test points) | Frame (front) | proved in Lean |
| Gap-G, matching (MatchG), fractional matching (FracMatch) each imply the hard case | GapG, MatchG, FracMatch, HardFrac (front) | proved in Lean |
| Explicit union-find merges; per test system, at least \|S\|-1 merges inside the counted gates; a pair of blocks is joined at most once | MergeRun, MergeRunT (coord) | proved in Lean |
| 952 (projective planes) follows from 951 | Plane (coord) | proved in Lean |
| Partial bound: 1 + sum over sets avoiding k, under the covering hypothesis on k | PartialBound (coord, Fable agent) | proved in Lean |
| T1: 951 for all \|S\| <= 3; s >= sum min(\|S\|-1, 2) in general | Small3 (front, Fable) | proved in Lean |
| Open statement shrinks to HardCaseDD4 (some set of size >= 4) | Hard | proved in Lean |
| G1: a minimal counterexample has two points of degree >= 3 (absorbing lemma) | Absorb, Bottom (front, Fable) | proved in Lean |
| Theorem E: easy sets have >= \|S\|-1 private gates; a minimal counterexample has a HARD set of size >= 4 | EasySets (front, Fable) | proved in Lean |
| R0' point deletion; open statement shrinks to HardCaseCore (every point in >= 2 sets of size >= 3) | Restrict, Dead, Lower, Core (front) | proved in Lean |
| G1.5 (a tight point has only OR readers; the NOT never reads it), G1.3 peeling (single-reader points: the reader is x_v o c with c earlier; x_u := 0 kills r_v and c_v), G1.6 capacity with the kL term, rule 's' (kL(u) <= l(u) - sigma - 2, any sigma) | Peel, RuleS (coord, Fable; math: front) | proved in Lean |
| Conjecture FJ (front's Fable R: for EVERY monotone h, lifted interval circuits need >= base gates) implies 951 and even s >= base + 1; FJ holds for h = x_p | LiftFJ (coord, Fable) | proved in Lean (FJ itself open) |
| Exact G1.9 (tight point: unique pair gates, kL = 0, nonpair = l - sigma); G1.3 (iii) two-point form; degree corollaries deg >= 3+sigma (B) / 2+sigma (V1); multi-point N2 | Peel2 (coord, Fable) | proved in Lean |
| Lemma K (scaffold): s >= 1 + \|U\| + base - ex, ex = sum (\|S\|-3)^+; ex <= 1 => 951; a minimal counterexample has ex >= 2 | LemmaK (session dZb2E; refereed by dwV8p) | proved in Lean |
| MergeFrac chain: Lemma M (exactly \|S\|-1 merge gates at every zero point), load identity, MergeFrac <=> MergePrice (LP duality), single-price case, cover-price form, Theorem F; world split (merge sets at world-b points = those of the monotone circuit C_b) | MergeFrac, MergeWorld (tractability, cTAHG, dRKvz; Fable J levels 1-3) | proved in Lean; the open target is MergePrice for a minimal counterexample |
| Lifted ClassFrac => bound: if the lifted circuit has, for each set, a convex combination of S2.1 configurations with every gate's total load <= 1, then s >= base + 1; so `no_minCE` follows from 'every minimal counterexample admits a lifted ClassFrac' (the LP data: L* <= 1 on all 2558 circuits) | LiftFrac (coord, Fable) | proved in Lean (the hypothesis is the open part) |
| Pair lemma G1.9 and rule 'p' (front): in a minimal counterexample, a tight point u with a 2-set {u,w} forces the gate x_u OR x_w; nonpair(u) + p(u) <= #gates dying under x_u := 0; every point lies in >= 1 + sigma sets of size >= 3 (sigma = base - s); heredity s(F) <= s(F - b) + deg(b) | PairLemma, Heredity (coord, Opus then Fable) | proved in Lean (without the kL term) |
| Lifted monotone form: replacing the NOT by a fresh input y gives a monotone circuit with one gate fewer whose outputs lie in [o_w AND (y OR h), o_w OR (y AND h)]; conversely; so 951 is EQUIVALENT to a monotone lower bound for these interval Boolean sums (`LiftedBound <-> OneNotBound`) | Lift, LiftBound (coord, Opus then Fable; math: front's Fable S) | proved in Lean |
| Lifted counting S2.1 (join-closed zero set Z + k atoms, condition (L) => >= k-1 OR merge gates vanishing on Z) and pair budget S2.2 (blocked atoms; |P(a\|b)| <= 1 or |P(b\|a)| <= 1 => classes disjoint), for any monotone circuit | LiftCount (coord, Opus then Fable; math: front's Fable S) | proved in Lean |
| Assembly: per-set classes of size >= \|S\|-1, pairwise disjoint => sum <= size; OR-only circuits with own base points | Kernel/MultiBase (tractability) | proved in Lean |
| Theorem P (payment lemma for h = x_a or x_b under H*) | Pay, PayDraft (coord) | facts F1-F3, Lemmas 1-3 and the counting step proved in Lean; Lemmas 4-6 open in a draft; parked |

**Sandwich fact used throughout:** replacing every NOT gate by constant false (C0) or constant true (C1) gives
C0 <= real circuit <= C1 on every wire.

## 3. The open core
- **Reformulation (front, Fable S; proved on paper, SORRY_DISSECTION §11):** 951 is equivalent to a MONOTONE lower bound
  for partial (don't-care) Boolean sums, in a lifted form. This moves the problem fully into the monotone world.
- **G1 (front; G1.1 and G1.2 PROVED IN LEAN: MinCE.no_minCE_deg2, MinCE.two_deg3):** G1.1: 951 holds for every system in which each point
  lies in at most 2 sets (first-gate absorbing lemma + point-deletion count). G1.2: a minimal counterexample has at least
  two multi-reader points; s >= base if at most one point has degree >= 3. G1.3 peeling cascade. Front's cover.py: these
  cover c11, c12, the n = 8 base-13 core, small n = 9/10 cores, and the 4x3 / 4x4 grids.
- **Equivalent open target (Lean, LiftFrac.lean):** it suffices to show that every minimal counterexample admits a lifted ClassFrac
  (`no_minCE_of_liftClassFrac`). Whole-class S-repay is refuted; the missing step is open for cyclic / core systems.
- **Single open statement (Lean, MinCE.lean):** `no_minCE`: there is no MINIMAL counterexample (minimal in gate count,
  then in sum of set sizes). Every earlier hypothesis is a proved consequence of minimality (MinCE.clean, live, essential,
  h0, twoHardN, noThmX, DD, has4, core), plus new minimality facts: output deletion (outDel) and the point-deletion
  count (deadBound).
- **R0' (front, Fable E/F; PROVED IN LEAN: Restrict, Dead, Lower, Core):** deleting a point
  v (x_v := 0) that lies in at most one set of size >= 3 removes at least deg(v) gates. With T1: 951 holds for every
  system whose 'core' has no set of size 4, and a minimal counterexample has every point in >= 2 sets of size >= 3.
  Smallest remaining test system: n = 8, base 13 (scaffold running exhaustive SAT at base - 1).
- **T1 (front, Fable B; PROVED IN LEAN, Small3.lean, `small3_bound`; also `small_min2_bound`: s >= sum min(|S|-1, 2)):** 951 holds whenever every set has size at most 3 (clean circuits; free-choice MatchG with
  B3 test systems). So triple systems (Fano, Pasch, sunflowers) cannot be counterexamples; this covers 952 at q = 2.
  Remaining gap: the third and later merge gates of sets of size >= 4.
`hard_case_core` (Final.lean; now a corollary of `no_minCE`; the old HardCase chain was removed): a clean, live circuit with exactly one essential NOT, at least two hard sets, no family of zero
sets satisfying the pairwise condition, at least one DD set, at least one set of size >= 4, and every point (lying in some set) in at least two sets of size >= 3, cannot have fewer than sum(|S_i|-1) gates.

Sufficient routes (each proved to close it):
- Gap-G: disjoint counts;
- MatchG: a matching;
- **FracMatch**: a fractional charge, the weakest of the three. This is the main route (board priority 1).

## 4. Evidence (checked on cases)
- Gap-G held on every hard circuit tested, with no counterexample:
  - front: 120 of 120 (n <= 7)
  - scaffold: hundreds more across K4, K4-e, P2 and random systems
- Two-World held on 7,200 K4 circuits with the predicted obstruction forced (size 16, capped sample); the same
  7,200 also pass canonical Hall and R* (scaffold).
- Sunflower / Pasch / two-triple essential circuits: 6,014 (scaffold) plus coord's sunflower runs at sizes 18-20, 0 failures.
- Fano plane in 13 gates with one NOT (would refute 951): open, relaunched on the WLOG cases only.
- Refuted along the way:
  - the full-D ChargeOK (3 counterexamples)
  - Lemma R as stated
  - canonical Hall (cx1-cx3)
  - rule R*
  - the Π* private-class matching rule (front, SORRY_DISSECTION §10; counterexample cxP6 is on a core system)
  - the fixed 50/50 split rule for FracMatch (front, cxtw3c; outside the open case, free-choice FracMatch survives)
  - per-output-cube multi-base Nechiporuk for AND/OR circuits (tractability, PROVED IN LEAN, Kernel/MultiBase
    `multiBase_without_compat_false`: K_{2,2} edge sums, gates x0x1, x2x3 and their OR, 3 < 4). Lesson: a proof must use that
    each o_w is exact on ALL of {h = 1} at once, not on one cube per output. (OR-only circuits: the own-base bound is proved.)
  - whole-class S-repay (front's referee, SORRY_DISSECTION §15, w9/srepay_ref/v2whole_cx.json); the merge-set version that does hold
    is equivalent to Lemma J (weight <= 1 union-find bound) and covers only hyperforests, which R0' already handles. So lifted
    ClassFrac for cyclic / core systems is fully open and must use inputs of weight >= 2.
- None of these refutes 951 itself.
- Constructive refutation attempt on free-choice FracMatch (scaffold, Fable): FAILED to find a violation; best load 0.50
  after ~5,000 hard neighbours. Necessary features of any counterexample worked out (sharing hidden behind the NOT,
  N-hidden AND-cut; graphs and size-2 sets can never refute). Untested lead: h with non-singleton mutually absorbing
  minterms (e.g. h = pq or rs) and >= 3 sets of size >= 3, one of size >= 4. Details: agents/scaffold-fable-fracmatch.md.
- Overlap stress test (scaffold, exact SAT, n = 4..6, 52 systems with one or two pairs sharing 2 points): the one-NOT
  optimum always equals the MONOTONE optimum, which drops below sum(|S|-1) by about 1 per overlapping pair. Reading:
  breaking disjointness breaks the formula, not the 'one NOT saves nothing' phenomenon. Suggests the stronger conjecture
  'one NOT never beats monotone complexity for Boolean sums' (small cases only; Sung-Tanaka shows it fails for general
  monotone functions).
- Core system c11 (n = 8, sets {0,1,2},{0,3,4},{1,5,6},{3,5,7},{2,4,6,7}, base 11): no circuit with one NOT and 10 gates
  (scaffold, exhaustive SAT, all UNSAT). 951 holds there; the smallest core system is settled.
- Coverage frontier (front; coverage checker with paper rules, not Lean): every core system up to base 15 is covered by
  REFEREED paper rules (a, s, b, n; front's referee, SORRY_DISSECTION §18; s also in Lean); base 16: 14 systems left (n = 8).
  Earlier:
  at base 15 (n = 8) 33 -> 4 uncovered after rules a/s/b (SORRY_DISSECTION §16, NOT yet refereed); each survivor misses by
  exactly one death; next layer 30 systems at base 16. Scaffold runs exhaustive 14-gate one-NOT SAT on the 4 survivors Details: front-match SORRY_DISSECTION.md §12, w9/g1/uncovered_after_pairs.json.
- Counterexample hunt (front's Fable R, w9/r_fable.md): NO counterexample. Best essential near-miss s = base + 4 (PG(2,3), s = 43).
  E4 (CHECKED: UNSAT at base+3 on all 53 systems with n <= 5, base <= 6): an essential NOT costs at least 4 extra gates?
  PROVED-PAPER: AND2 (an essential NOT forces >= 2 AND gates); R6 REFUTED (per-world bounds; the two worlds must be treated jointly).
  CONJECTURE FJ (joint, function level): for EVERY monotone h, lifted interval circuits need >= base gates; FJ => s >= base + 1;
  CHECKED on ~22,000 (system, h) pairs with n <= 7; PROVED for h = x_p. HEURISTIC (R4): with O(log n) NOT gates the bound FAILS
  asymptotically (lines of AG(2,p) via a finite Radon transform / FFT), so any proof must use 'exactly one NOT' essentially.
- Game / adversary lane (coord Fable D, agents/coord-lateral.md; PROVED-PAPER, unrefereed):
  - Sokolov's dag-like game is node-for-node equivalent, so it adds language, not a new invariant. Negative result:
    an adversary holding a join-closed part of the zero set meets S-repay; holding all of it meets the 'defect form'
    (951 <=> sum over split ANDs T of (m(T) - 1) <= #gates outside classes; an identity, checked on 3,621 circuits).
  - AND-witness lemma (new; referee: correct with a fix, parent of the FIRST non-vanishing wire; the corollary 'every S2.2
    collision has an AND below it' is WRONG, 2 counterexamples, nothing depends on it): every S2.2 collision forces an AND gate below it in both vanishing sets; ANDs lie in no
    merge class. Missing: one AND may serve two pairs (the factor 2).
  - THEOREM H2 (follow-up, PROVED-PAPER + every step CHECKED by asserts on ~12,000 constructed/mutated circuits and a SAT hunt
    on 120 systems; NOT yet refereed): for h = x_a OR x_b every lifted circuit has >= base gates (FJ for this h), so s >= base+1.
    Extension H3: h = OR(P) when every set meets P in <= 1 point and every point outside P lies on <= 2 sets meeting P.
  - (earlier partial result, front's referee: CORRECT) h = x_a OR x_b: s >= base + 1 - floor(K/2), K <= pi = #points sharing a set through a and a set
    through b; so 951 holds for h = x_a OR x_b when pi <= 3 (s >= base+1 when pi <= 1). Conjecture H2: K <= #outside.
  - h <= x_a (incl. x_a AND x_b): Theorem-X type-1 family, s >= base+1 (known).
- Number of NOT gates (axis A): with ANY number of NOT gates, no circuit beats base on all 422 enumerated (1,1)-disjoint systems
  with n <= 7 (coord Fable F, exact SAT; n = 7 only min set size 3); c11 with <= 3 NOTs and Fano with <= 2 NOTs (s <= 12) also
  need base (scaffold). Savings with many NOTs (front R4, heuristic) only at large n.
- LEMMA K (scaffold; PROVED-PAPER, REFEREED CORRECT by session dwV8p with 2 wording fixes; checked on 42 corpus + 7.19M random
  one-NOT circuits): s >= 1 + |U| + base - ex with ex = sum_w (|S_w| - 3)^+. Hence 951 holds whenever ex <= 1 (e.g. at most one set
  of size 4 and all others of size <= 3), and a minimal counterexample needs ex >= 2. Its only loss is sum over hard sets of (d_w - 2),
  i.e. exactly the 3rd and later merge gates of hard sets with |S| >= 4. PROVED IN LEAN (LemmaK.lean: K1_bound, MinCE.ex_ge_two).
- Caveat: all data is small (at most about 7-9 inputs), and several early samples were weaker than reported
  (dead NOT gates).

## 5. Side results
- Q3 edge function: a verified 13-gate monotone circuit; the lower bound of 12 is a checked step on the
  site (970). So the optimum is 12 or 13.
- Our independent proof of the ladder-value lemma (site step 1349; merged there from another contributor).

## 5b. Related work (research session, 2026-11-24)
- No published result settles 951. Monotone baseline: Nechiporuk 1969; Mehlhorn 1979 / Pippenger (h,k)-disjoint sums; Wegener 1980
  (Acta Inf. 13) and book §6.6. One-NOT decomposition f = g(0,x) ∨ (g(1,x) ∧ ¬h(x)) (Markov; Jukna BFC Lemma 10.7).
- Sung-Tanaka (IPL 2002): one NOT can save exponentially for some monotone functions, so a proof must use the (1,1) structure.
- Closest templates: Amano-Maruoka-Tarui (DAM 2003, negation-limited merging); Amano-Maruoka (SICOMP 2005, §4).
- Barrier (research; Wegener CoBF pp. 207-214 set circuits / 1-slice; Hiltgen-Paterson, Comput. Complexity 5 (1995) 132-154):
  the restriction of 951 to inputs of weight <= 1 is FALSE for large systems, even with no NOT gate. On weight <= 1 inputs a
  Boolean sum equals its 1-slice f_w ∨ T_2, and Hiltgen-Paterson give a circuit of size 3n + o(n) for the 1-slice of
  Nechiporuk's (1,1)-disjoint sums (base Θ(n^{3/2})); more generally, in Wegener's union/intersection set circuits savings
  exist for any m sets over n points once the OR-cost is >= 3n + 2m. (Paper read at summary level; full text not reached.)
  Stronger (research Fable W, construction checked independently on all 195626 inputs): even WEIGHT <= 2 is not enough.
  For AG(2,25) (n = 625, 650 lines, base 15600) there is a MONOTONE circuit with 12370 gates that equals OR(line) on every
  input of weight <= 2 (hub/spoke 'phantom point' construction with Reed-Solomon functionals; agents/research-fable-weight.md).
  On paper the same fails for every fixed k, and via colour coding for k up to n^{1/4-o(1)}. Positive side (trivial): for a
  monotone circuit, correctness on {e_v} ∪ {comp(S_w)} implies correctness everywhere. So the zero-side tests of each output
  must be join-closed (contain comp(S_w)): any proof of 951 must use inputs of unbounded weight, as Wegener's c = a ∨ b does. On small
  systems the weight <= 1 restriction is still exact (c11 UNSAT at s = 10 with weight <= 1 rows; no union/intersection
  savings on any (1,1)-disjoint system with n <= 5; agents/research-relax.md), consistent with base < 3n + 2m there.
  Tarjan 1978: AND gates help for sums that are not (1,1)-disjoint (17 < 18).
- Novelty check DONE (research, OpenAlex forward-citation crawl, 2026-11-24): 28 seed papers (Nechiporuk, Mehlhorn, Pippenger,
  Wegener 80/82/85/86, Tarjan, Weiss, Amano-Maruoka 98/05, Amano-Maruoka-Tarui, Sung-Tanaka, Tanaka-Nishino, Beals-Nishino-Tanaka,
  Fischer 75, Morizumi, Iwama-Morizumi-Tarui, Guo-Malkin-Oliveira, Blais et al., Jukna-Lingas, Jukna-Sergeev, Grinchuk-Sergeev,
  Blum 09, Tsukiji 96); 255 citing papers (agents/research-crawl.md, research-crawl-citers.tsv). None states or proves a
  one-NOT (or few-NOT) lower bound for Boolean sums. Exact 'non-monotone complexity' results (Kochergin-Mikhailovich, Math.
  Notes 2019/2025) count NOT gates, not circuit size. Jukna-Sergeev (FnT TCS 2013, §7) and Blum (ECCC TR24-179, 2024) state the
  question of negations for Boolean sums as open.
- Possible proof templates (not yet used): Sokolov, ECCC TR16-202, Thm 3.2: monotone circuit size S <=> dag-like KW game size S,
  valid for partial functions, so it applies to the lifted form of §11 (agents/research-partial.md); Chistikov-Ivan-Lubiw-Shallit
  (STACS 2017) fractional rectangle coverings for OR circuits (LP duality), cf. FracMatch.
- Jukna-Lingas (JCSS 2022) negation width: multiplicative loss, not exact. N. Blum, 'On Negations in Boolean Networks' (2009) does not
  cover it; Blum's ECCC TR24-179 (2024) lists (1,1)-disjoint Boolean sums with negations as an OPEN target.

## 6. To do for the paper
- Literature: novelty confirmed by citation crawl (§5b, 2026-11-24); re-run the crawl before submission (new citers of the seeds).
- Either close `hard_case_core`, or present the reduction chain plus evidence as the result.
- Write the human-readable proofs of Two-World and the merge-run lemmas (short; both are union-find arguments).
- Disclose AI assistance per venue policy.
