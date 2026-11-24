# Brief: prove (or refute) TWO-WORLD HALL for L-meta-951

Read first (folder F = /tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad):
F/HANDOFF_front.md (whole state), F/wave5_context.md, F/wave6_context.md (setting, definitions, dead ends),
F/w8_hall.md and F/w8_hall_b.md (Hall work: cx1-cx3, cxr, lemmas R7/L1-L4, B1-B8), F/w9/ (fraclp.py, mixrule.py).

## Setting (short)
Sets S_w ⊆ [n], |S_w| >= 2, pairwise |S_a ∩ S_b| <= 1; d_w = |S_w|-1, base = Σ d_w. Circuit: fan-in-2 AND/OR gates +
one NOT N = ¬h. Outputs o_w = OR(S_w). C0: N:=0, C1: N:=1 (monotone). Hard case: clean, all gates read, C0 and C1 both
wrong, h(0)=0, >= 2 hard N-sets (hard: h(z_S)=1). Goal: s >= base.

## The rule (data: 0 failures on ~8.4k circuits incl. all canonical-Hall and R* counterexamples)
Each set w has two test systems (both legal Lean TestSys; counting lemma gives each >= d_w counted gates):
- canonical: z = z_Q for the smallest Good zero set Q ⊇ S_w (cone-restricted, unit atoms e_u).
  For hard N-sets h(z_Q)=0, so N=1 there ("N=1 world"). Counted set Dc_w.
- R*: z = z_{S_w}, unit atoms, K = all gates. For hard sets h(z_S)=1, N=0 ("N=0 world"). Counted set Dr_w.
  (Easy sets: both coincide, Q = S.)
Counted gate g for (z, S): g(z)=0 and g(e_u + z-ish atom)=1 for >= 2 u ∈ S (see hallcheck.canon / rstar.cnt_z for exact code).
Each set uses each system with weight 1/2. By bipartite b-matching integrality, the rule works iff

TWO-WORLD HALL (CORRECTED; a system may use a gate at most once, gate capacity 2):
   for every family X of systems x = (w, c), c ∈ {canonical, R*}:
   Σ_{x∈X} d_x  <=  Σ_g min(2, deg_X(g))  =  |N(X)| + #{g : g counted by >= 2 systems of X}.
(The older form 2·|N(X)| >= Σ d is only necessary, NOT sufficient. mixrule.py's LP decides exactly the corrected form.)
(Lean already has: FracMatch ⇒ bound (front-match FracMatch.lean), merge sets M ⊆ cnt with |M| >= d (coord MergeRunT).)

## Heuristic why
Canonical loses only on merges above h (gates h, x_c ∨ h; output = AND-cut r ∧ k with k ⊇ N, k(z_Q)=1, so k-chain
invisible). Those gates are >= h, hence 1 at z_S when h(z_S)=1: never counted by R*. R* loses only on OR-cut junk
(o = t ∨ k, k = N ∧ (...)), which the N=1 world sees. Each world covers the other's blind cut.

## Tasks, in order
1. Test whether the stronger, cleaner statements hold on data (F/w8/cx*.json, F/w8b/cxr.json, F/w7/badT.jsonl, bad.jsonl,
   F/chk/c.jsonl, /tmp/w5ess.jsonl): e.g. (a) F_c=F_r case; (b) per-gate: #(w: g ∈ Dc_w) + #(w: g ∈ Dr_w) <= 2 after
   discarding gates a set doesn't need; (c) union-find statements in both worlds simultaneously (merge in C1 at z_Q or in
   C0 at z_S). Find the cleanest statement that holds and implies two-world Hall.
2. Try to PROVE it on paper, using: correctness of the real circuit (= C1 on {h=0}, C0 on {h=1}), sandwich g0 <= f <= g1,
   union-find charging / merge records ("2 blocks joined at most once"), privacy lemmas (B1, R7 L1-L4), minimality B8(3)
   (in a minimal counterexample, for every proper family F, #gates in no cone outside F < Σ_F d). You may assume s < base
   and derive a contradiction, and may assume a DD set exists.
3. If you find a counterexample to two-world Hall (or to the coin rule), verify it with mixrule.py and verify correctness
   of the circuit independently, then try whether the full LP (fraclp.py) still has L* <= 1.

## Rules
- Log incrementally (every ~20 min) to F/w9/twoworldhall.md: PROVED / CHECKED / CONJECTURE / REFUTED labels, exact statements.
- Python + pysat + scipy ok; one heavy process at a time, each < 5 min. No Lean builds needed. No git, no websites,
  no messaging other sessions.
- Final report: the strongest proved statement, exact remaining gap, any counterexample in full JSON.

## UPDATE 04:27 (VERIFIED by front): the FIXED 1/2-1/2 coin rule / two-world Hall is REFUTED
See w9/twoworldhall.md section T2 and w9/tw/cxtw3c.json (n=9, s=34, base 7; correct, clean, read, C0 and C1 wrong).
mixrule: a=0.5 load 1.5, a=0.3 2.1, a=0.7 1.0. Canonical alone matches (7 = base). fraclp (free choice) L* = 1.0: FracMatch SURVIVES.
Mechanism: in the R* world a gate G = x0 ∨ T (T <= h, built without N) is a merge for ALL sunflower triples.
CAVEAT: a Theorem X zero-set family exists for cxtw (cyclic Q_i = S_i ∪ {i+1}), so it is OUTSIDE the Lean sorry's case.
New target: free-choice FracMatch (weights chosen per circuit, any Lean test systems) under the sorry's hypotheses
(incl. NO pairwise zero-set family). A fixed rule must be circuit-dependent (e.g. canonical unless an AND-cut k ⊇ N hides merges).
