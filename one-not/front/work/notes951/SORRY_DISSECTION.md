# 951: dissection of the last sorry, refactor plan, task split (front, 2026-11-24 05:20 UTC)

Owner directive: go GLOBAL; dissect the sorry; refactor everything; if ResearcH finds anything (even far-fetched),
everyone goes all in on connecting it. Use everyone.

## 0. Where we are (all in Lean, no sorry unless stated)
- 951 ⇐ HardCaseCore (front-r0 ba4d780: Restrict/Dead/Lower/Core, `L_meta_951_of_core`).
- Proved reductions feeding it: NOT dead / h(0)=1; all sets easy; ≤1 hard set (Theorem X); cleanup (copy gates, unread gates);
  removable NOT (C0 or C1 correct); Two-World ⇒ DD; small3 (all |S| ≤ 3, also s ≥ Σ min(|S|-1,2)); R0' (point deletion ⇒ core).
- Proved bridges into it: GapG, MatchG, MatchG2, FracMatch (ℝ), PriceIneq (LP duality), Hall/simple-b-matching interfaces.

## 1. The sorry, dissected
`HardCaseCore` has 20 hypotheses. Every one except the problem itself is a CONSEQUENCE OF MINIMALITY + a proved lemma:
| hyp | meaning | source |
|---|---|---|
| hg, hU, hev, h2, hS | the problem: fan-in ≤ 2, ≤ 1 NOT, outputs OR(S_w), |S| ≥ 2, pairwise |∩| ≤ 1 | statement |
| hlt | s < base | counterexample |
| hclean, hlive | no gate equals an earlier wire; every gate read or output | cleanup reductions |
| hC0, hC1 | NOT essential (C0 and C1 both wrong) | removable-NOT reduction |
| hz | h(0) = 0 | NOT-dead case |
| hhard, h1, h1N | ≥ 2 hard sets, ≥ 2 hard N-sets | all-easy / Theorem X ≤1 hard |
| hC | no Theorem X zero-set family | Theorem X (cone) |
| hDD | some DD set | Two-World |
| h4 | some |S| ≥ 4 | small3 |
| hcore | every point in a set lies in ≥ 2 sets of size ≥ 3 | R0' |
So the sorry is really: **"there is no MINIMAL counterexample"**, with a growing list of minimality facts inlined.

## 2. Refactor (Lean) — one predicate, one sorry
- `IsCE S gates out` := problem hyps ∧ hlt.  `MinCE` := IsCE ∧ minimal in (gates.length, Σ|S_w|) lexicographically.
- One lemma per reduction: `MinCE → clean`, `→ live`, `→ essential`, `→ h0`, `→ twoHardN`, `→ noThmX`, `→ DD`, `→ has4`, `→ core`,
  plus NEW minimality facts usable by global arguments:
  - (B8(3)) output deletion: for every proper family F of outputs, #gates outside every cone of F^c < Σ_F d.
  - (R0 quantitative, Fable E N2/N3) for every v: #readers(x_v) ≤ #dead(x_v:=0) ≤ deg(v) − σ;
    #(gates ≥ x_v) + #(unread after x_v:=1) ≤ Σ_{w∋v} d_w − σ, where σ = base − s ≥ 1.
  - (heavy point) h ≥ x_v ⇒ s ≥ 1 + Σ_{w∌v} d_w + Σ_{w∋v} |P_w|.
- Single sorry: `no_minCE : ¬ MinCE S gates out`. Old HardCase* defs become derived corollaries (keep for compatibility).
- Refactor everything else onto the kernel (tractability's port), one shared Python module for evaluation/matching/menus.

## 3. Global attack lines (math), each a task
- G1 DOUBLE COUNTING OF MINIMALITY (new, front): sum the per-point constraints N2/N3 over all v and the per-family
  constraint B8(3) over families; core systems have every point of degree ≥ 2 (in sets of size ≥ 3). Goal: contradiction
  σ ≥ 1, or a quantitative bound on σ. Check on the n=8 core system and 4×3 grid.
- G2 FracMatch / PriceIneq globally: price rule (relative sandwich rule, as implemented by tractability: z any point
  vanishing on S_w of weight ≤ 2, P_w = private-above class) — prove the cross-set collision bound (E0.1 gives collisions
  only between mutually hitting z's).
- G3 strengthened induction ★ (Fable E): #gates outside J^L ∪ J^U ≥ base (J^L: below two different sums; J^U: above two).
- G4 two-world global charging: real circuit = C1 on {h=0}, C0 on {h=1}; monotone lower bounds on the two halves
  (Wegener §6.6 is monotone-only; 1-slice open), combined via restriction bound (PartialBound) through heavy points.
- G5 RESEARCH-DRIVEN: anything the literature suggests (negation-limited circuits, Markov/Fischer, Amano–Maruoka,
  Jukna's negation width, sandwich/approximation methods, LP/Hall-type lower bounds for Boolean sums, design theory for
  partial linear spaces with all points on ≥ 2 lines of size ≥ 3). If any hit: everyone pivots to connect it.

## 4. Task split
| who | task |
|---|---|
| coord | Lean refactor §2: IsCE/MinCE, per-reduction lemmas, single sorry `no_minCE`; merge front-r0 |
| tractability | kernel port (Eval/Cleanup now unfrozen; keep front-r0 building); MinCE-level ops: output deletion (B8(3)) and variable restriction as general kernel lemmas; price-form tie-in |
| scaffold | exhaustive SAT on core systems (n=8 running; next 4×3 grid); generate near-minimal core circuits; test G1/G3 inequalities numerically |
| ResearcH | literature + global strategies for G4/G5; report ANY lead, however far-fetched, with exact statement + citation |
| front | G1 (Fable), G2/G3 follow-ups, integrate research leads, keep this file current |

## 5. UPDATE 05:45 — G1 results (Fable G1; log w9/g1_fable.md, code w9/g1/)
PROVED-PAPER (front checked G1.1 line by line):
- G1.1: s >= base for every system with all point degrees <= 2 (any set sizes; all grids). Minimal counterexample in this
  deletion-closed class: N2 ⇒ every point has degree 2 and exactly one reader. Absorbing lemma: a single reader of x_u can't be
  x_u∨x_v (set x_v=1), x_u∧x_v (x_v=0), or ¬x_u (monotonicity in (x,N)). The FIRST gate reads only variables ⇒ contradiction.
- G1.2 (bottom lemma, any minimal counterexample): V1 = single-reader points, B = multi-reader points; |B| >= 2;
  σ <= (2nd largest degree) − 2; s >= base when at most one point has degree >= 3.
- G1.3 (peeling cascade): order V1 by reader position; c_j depends only on A_j = B ∪ earlier V1; every S ∋ v_j meets A_j;
  if S ∩ A_j = {u} then x_u := 0 kills c_j and r_j too ⇒ deg(u) >= 3+σ (u ∈ B) or >= 2+σ (u ∈ V1).
CHECKED (cover.py: small3 + R0 + G1.2/G1.3 recursion): ALL of c11, c12, n=8 base-13, n=9 base-13, n=10 base-15 cores, 4×3 and
4×4 grids are covered; 858/1146 random cores (n <= 11) covered. c11 independently UNSAT by scaffold SAT (s=10).
GAP: systems where every set through every single-reader point has >= 2 possible multi-reader points of degree >= 3; includes all
systems with min degree >= 3 (V1 = ∅, e.g. PG(2,3)). Next tools: multi-point zero restrictions x_{S∩B} := 0, x_u := 1 (N3) on
the bottom part over B. Smallest uncovered n=8 examples in w9/g1_fable.md.

## 6. UPDATE 05:55 — lead J (Opus; log w9/j_cut_opus.md)
- PROVED-PAPER: (RM) relative Mehlhorn lemma (AND s∧t in an output's OR-decomposition on a world's domain can be replaced by s or
  t; needs the domain closed under a∨b for points avoiding S_w: always in U1, in U0 iff w easy) ⇒ the NOT breaks Mehlhorn only at
  crossing joins (a,b ∈ U0, a∨b ∈ U1), which forces w hard. (E1) easy sets: >= L_w − 1 private world-1 OR gates (L_w = light
  units). (E3) hard sets: >= d_w world-0 merge gates (the R* class; not private). Best proved: s >= Σ_{easy} (L_w − 1).
- Gap = exactly: heavy units of easy sets + world-0 sharing among hard sets (private only with Theorem-X base points, excluded).
- CHECKED: Π*_w = Dr ∪ Pr ∪ D0 ∪ P0 (hard) ∪ D1 gives a full matching on 2559/2559 circuits; |Π*_w| >= d_w everywhere.
  Conjectures C2/Π* and J-repay (rule-B deficiency <= N-dependent gates outside the classes).

## 7. UPDATE 06:05 — G3 (Opus; w9/g3/g3_opus.md): conjecture ★ REFUTED for one-NOT circuits
- cxstar5.json (n=6, sets {1..5},{0,1},{0,2}, s=18, base 6, front re-verified correct/essential): only 5 gates outside J^L ∪ J^U.
  Shannon split on shared point 0: hard set's h=1-side merges (≤ x0) land in J^L, h=0-side merges (≥ A_c ∨ A_d) in J^U.
- PROVED: ★ for all |S| ≤ 3; ★ for monotone circuits (Σ|L_a| ≥ base via union-find at z_S); easy sets: class M_a of size ≥ d_a.
- Verdict: the ★ induction route is dead as stated; ★_3 (witnesses of size ≥ 3) survives but is not restriction-stable.

## 8. UPDATE 06:15 — G1 round 2 (w9/g1_fable.md "ROUND 2"; cover2.py, enumcores.py)
PROVED-PAPER: G1.5 (AND/NOT-reader: tight points have only OR-readers, not read by N); G1.6 capacity cascade
(k single-reader points using u as only earlier point ⇒ k ≤ deg(u) − σ − readers(u)); G1.7 tight-pair lemma (σ=1).
Coverage of skeleton cores: n=8 4/4, n=9 36/50, n=10 657/1538 (pairs-added systems not counted).
Blocks: tight T of size ≥ 3; non-tight points as singletons/pairs; V1 = ∅ (3-regular, PG(2,3)) — partial: tight point behaves like a
single-reader point on the half-cube x_b=1 ⇒ next: a "relative peeling lemma". x_u := 1 (N3) route not developed yet.

## 9. UPDATE 06:30 — G1 round 3 (stalled; Fable stopped) + Lean G1 landed
- Lean (front-g1 0abd4a9, verified): MinCE.no_minCE_deg2 (G1.1), MinCE.two_heavy/two_deg3 (G1.2, dead-gate form), absorb_eq/anti.
- PROVED-PAPER: relative absorbing lemma (tight a, readers x_a∨x_b and x_a∨c2 ⇒ c2 ≤ OR(S'\a) on {x_b=1}); full peeling if c2 monotone.
  Exact obstruction: when c2 depends on N, the bound fails exactly at crossings x → x∨e_b with h(x)=0, h(x∨e_b)=1 (same crossing
  joins as lead J's relative Mehlhorn lemma). Pair lemma: tight v with pair-set {v,u} ⇒ gate x_v∨x_u exists.
- Coverage unchanged (skeleton 4/4, 36/50, 657/1538); with pairs: n=8 37/262. Conjectures H+, Ψ1 (surcharges) — no induction.
- PNP-subproblem link: x_v:=0 gives f_{G−v}; dual absorbing lemma ⇒ max-degree-≤2 graphs in monotone / one-NOT settings.

## 10. UPDATE 06:50 — Fable P (w9/p_fable.md, w9/p/)
- PROVED-PAPER, front re-checked: THEOREM E (easy sets): for every easy set w (h(z_S)=0) in any correct one-NOT circuit,
  |Dr_w| ≥ d_w where Dr_w = {g ≤ OR(S_w) everywhere, g(e_u)=1 for ≥ 2 u ∈ S_w}. Proof: test system z = z_S, atoms e_u is Good
  (N(z_S)=1); counted g has g(z_S)=0 ⇒ C1(g)(z_S)=0 ⇒ C1(g) ≤ OR(S_w) (monotone) ⇒ real g ≤ C1(g) ≤ OR(S_w); Lemma G gives ≥ d_w.
  COROLLARY E': s ≥ Σ_easy d_w + Σ_hard min(d_w,2) (T3 classes pairwise disjoint) ⇒ 951 holds whenever every HARD set has size ≤ 3.
- Hard-set lemmas H1, (a') per-minterm classes, H2; disjointness table.
- REFUTED: C2/Π* (Opus J) as stated — cxP5 (n=8, s=32, base 7), cxP6 (n=9 CORE system, s=43, base 19), cxP1, cxP2 (also refutes
  per-minterm repair Π**), cxP3/cxP4 (class conflicts). Front re-verified cxP5, cxP6, cxP3 (correct, clean, read, C0/C1 wrong).
  Free-choice MatchG not refuted (cxP2: Σ(0) gives a full matching). Mechanism: split U1 over two minterms of h + crossing-join junk.
- Gap: hard sets of size ≥ 4, 3rd+ gates. Any fixed finite list of function-level classes is likely refutable the same way;
  a proof must use s < base essentially (counting/induction).

## 11. UPDATE 07:00 — Fable S (w9/s_fable.md, w9/s/)
- PROVED-PAPER: LIFTED MONOTONE FORM. Replace N by a fresh input y: M(x,y) monotone, s−1 gates, h y-free, and each output F_w
  satisfies o_w ∧ (y ∨ h) ≤ F_w ≤ o_w ∨ (y ∧ h) (F_w(x,0) = o_w on {h=1}, F_w(x,1) = o_w on {h=0}). 951 ⇔ every such monotone
  circuit has ≥ base − 1 gates: a MONOTONE lower bound for interval (partially specified) Boolean sums.
- S2.1 lifted counting lemma (join-closed zero set Z, atoms ⇒ ≥ k−1 OR merges), S2.2 lifted X+/pair budget, S2.3 classification
  of join-closed forced-zero domains into type 0 / type 1 (unifies Theorem X, X+, E0.1, B4, heavy-point bound). Coverage d_w always
  holds in a join-closed domain; only privacy fails. s ≥ base+1 whenever a pairwise X+-compatible lifted family exists.
- CHECKED: ClassFrac LP on the lifted menu L* ≤ 1 on all circuits (incl. cxT4 0.632); extreme duals are 0/1 prices (K-Rado form).
- REFUTED as methods: one-gate-at-a-time elimination in price form (increments > 1); 0-strict world-0 classes.
- Gap: charge each collision g ∈ cl_a ∩ cl_b to a gate outside all chosen classes (S-repay). Smallest target: two complementary
  4-sets with h = Th_2.

## 12. UPDATE 07:15 — pair rules (Opus; w9/g1/pairrule_log.md) [wind-down result: PARTIAL]
- PROVED-PAPER + encoded in cover2.py (default '245pqr'): monotone point-insertion bound s(F) ≤ s(F−b) + deg(b) (justifies
  multi-point zero restrictions); 'p' G1.9 pair lemma in counting form (nonpair(u) + kL(u) ≤ ℓ(u) − σ, nonpair ≥ 1);
  'q' G1.7+G1.9 one-pair-set tight-pair rule; 'r' cascaded gate c_v also dies (single-reader singleton needs degree ≥ 3+σ).
- Coverage: skeleton n=8 4/4, n=9 36/50, n=10 657→734/1538; with pairs n=8 37→58/262, n=9 sample 202→354/2178.
  The four base-14 open systems are now covered. Smallest open: 33 systems at base 15 (all n=8, 2–4 pair-sets), all with σ = 1.
  Minimal uncovered list: w9/g1/uncovered_after_pairs.json (1279 systems).
- Blocks: degree-4 B point with one B pair partner used once as a singleton (needs a second death under x_w := 1 or relative peeling).

## 13. 07:20 — WIND-DOWN: all front agents stopped (owner directive via warden)
- Fable R (counterexample hunt): stopped mid-run; partial log w9/r_fable.md (+ w9/r/), no verified counterexample reported.
- Opus S-repay: stopped before writing its log; no result.
- Final state of front's 951 work: this file §§1–12, PROVED_951.md, w9/*. Lean: everything merged into coord-951 by coord.

## 14. 07:35 — 951 RESTARTED (owner confirmed directly); Opus agents hit usage limit → continued on Fable
- Opus S-repay (stopped by API limit) log w9/srepay_opus.md: claims Lemma J + (CHARGE) |X| ≥ coll + #{g ∈ ∪M_w \ J} − cyc(H),
  S-repay PROVED for hyperforest systems (two sets incl.), reduction 951 ⇔ #(non-joint-world-1-merge gates of M) ≥ base − |J|.
  UNREFEREED — a Fable referee is checking it (w9/srepay_referee.md); a Fable extends it to cyclic systems (w9/srepay_fable.md).
- Opus frontier (stopped) → Fable continues in w9/g1/frontier15_log.md. Fable R continues (E4: essential NOT ⇒ s ≥ base+4).

## 15. 07:50 — REFEREE of srepay_opus.md (Fable; w9/srepay_referee.md, w9/srepay_ref/)
- Lemma J (|J| ≥ |V'| − c, weight-≤1 union-find on the lifted circuit at (0,1)): CORRECT. Hyperforest ⇒ s ≥ base + 1 (with a NOT,
  h(0)=0): CORRECT, but hyperforests are already covered by R0' (no core is a hyperforest).
- "S-repay PROVED": overstated — only for the merge-set selection cl_w := M_w (equivalent to Lemma J); whole-class S-repay FAILS
  (srepay_ref/v2whole_cx.json; 1532/2766 random essential forest circuits).
- "951 ⇔ …": a restatement (and off by one: it is s ≥ base + 1).
- "mixedness only via cross merges": WRONG for intersecting sets (srepay_ref/inter_input_child.json); CHARGE unaffected.
- Key caveat: Lemma J is exactly the weight-≤1 bound, capped at |V'| − 1 < base whenever cyc(H) ≥ c; the missing cyc(H) gates on
  cyclic/core systems MUST come from inputs of weight ≥ 2 (Wegener 1-slice barrier). Nothing in srepay_opus touches core systems.

## 16. 08:05 — base-15 frontier: 33 → 4 (Fable; w9/g1/frontier15_log.md) [paper proofs, NOT yet refereed]
- New rules in cover2.py (default '245pqrasb'): 'a' p-tight pair lemma (σ=1, subsumes q); 's' absorption at the singleton user
  (any σ: a point used as a singleton needs kL(u) ≤ l(u) − σ − 2 — resolves the named blocker via the weight-≥2 input z = 1 on
  P(u) ∪ users); 'b' bottom lemma with pair gates (any σ; first rule that works with V1 = ∅).
- Coverage: skeleton n=9 37/50, n=10 792/1538; pairs n=8 130/262, n=9 sample 713/2178; minimal uncovered 1279 → 1204.
- Open at base 15 (n=8): {2367},{016},{035},{124},{157},{456}+{02},{13}; {2367},{017},{034},{056},{125},{146}+{02},{13};
  {2367},{034},{056},{125},{146},{457}+{02},{13}; {1456},{2357},{012},{036},{047}+{05},{13},{24}. Then 30 at base 16 (n=8).
  New list: w9/g1/uncovered_after_round5.json. Each survivor misses by exactly one death (needs a surcharge, conjecture H+).

## 17. 08:20 — base-15 frontier CLOSED on paper (rule 'n'; w9/g1/frontier15_log.md §§6,7,9) [rules a, b, n UNREFEREED; s Lean-proved]
- Rule 'n' (refined scenarios: B-point classes U/T/M/S; refined bottom lemma; Lemma N-O: every point has a non-pair reader that is
  not an output; (E) equality-case one-death surcharge via two-sided restriction; (P) Lemma-A feeders as pseudo pair-gates; (K),(K2)).
- All 33 base-15 systems covered (hand-checked the last 4). Coverage: skel n=9 38/50, n=10 799/1538; pairs n=8 141/262, n=9 729/2178.
- Frontier: 1230 minimal uncovered; base 16: 24 (all n=8), list w9/g1/uncovered_after_round6.json; blockers in f16_explain.txt.

## 18. 08:35 — REFEREE of rules a, s, b, n (Fable; w9/g1/referee_asb.md): ALL CORRECT (fixable write-up gaps)
- a: CORRECT; (A2) gap fixed (g1 or a lower duplicate j0 is the extra death). "subsumes q" true on data, not a theorem (q stays on).
- s: CORRECT; encoding = Lean MinCE.rule_s (Users = singleton users through ANY set; checked in RuleS.lean by front).
- b: CORRECT; coded key is a sufficient condition; hand check #28 redone.
- n (cover2_round6.py, md5 6bc4e776…): CORRECT; gap 1 cosmetic (§6 N-O reader ≠ c: use §9's argument); gap 2 in (K2) fixed
  (AL gives c_v ≤ OR(S\v) on both lines of v, so c_v ≥ x_u would put u on both lines).
- Numbers reproduced (base-15: 33→9→7→4→0). Sub-claims tested on ~730k circuits, 0 violations; rule-b count (C) weakly exercised.
- NOT refereed: live cover2.py "section 10" (ones-set O, (E+), (K0), (K-U+), widened (E)) — base-16 work in progress.
=> base-15 frontier closed on refereed paper rules (cover2_round6.py).

## 19. 08:50 — frontier round 7 (base 16: 24 → 14) + Fable R final
- Frontier (w9/g1/frontier15_log.md §§10–12, cover2_round7.py) [round-7 lemmas UNREFEREED]: (PG) pair-zero lemma (σ=1);
  (E+) general one-death surcharge (any σ; ¬p exception uses σ=1); (K0) forced zeros; (K-U+) ones plus one zero; (E) for |W| ≥ 2.
  Coverage: pairs n=8 141 → 204/262, n=9 sample 729 → 778/2178. Frontier: 1317 minimal uncovered; base 16: 14 (n=8); the n=8 part
  is complete with 58 systems. List: w9/g1/uncovered_after_round7.json. Referee fixes for a/n folded into the log.
- Fable R (w9/r_fable.md R1–R12, w9/rf/): NO counterexample. Best near-miss +4: PG(2,3) with s = 43 (base 39), essential, clean,
  read — front re-verified (w9/rf/pg3_ess43.json). E4 SAT: UNSAT at +3 on all 53 systems with n ≤ 5, base ≤ 6. PROVED-PAPER (unrefereed):
  R2 easy sets private (cf. Theorem E); AND2: < 2 AND gates ⇒ removable NOT (so merge-class proofs give s ≥ base+3 for essential
  circuits); R6 per-world route refuted (SAT). CONJECTURE FJ: for EVERY monotone h (wire cost not counted) a monotone circuit over
  (x,y) with F_w ∈ [o_w∧(y∨h), o_w∨(y∧h)] has ≥ base gates — no violation on ~22,000 (system, h) pairs, n ≤ 7. FJ ⇒ s ≥ base+1.
  PNP link (unverified, asymptotic): Radon/FFT gives C(f_G) = o(|E|) on Levi graphs of AG(2,p) with many NOTs.

## 20. 09:00 — Fable chist (Chistikov–Iván–Lubiw–Shallit fractional coverings; w9/chist_fable.md, w9/chist/)
- PROVED-PAPER: charging principle; three LP forms + duals (whole-class = set cover; LiftClassFrac ↔ PriceIneq; unnormalised
  sub-selection "cover-price" = weakest hypothesis giving the bound); THEOREM F: s ≥ 1 + V_fun(S,h) (fractional relaxation of the
  Theorem X / X+ / E0.1 family; circuit-independent dual is feasible exactly in the monotone case = (1,1)-disjointness).
  LEMMA M: for ANY z vanishing on S_w, union-find over wires 0 at z gives exactly d_w merging OR gates M_z(w) (no Good condition).
  Load identity: for any distributions μ_w on zero points, total load = base, only OR gates carry load.
- REFUTED: whole-class lifted charging (cxT2, cxT4); every circuit-independent zero-point distribution tried (uniform p=1/2 refuted
  by new cxrb(k) and essential cxU_8_4.json, n=20; other biases, h-adapted rules).
- PRECISE OPEN STATEMENT (MergeFrac): ∃ distributions μ_w over zero points with every gate load Σ_w Σ_z μ_w(z)[g ∈ M_z(w)] ≤ 1.
  ⇒ FracMatch ⇒ 951 (even #OR ≥ base). Dual: ∀ π ≥ 0, Σ_w min_z π(M_z(w)) ≤ π(gates). CHECKED on ~15,300 circuits incl. cxT4,
  cxU_8_4 and 300 random re-orderings. Single-price case PROVED. Missing: bound on load of N-dependent gates from a world-0 entry of
  one set with a world-1 entry of another.

## 21. 09:20 — frontier round 8 (base 16: 14 → 13) [L1–L6 UNREFEREED]
- (L6) correction to round-7 (K-U+): the +1 requires P(u0) ∩ (O ∪ P(w)) = ∅ for all w ∈ O (round-7 numbers unaffected).
- New: (L1) AND-reader of a pair-gate (σ=1); (L2) (E+)/(K-U+) with S-class points in O (kills c = ¬(x_t|x_w) by monotonicity);
  (L3) c counted in (K-U+) for class-T u0; (L4) (K) for every V1 point, any reader type; (L5) relaxed (K-U+).
- Coverage: pairs n=8 206/262, n=9 sample 806/2178; 1286 minimal uncovered; base 16: 13 (n=8).
- Open lemma that would close most of base 16: "a strictly tight point with two OR-readers and no pair-set has no reader x_u0 | p
  with p a pair-gate". Diminishing returns → frontier agent paused; lemma handed to Fable H+; scaffold SAT runs base 16 at s = 15.

## 22. 09:30 — ALL front Fables stopped by the Fable monthly spend limit (resets 11:30 UTC)
- Stopped mid-run (partial logs saved in w9/): S-repay-cyclic, MergeFrac, FJ, H+, deg3, referee-round7, referee-LemmaK.
- Landed before the stop: Lean RuleN (front-no 0705aa1: Lemma N-O, (E) surcharge); referee of coord-lateral (§ board front-referee-lateral).
- Lean side: tractability's LiftHelpers reduce no_minCE (via LiftClassFrac) to ONE hypothesis hload (per-gate load of real-base-point
  classes ≤ 1) — the S-repay / MergeFrac target.
