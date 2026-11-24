# r_fable.md — adversary task R (counterexample hunt for L-meta-951), restart-safe log. Code: w9/rf/
Tags: PROVED (paper, by me, not second-checked), CHECKED (code), HEURISTIC (argument, not a proof).

## R1 Two-world / sandwich formulation (PROVED, elementary)
A one-NOT circuit is a circuit monotone in (x,N). g0 = value with N:=0, g1 = value with N:=1, g0 <= g1 gate-wise. Correct iff for all w
  A_w ∧ h <= g0_w <= A_w   and   A_w <= g1_w <= A_w ∨ h      (A_w = OR(S_w)).
So with sand0(h) := min monotone size of any family {g0_w} in [A_w∧h, A_w], sand1(h) := same for [A_w, A_w∨h]:
  max(sand0(h), sand1(h)) <= s-1,   s <= sand0 + sand1 + C(h) + 2m + 1  (o_w = g0_w ∨ (N ∧ g1_w)).
Subcube bounds (monotone restriction; in a monotone circuit the classes L_w are private):
  sand0(h) >= max over minterms T of h of  Σ_{w: S_w∩T=∅} d_w                      (x_T := 1 is inside U1)
  sand1(h) >= max over maximal zeros Y of h of  Σ_w (|S_w∩Y|-1)^+                   (x_{Y^c} := 0 is inside U0)
The NOT only gives "negation information" at the boundary: the best monotone lower pseudo-complement of x_i valid on U0 is
h|_{x_i=1}, the best upper one on U1 is h|_{x_i=0}. Deep inside either world the circuit is plainly monotone.

## R2 Easy sets are private (PROVED; strengthens the all-easy reduction to mixed families)
M_a = {g : g(z_{S_a})=0, g(e_u)=1 for >=2 u in S_a}, |M_a| >= d_a for easy a (G3.4). If a,b are both easy, M_a ∩ M_b = ∅:
u in S_a\S_b with g(e_u)=1; e_u <= z_b and N(e_u) <= 1 = N(z_b), so g(e_u) <= g(z_b) = 0. Hence s >= Σ_{easy} d_a, and ALL
savings of a counterexample must come from hard sets (h(z_S)=1): their R*-merges must ride on other sets' gates.

## R3 Savings mechanisms, quantified
(a) World-0 "intersection representation" (genuine function-level saving, PROVED): product design D(r,2,μ): points F_r^2 × F_r^2,
 lines l1 × l2 with l1,l2 lines of the same one of μ <= r+1 slope classes (pairwise ∩ <= 1; point degree μ; n = r^4, m = μ r^2,
 |S| = r^2, base = μ r^2 (r^2-1)). On weight <= 1 inputs A_w = OR(l1 × F^2) ∧ OR(F^2 × l2). Cost of {A_w ∨ Th_2}:
 2(n - r^2) + 2 μ r (r-1) + m  (+ Th_2).  r=3, μ=4: 228 < base 288;  large r: ~2n vs μ n.
 But sand0(Th_2) >= base - 2μ(r^2-1) (a pair misses almost all lines): the other world pays everything.
(b) World-1 trick: U1 = {zero set inside one line}: g0_w = x_a ∨ x_b ∨ Th_{n-k+1} (2 gates per line). Then U0 contains
 {x_Z = 0} for any non-collinear triple Z, so sand1 >= base - 3·deg: again the other world pays.
(c) Thresholds h = Th_{t+1} on a plane-like design (k = line size): world 0 needs every monomial of length 2..t absorbed, the only
 known device is a (t+1)-fold AND of ORs of supersets pairwise meeting in S_w: t ANDs per line (fraction t/k of base);
 world 1 pays all lines missed by t+1 points: fraction >= 1 - (t+1)k/n. The two fractions add up to >= 1 unless k^2 > n·t/(t+1),
 which a (1,1)-disjoint family with point degree >= 3 only reaches for k <= 1.22 sqrt(n) (dual Steiner triple systems), and there the
 superset pool (cost >= n ~ base/3 per level) eats the margin. HEURISTIC conservation law: (world-0 share) + (world-1 share) >= base.
(d) Shannon split on a point (cxstar, h = x_0): saving <= deg(0) per world, cost >= 2 glue gates per set through 0 (N2 form).
(e) Time-sharing a tree (leaf l_v = (x_{π v} ∧ h) ∨ (N ∧ x_v), one OR-tree gives rows in world 0 and columns in world 1): useless,
 each world still needs ALL outputs.

## R4 Calibration: the statement is FALSE with O(log n) NOT gates (HEURISTIC-level proof sketch, standard tools, not machine-checked)
Sets = the p^2 non-vertical lines of AG(2,p), p prime (n = p^2, base = p^2 (p-1)). count(m,b) = Σ_x f(x, mx+b) is the finite Radon
transform; by the Fourier slice identity  Σ_b count(m,b) ω^{vb} = F(-vm, v)  it is one 2-D DFT plus p 1-D inverse DFTs over
Z_P (P prime, P ≡ 1 mod p, P > p): O(p^2 log p) ring operations, O(p^2 polylog p) Boolean gates; A_w = [count ≠ 0].
So general circuits need only Õ(n) << n^{1.5} = base, and by Fischer/Beals–Nishino–Tanaka ⌈log2(n+1)⌉ NOTs suffice (+O(n log n)).
Consequence for 951: any proof must use "exactly one NOT" essentially (two monotone worlds); with r NOTs there are r+1 threshold
worlds and the slice trick (monotone pseudo-complements Th_k(x - x_i)) becomes available once a single slice can be isolated on
all inputs, i.e. with ~log n NOTs. One NOT isolates nothing: both worlds contain many slices.

## PNP-SUBPROBLEM LINKS
(1) (HEURISTIC, asymptotic, NOT truth-table verified — instance far too large) G = Levi graph of the p^2 points and p^2 non-vertical
 lines of AG(2,p): bipartite, girth 6 (C4-free), |V| = 2p^2, |E| = p^3, τ = p^2. f_G = [Σ_L y_L·count_L(x) >= 1] = OR_L (y_L ∧ [count_L ≠ 0]),
 and all count_L together cost O(p^2 polylog p) gates by R4. So C(f_G) = O(p^2 polylog p) = o(|E|): the conjecture |E| + τ - 1 fails
 asymptotically on C4-free graphs with AND/OR/NOT (uses many NOTs; crossover p is in the hundreds/thousands because of modular
 arithmetic constants). The same holds for the polarity graph ER_p-type dense C4-free graphs whenever the neighbourhood sums have a
 fast transform.
(2) Small girth >= 5 graphs (Petersen, Heawood, Möbius–Kantor): the neighbourhood systems have all sets of size 3 (covered by
 small3 for the one-NOT Boolean-sum problem); nothing from my side beats |E| + τ - 1 there.

## R5 Experiments (CHECKED; code w9/rf/)
(a) unc8.py: skeletons g1/cores8.pkl + pairs, cover.covered: base<=13 all covered; base 14: 12 uncovered classes (my enumeration; front
 quotes 18 — probably a different skeleton list), base 15: 49 uncovered. List in rf/unc8.json.
 Generic SAT (g1/satgen.py, readcap=1 = N2 for sigma=1, legal since all point deletions are covered) on unc8[0]
 {012},{034},{056},{1357},{2467},{07},{14} at s=13: no answer in 240 s. Exhaustive n=8 is scaffold-scale, not 5-minute-scale.
(b) prod.py: explicit world-0 circuits for the product design (R3a), verified exact on weight<=1 and >= A_w on random inputs:
 D(3,2,4): n=81, 36 lines of size 9, base 288, world-0 gates 228.   D(3,2,3): base 216, 207.   D(5,2,6): n=625, base 3600, 1590 (44%).
 Weight<=2 version (PROVED): D(r,3,μ), g_w = OR(U_12)∧OR(U_23)∧OR(U_13), U_J = {coords in J on the line}; a point off S_w lies in at
 most one U_J, so two ones cannot fire all three. Cost 3(n - r^4) + 3μ r^2(r^2-1) + 2μ r^3; r=5, μ=5: 55250 < base 77500.
 In general exactness on weight <= t costs t ANDs per line + a pool of size ~(t+1)(1+μ)n/r^2 in D(r,t+1,μ).
(c) ess.py: SAT for the minimum size of a correct circuit whose NOT is ESSENTIAL (C0 wrong and C1 wrong), live:
 min s = base + 4 EXACTLY (UNSAT at +1,+2,+3, SAT at +4) for: {01},{12}; {01},{02}; K3; {012},{03}; three pairs through 0; K4;
 {012},{034}; {012},{034},{13}; {0123},{04},{14}.  Witness gadget (n=3, {01},{12}, s=6):
   g3 = x1∨x2 (=o_{12}), N = ¬x2, g5 = x1∧x2, g6 = N∨g5, g7 = g3∧g6 (= x1), o_{01} = x0∨g7.
 So "the price of an essential NOT" is +4 on every system tested; the gadget attaches to any system with two sets sharing a point,
 giving s = base + 4 always (ratio s/base -> 1 from above, e.g. PG(2,3): 43/39). Best near-miss = +4, never below.
 Clean variant (ess.py ... clean): still exactly +4 on {01},{12}; K3; {012},{03}. Clean gadget = Shannon split of one variable:
   x_q := (x_p ∧ x_q) ∨ (¬x_p ∧ (x_p ∨ x_q)), with x_p ∨ x_q an existing gate of a line through p,q (N, 2 ANDs, 1 extra OR).
 More +3 UNSAT (essential, not nec. clean): {0123},{04},{14},{24},{34} (s=10, 164 s); triangle {012},{234},{450} (s=9, 54 s).
 Timeouts at +3 (250 s, undecided): {0123},{045},{14},{25}; Pasch.
 VERIFIED artifact: rf/pg3_ess43.json — PG(2,3) (13 points, 13 lines of size 4, base 39) with s = 43: correct on all 2^13 inputs,
 C0 wrong, C1 wrong, clean, every gate read (w8/verify.py and fa/lib.verify both). Ratio 43/39 = 1.103; excess +4.
(d) sand.py / sand2.py (monotone sandwich complexities by SAT; outputs may be inputs/constants at cost 0):
 n=4 {012},{03},{13}: all 166 monotone h with h(0)=0: sand0+sand1 >= base, max >= base-1.
 n=5 {0123},{04},{14} (base 5): 400 random h + all 316 h with <= 2 minterms; n=5 {012},{034},{13},{24} (base 6): 350 random h:
 sand1 = base except for a handful of h; never max(sand0,sand1) <= base-2.  h = x0∨x1 on the first system: (sand0,sand1) = (3,4).

## R6 REFUTED (by me, PROVED + CHECKED): "one world alone always costs >= base-1" (function-level route FN)
 System a = {0,1,2,3,4,5}, pairs {0,6},{1,6},{0,7},{1,7} (n=8, base 9), h = x0∨x1.  sand0 <= 5 (t = x0∨x1 serves a; pairs exact),
 sand1 <= 7 (t, t∨x6 for both pairs at 6, t∨x7, t∨x2∨..∨x5); SAT confirms both (rf, 1 s).  General: heavy set H inside one line a,
 c light points joined by pairs to all of H: world 1 saves |a|-|H|, world 0 saves c(|H|-1); both unbounded.
 So no bound of the form max(sand0(h),sand1(h)) >= base - O(1) exists: a proof MUST treat the two worlds jointly (gate-wise g0 <= g1).
 In the joint circuit this example gains nothing: the pair {0,6} needs G(x,1) ⊇ x0∨x6, G(x,0) = x0 ∨ x6∧x1 on U1, i.e.
 G = x0 ∨ x6∧(x1∨N): 3 gates instead of 1.

## R7 Verdict and obstacle analysis
NO counterexample found. Best near-miss: s - base = +4 (essential, clean, live), on every system tried, never +3.
Why the remaining systems resist (what each savings device costs):
 1. Easy sets are private (R2): only hard sets can save, and then h is below no A_b among them: no world-1 "freebies".
 2. World 0 (C1, must be >= A_w everywhere): the only saving device is an AND of F ORs of supersets (intersection representation). It
    forces a minterm of h of size <= F inside S_w^c, for every saved line; amortising the superset pool needs many saved lines, hence
    many small scattered minterms.
 3. World 1 (C0) pays in full, with private gates, every line missed by a minterm T (subcube x_T := 1). With |T| <= F < k a minterm
    hits <= Fμ lines. Accounting on a uniform design (m lines of size k, degree μ): world 0 >= m(F-1), world 1 >= (m - Fμ)(k-1),
    sum >= base - μ(k - F) (+ pool), while gluing the two worlds costs >= 1 gate per line (m = μ n/k >= μ k gates when n >= k^2).
    The possible gain μ(k-F) is always below the glue m: knife-edge at scale m, never positive in any design I could write down.
 4. Sharing world-1 merges between two hard lines a,b (the cxstar/cxT4 "J^L" merges) needs wires vanishing at both z_a and z_b:
    leaves x_u∧x_v' (1 AND each); a shared tree of K leaves costs 2K-1 gates for 2(K-1) merges: loses 1 per tree; for r lines
    leaves cost r-1 ANDs (or 2r-1 with selectors): always a net loss. A single variable is a free common leaf only at S_a∩S_b (1 point).
 5. Shannon split on a point (gadget above) costs +4 and saves nothing; several splits do not compound (each needs its own glue;
    one NOT gives one h, and negation information exists only at the boundary of {h=0}, see R1).
 6. Calibration (R4): with ~log n NOTs the bound is false by a polynomial factor (Radon/FFT + inverter), so the obstacle is exactly
    "one NOT = two monotone worlds", not Boolean-sum structure.
What I did NOT do: no exhaustive result on any uncovered core system (n=8 at s=13 is beyond 5-minute runs); PG(2,3)/min-degree-3
cores were only attacked by construction, not by search; items 2-4 are HEURISTIC accounting for the devices I know, not a proof that
no other device exists; R4 and the PNP link are asymptotic arguments, not verified circuits.
Suggested targets: (E4) "essential NOT ⇒ s >= base+4" (true on all SAT-decided systems; much stronger than 951, maybe easier to
attack by induction because the gadget is tight); joint two-world statement instead of per-world bounds (R6).

# ROUND 2 (resumed): E4 and the joint statement
## R8 E4 evidence (CHECKED)
e4enum.py: ALL (1,1)-disjoint systems on <= 5 points with base <= 6 (53 isomorphism classes, every point used): no correct circuit with
 an essential NOT of size base+3 (UNSAT, all 53; padding makes this cover +1,+2 too). Logs rf/e4_a.log, e4_b.log.
Data (bt.allcirc + /tmp/w5ess.jsonl, n <= 12, 6641 correct circuits, 4270 with essential NOT): every essential circuit has
 #AND >= 2 and #OR >= base+1; every circuit has #OR >= base. Minimal SAT witnesses at +4 always have exactly 2 ANDs, base+1 ORs, 1 NOT.
So E4 splits into   (AND2) essential ⇒ #AND >= 2   and   (OR+) essential ⇒ #OR >= base+1   (OR-951: #OR >= base always).

## R9 PROVED (paper): AND2 — a correct one-NOT circuit with fewer than two AND gates has a removable NOT (C0 or C1 correct)
Lift N to an input y (Fable S, S2): monotone M(x,y), F_w(x,0) <= o_w <= F_w(x,1), F_w(.,0) = o_w on U1, F_w(.,1) = o_w on U0.
WLOG h(0)=0 and h not constant (h ≡ 1: real = C0; h ≡ 0: real = C1).
No AND: every wire is OR(V) or OR(V)∨y; an output with y has F_w(0,1) = 1 ≠ o_w(0) (0 ∈ U0). So outputs are y-free, C0 = C1.
One AND gate A = P∧Q: every wire is L or L∨A with L = OR(V)[∨y]; P,Q are of the form L. If A is y-free, y reaches outputs only as a bare
 summand, excluded as above. If both P,Q contain y then A >= y, excluded as well. So A = (OR(V1)∨y) ∧ OR(V2), h = OR(H) (A is after N),
 and every y-dependent output is F_w = OR(V_w) ∨ A with  (i) V_w ⊆ S_w,  (ii) V_w ∪ V2 ⊇ S_w,  (iii) OR(V1)∧OR(V2) <= o_w.
 Suppose C1 is wrong at w: V2 ⊄ S_w, take u ∈ V2 \ S_w. Then u is heavy (else F_w(e_u,1) = 1 ≠ 0 on U0) and by (iii) V1 ⊆ S_w, u ∉ V1.
 Suppose C0 is wrong at w' (w' reads A). For v ∈ S_w' \ V_w' and any heavy t: e_v∨e_t ∈ U1 hits S_w', so F_w'(e_v∨e_t,0) = 1, i.e.
 (v ∈ V1 or t ∈ V1). If v ∉ V1 then every heavy t, in particular u, is in V1: contradiction. So S_w' \ V_w' ⊆ V1∩V2 (V2 by (ii)), hence
 F_w'(x,0) >= OR(V_w') ∨ OR(S_w'\V_w') = o_w': C0 is right at w'. Contradiction. ∎
COROLLARY: any proof of 951 that produces base OR gates (all merge-class proofs do: S2.1 merges are OR gates) gives s >= base + 3 for
 circuits with an essential NOT (base ORs + 2 ANDs + NOT). E4 needs one more OR gate (OR+): in the tight gadget it is the "glue" OR that
 joins the two Shannon halves, o = (x_p∧x_q) ∨ (x_r ∨ N∧(x_p∨x_q)); x_r∨(..) and the output are both in L_{qr} (|L| = 2 > d = 1).

## R10 Base-15 uncovered systems (g1/uncovered_after_pairs.json): NOT decided by me
Exhaustive E4 at base+3 = 18 gates on n=8 is beyond 5-minute SAT runs with my encoder (ess.py needs 3 valuation copies): rank 0
 {0567},{034},{126},{145},{235},{247},{01},{02} with <= 2 ANDs: no answer in 90 s; already Pasch (n=6, s=11, <= 2 ANDs) does not finish in
 100 s, triangle (s=9) took 54 s. E4 there is strictly harder than 951 itself (which is open on these systems). Left to scaffold.

## R11 Joint two-world statement at FUNCTION level, via Fable S's lift (CONJECTURE FJ; CHECKED exhaustively at n <= 5)
FJ: for every (1,1)-disjoint system and EVERY monotone h (no requirement that h is a wire, cost of h not counted), any monotone circuit
 over (x,y) with outputs F_w in [o_w∧(y∨h), o_w∨(y∧h)] has >= base gates.
 FJ ⇒ s >= base+1 for every one-NOT circuit (M has s-1 gates). FJ is the joint form that survives R6 (per-world sandwiches do not).
 It is a single monotone SAT call per (system,h) (fj.py: is there a circuit with base-1 gates? inputs/constants as outputs cost 0):
   n=4: {012},{03},{13}: all 166 h; K4: all 166 h — no violation.
   n=5: {012},{034},{13},{24} (base 6): ALL 7579 h — no violation.  {0123},{04},{14} (base 5): 7156 of 7579 h — none.
        {0123},{04},{14},{24},{34} (base 7): 4402 h — none.
   n=6: Pasch (base 8): 364 h with <= 2 minterms — none.
 PROVED special case (rederives Theorem X in lifted form, self-contained): h = x_p. Configurations (S2.1): w ∌ p: Z_w = {(x,1) : x avoids
 S_w ∪ {p}}, atoms (e_u,1); w ∋ p: Z_w = {(x,1) : x avoids S_w}, atoms (e_u,1) for u ≠ p and (e_p,0). Each class has >= d_w OR gates and
 the classes are pairwise disjoint (an atom (e_u,1) with u ∉ S_w' lies in Z_w'; the p-atom is shared by no two sets usefully). So
 |M| >= base for h = x_p, without using that h is a wire.
 Open hosts for FJ are exactly the (sets,h) without a separated family (C7): e.g. {0123},{0456} with h = x1x2 ∨ x4x5.
 More FJ checks (fj2.py, single (system,h), UNSAT at base-1 gates): {0123},{0456} with h = x1x2∨x4x5 and with h = maj(123)∨maj(456)
 (the C7 hosts without separated family): UNSAT in <1 s each.  {0123},{045},{146},{256} (n=7, base 9): h = x1x2∨x4x5, h = x4∨x5∨x6, and
 24 further h with <= 2 minterms: UNSAT (10 s each).  {0123},{045},{14},{25} (n=6, base 7): 1170 h with <= 2 minterms: none.
 Limit of my encoder: n=8 base-16 (uncovered_after_round5 rank 4, h = x0∨x2, 15 gates): no answer in 280 s.
 (Coordination: I ran NO SAT on the 4 remaining base-15 systems after the notice; the one earlier 90 s attempt on
 {0567},{034},{126},{145},{235},{247},{01},{02} returned nothing.)

## R12 Function-level E4 (CONJECTURE FJ-E; CHECKED small) and AND2 at function level (PROVED)
FJ-E: for every monotone h, a monotone lifted circuit with F_w in [o_w∧(y∨h), o_w∨(y∧h)], F(.,0) ≠ o somewhere and F(.,1) ≠ o somewhere
 has >= base+3 gates (h not required to be a wire). FJ-E ⇒ E4.  fj.py ... -2 ess (essential circuit with base+2 gates?):
 {01},{12}: all 18 h UNSAT (and base+3 is attained for 5 h);  {012},{03},{13}: all 166 h UNSAT;  {0123},{04},{14}: 41 random h UNSAT.
AND2 holds at function level too: in the proof of R9 replace "h = OR(H)" by: u ∈ V2\S_w has F_w(e_u,1) = 1 <= o_w∨h, so h(e_u) = 1, and use
 the single 1-point e_v ∨ e_u of U1. So any lifted circuit with <= 1 AND gate has F(.,0) = o or F(.,1) = o, for every h.

## STATUS (end of round 2)
No counterexample. Near-miss unchanged: s - base = +4 (PG(2,3) witness s=43, verified).
PROVED: R2 (easy sets private), R9 (AND2: essential ⇒ >= 2 ANDs; also function level), R6 (per-world route refuted), FJ for h = x_p.
CHECKED: E4 on all 53 systems with n<=5, base<=6; on 4270 essential data circuits (#AND>=2, #OR>=base+1); FJ on ~22,000 (system,h) pairs
 with n<=7 incl. all 7579 h for one n=5 system; FJ-E on 225 pairs.
OPEN / not done: E4 or FJ on any n=8 uncovered system; OR+ (essential ⇒ #OR >= base+1); FJ in general (= function-level ClassFrac target).
