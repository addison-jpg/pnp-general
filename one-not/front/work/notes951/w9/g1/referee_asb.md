# referee_asb.md — referee report on rules 'a', 's', 'b' (frontier15_log.md §§1-3) and their encoding in cover2.py
(Referee = Fable; work files in w9/g1/ref_asb/. Section N at the end: rule 'n' — written later, see there.)

## 0. Framework re-derived (what every step below rests on)
Minimal counterexample: system F, every single point deletion satisfies the bound; heredity (s(F) <= s(F-b)+deg b, set deletion costs
|S|-1) then gives the bound for every F-Z and for "F minus all sets meeting W". Minimum circuit: clean (all wires distinct functions,
no constants), live. For a restriction rho (x_Z:=0, x_O:=1) "dead" = gates outside need(rho), need = cone of the surviving outputs
after replacing every wire by the FIRST wire with the same restricted function (constants / variables first). Hence a gate is dead as soon as
its restriction is constant, a variable, or equal to the restriction of an earlier wire, and dead(rho) <= loss(rho) - sigma. Only
DISTINCTNESS of the counted gates has to be checked (not "different reasons"). All counts below were re-checked in this form.
Rule p re-derived (dead0(u) >= nonpair + p(u) + kL): OK. (T0) capL(u)=0 => p-tight: OK in all three cases.

## 1. Rule 'a' — VERDICT: CORRECT (one cosmetic gap in (A2), fix below). Encoding: matches the lemma, not stronger.
(T1) CORRECT. Readers of g = x_u&y (or N=~x_u) are duplicates/constants under x_u:=0, are not readers of x_u (clean), so lie in G_u
     by exactness of dead0(u)=R_u ∪ G_u; lowest-gate property forces the other input to be the variable x_w. (Also: the NOT gate
     never reads an AND-reader of a p-tight point; g has a reader since g <= x_u is no output; so P(u) must contain a partner w/o pair-gate.)
(T2) CORRECT. NOT-type: antitone argument; AND-type: T1 + z = 1_{P(v)} (weight |P(v)|; if P(v)=∅ the reader r is unread: liveness).
     AL consequences (c gate, c over A_j, c <= OR(T_S') for every set through v) OK; uses d(v) >= 2.
(A0),(A1) CORRECT. loss(x_a=x_b=0) = d(a)+d(b) (S is the only set through both; a,b not partners). All membership exclusions verified:
     r, c not in R_a ∪ G_a ∪ R_b ∪ G_b; R_a ∩ G_b = ∅ (a not in P(b)); G_a ∩ G_b = ∅ (P(a) ∩ P(b) = ∅); count tau >= 1 + extra.
     x_a&x_b: by T1 its readers would be (x_a&x_b)|x_w with w in P(a) ∩ P(b) -> unread, no output. g1 = x_a|x_b is no output ({a,b}
     lies in the line S). With tau = 1 the dead set is EXACTLY the listed one, so every reader of g1 is c; c = g1&y.
(A2) CORRECT WITH A COSMETIC GAP. "g1 dies (unread)": in the cleanup g1 could survive as the canonical representative of a LATER gate
     with the same restriction x_a|x_b. Fix: let j0 be the lowest gate != g1 restricting to x_a|x_b under x_a'=x_b'=0. j0 is a
     duplicate (dead); it is not c (-> 0), not r (-> x_v), not in G (-> variable), and not a reader x_a'|q of a'/b' (q would be g1,
     making j0 a reader of g1, i.e. c; or a lower such gate). So either g1 or j0 is one more death; the count d(a')+d(b') > loss-1 stands.
(A3') CORRECT (does not even need "read only by c"): k feeders are distinct non-pair readers on k distinct lines; k = l(a)-1 = nonpair
     gives z = 1_W + sum e_{b_i}, all readers of x_a equal 1, the remaining line L' sees x_a. "A pair is used by at most one v": OK.
Encoding (status(): RA block; okuse 'a'): fires only for sigma=1, v in V1 with l(v)=2 (=> capL(v)=0, p-tight), |T|=2, capL(a)=capL(b)=0
     (T0 => p-tight), P(a) ∩ P(b)=∅; (A1) reject if a or b not in B; (A2) reject na >= 2; (A3') counter <= l-sigma-1 = l-2. EXACTLY the
     lemma. Remark: "subsumes q" is true on all data (33 frontier systems and all 262 n=8 pair systems give identical results with
     and without 'q'), but not as a theorem (q also fires when P(a) ∩ P(b) != ∅); irrelevant for soundness, q stays switched on.

## 2. Rule 's' — VERDICT: CORRECT. (Now also Lean: MinCE.rule_s, coordinator message.)
Paper proof checked line by line, incl. the two steps the log leaves implicit: (i) AND-type user with c_v = h_u = x_u|y: y = 1 on
{x_u=0} makes h_u == 1 (not clean); (ii) h_u = ~x_u: antitone argument at z. Pair-set users (v in V1 with a B pair-partner u) are
covered by the proof (r_v is then g_v; c_v is still a constant-restricting extra death or the reader h_u).
Universal form tested numerically (see §4, claim C2): in EVERY correct clean live circuit, a point u with a singleton user and a
user-free line has dead0(u) >= p(u) + kL(u) + 2.
Encoding vs MinCE.rule_s (base + kL(u) + 2 <= s + l(u) iff kL <= l - sigma - 2): cover2 applies exactly kL(u) <= l(u)-sigma-2 when
('k',u) >= 1; kL = number of ('sL',u) uses = V1 points v with T_S(v) = {u} on a LINE S (one line per v), k counts line AND pair-set
singleton users. Not stronger than the paper lemma. CAVEAT (could not read RuleS.lean — commit 4c96be9 is not in the local clone and I
do not fetch): if "u has users" in Lean means LINE users only, then the code is stronger than the Lean statement in one case: u in B whose
only users are V1 pair-partners (kL = 0; code demands l(u) >= sigma+2). The paper proof covers that case (checked), so it is sound
on paper; coord should confirm the Lean hypothesis is "T_S(v) = {u} for some set S (line or pair-set)".

## 3. Rule 'b' — VERDICT: CORRECT. Encoding: matches (B-V), (B-U) = (R)+(C); not stronger.
(U1) OK (rule p; readers >= 2; P2; G1.9 for d(w) = 2+sigma). (U2) OK (monotonicity on Q for N; T1 + z = 1_{P(t)} for AND-type).
(U3) OK: on Q the only x_t-dependent wire below h_t would be a pair-gate (== 1); c_t not a variable (s in W: z = 1_W; s not in W: two
     lines); h_t no output (line S: z = 1_W + e_e; pair-set {t,w'}: w' in W duplicates the pair-gate, w' not in W as for a line).
Bottom lemma: below g* only variables of N' = B\U and pair-gates touching U are read (a gate x_u|x_s, s not in P(u), u in U IS h_u).
     pairs0 in the code (all pair-SETS inside B touching U, minus {t,w'}, w' not in W) is a superset of the real pair-gates => finer key
     => (R) as coded is a sufficient condition. (B-V): OR-type c == 0, AND-type c == 1 (c depends on B only). A pair-set {t,w'} with
     w' in V1 gives an empty zero set in zsets: legitimate (U3 for that pair-set, V1 coordinates are 0).
(C): c (== 0), h_t (== x_t), m_W outputs (== 1), h_w (== 1, w in W ∩ U, no output by U3, distinct for distinct w because c_w is no
     variable): pairwise distinct, all dead; pair-gates of W are among the outputs (clean) and are not double counted. loss(W) OK.
Enumeration of W (forced ⊆ W ⊆ P(t) ∩ B, W != ∅) covers every possible W_t; U-type t without B-partner is vacuous but such a
     scenario already has capL(t) < 0. Hand check #28 redone: key = 4 pair-gates, c_0|_{x_6=1} == 0, 6 deaths > 5.

## 4. Numerics
Re-run (identical to the log): old base-15 frontier 33 -> 9 (a) -> 7 (s) -> 4 (b); skeleton n=8/9/10: 4, 37, 792; pairs n=8: 58 / 122 /
124 / 130; n=9 sample: 354 -> 713.
Universal forms (hypotheses of minimality replaced by explicit exactness hypotheses; valid for ALL correct clean live circuits; ref_asb/uni.py):
 C1 dead0(u) >= nonpair+p+kL+eps (p, r);  C2 rule s;  C3 nonpair=1 & l>=1: reader not NOT, AND-type => dead0 >= p+2 (T2/U2);
 C4 T1 under exact dead0;  C5 relative AL, c_t gate, h_t no output (U3);  C6 Lemma A pieces (disjointness, count, no x_a&x_b, A0 in the
 equality case);  C7 (C) of rule b when c|_Q == 0;  C8 A3';  C9 bottom key claim.
 Corpora (15498 circuits, 1268 correct+clean+live): 0 violations. Random walk over correct clean live circuits (ref_asb/gen.py, honest
 start + junk relays incl. NOT/AND-type + random rewires; 14 systems incl. frontier systems): see the table appended below.
 Random-walk table (730100 distinct correct clean live circuits, 14 systems: pasch, pasch+pairs, c7, c7b, fano, core8, tri, p5, 3x3 grid,
 frontier systems old #0, #28, R0, R3):  claim / instances / violations / min slack
  C1_pr 4863153/0/0   C1_nonpair>=1 4863153/0   C2_s 309530/0/0   C3_andtype 46936/0/0   C3_notNOT 862131/0   C3b_V1notNOT 639420/0
  C4_T1 29339/0   C5_relAL 815195/0   C5_c_gate 523554/0   C5_h_not_output 523554/0   C6_c_r_die 881046/0   C6_disjoint 174069/0
  C6_count 174069/0/0   C6_noAND 174069/0   C6_A0 (equality case) 26406/0   C7_bcount 30/0/4   C8_A3 745017/0   C9_key 540257/0
 (slack 0 reached for C1, C2, C3, C6: the inequalities are sharp, the hypotheses are really exercised; C7 has few hits: the situation
 c_t|_Q == 0 hardly occurs in non-minimal circuits, so rule b rests on the paper proof.)  No sub-claim was violated by any correct circuit.

## N. Rule 'n' (frontier15_log.md §§6, 7, 9) — VERDICT: CORRECT (two fixable gaps in the write-up). Encoding in cover2_round6.py: matches.
REFEREED FILE = cover2_round6.py (md5 6bc4e776439aaa30ded8aa9f1b8bfa54), which is what §§6-9 describe.
!! The LIVE cover2.py (07:09) already differs: it contains "section 10" code (ones-set O / (E+), (K0), (K-U+)) with NO text in the log,
   and (E) widened from W = {w} to any W with all w of class U, P(w) ∩ B = {t}. Section 10 is NOT refereed. (The widened (E) I
   checked myself: same proof; the reader of some p_i must be c; OR-type as in §6; AND-type c = p_1&y: y = x_w2 is a non-pair reader
   of the U-point w_2 below h_w2, y = p_2 gives h_t = x_t, other outputs through W are no key functions. Holds.)
Class refinement (U/T/M/S exhaustive by rule p; capL per class = l-sigma-nonpair_min; S needs pB >= 1; S/M impossible for degree-tight
 points — consistent with the option lists): CORRECT. capL = 0 <=> class U/T or V1 with l = sigma+1 <=> p-tight, so rule a inside the
 class loop is used exactly under its hypotheses.
Class S facts: h_t != N; OR-type: (U3) verbatim (needs only nonpair = 1; >= 2 lines since m >= 2); AND-type: c = 1 on Q-points
 vanishing on S\t, c a gate or x_w (w in W); x_t&x_w excluded for w of class U (U2) / degree-tight (G1.5). CORRECT; the code gives
 "no conclusion" for other W.
Lemma N-O: CORRECT (an output reading x_w is OR(S) with w in S; <= l-sigma lines among them; z = 1 on P(w) ∪ U(S_i\w)).
Refined bottom lemma / count: CORRECT. Checked distinctness of every counted death: h_t; c (class U always; class S only under the cg
 condition — verified: a key-function output through w must be a line inside N' minus pseudo points, or a pair output with a second
 B-partner; c != p since h_t = x_t&p = x_t); m_W outputs; h_w (w in W ∩ U); ONE S-class h_w; N-O reader q of a class-T w (t of class U):
 q != c by the §9 argument (c reader of x_w: OR-type is 1 on Q; AND/NOT-type contradicts T1 because h_t reads c and the pair-gate
 {t,w} exists) — the §6 parenthesis "it is OR-type" is unjustified and should be replaced by the §9 argument (GAP 1, cosmetic; the
 code is unaffected). max(bS,bN): right (q may be the S-class h_w'' = x_w'' o x_w).
(E): CORRECT. All three forms of c reading p are exhausted (p&y, p|y, ~p); two-sided step x_w := 0 for c = N = ~p is valid (h_t == 1
 is a death outside R_w ∪ G_w of the p-tight w). In the code's (E) situation cg = 1 automatically, so "equality => dead set exactly the
 counted one" is legitimate. AND-type: y = x_w gives c = x_w (unclean) — not said in the log, trivial.
(P) pseudo pair-gates: CORRECT. T_S(v) = {a,b} in every order; Lemma A applies; readers(a) = {g1, g_a}, both OR; (P1) verified
 (c_a a gate, g_a no output for L avoiding b and for L = S); key extension right (below g* a pseudo variable is read only by g1);
 (B-P) deaths c_a, g_a, g1, g_b, m_b outputs pairwise distinct. Lines containing a pseudo point are no key functions (e_a+e_b vs e_b).
(K), (K'): CORRECT (c_v <= x_u from the bad-key analysis; r_v dead, not in R_u ∪ G_u; u p-tight of class U or T).
(K2): CORRECT WITH FIXABLE GAP 2. "c_v is no reader of x_u, as in (K')" does not transfer: in (K') c_v <= x_u was used, here only
 c_v <= x_u|x_w, and c_v = x_u|y (e.g. the pair-gate itself) is not excluded by that. Fix: AL gives c_v <= OR(S\v) for both lines S
 of v, so c_v >= x_u would put u on both lines. Rest of the count (overlap exactly {p}, loss d(u)+d(w)-1) verified.
Encoding: class loop, pp detection, (K)/(K2) conditions, (B-P) count 4+m_b > loss-1, cg, bonuses, (E) condition: all as proved, nothing stronger.
Numerics (cover2_round6.py): old base-15 frontier 33 -> 0 with 245pqrasbn; skeleton 4 / 38 / 799; pairs n=8 141; n=9 sample 729
 (= log §9). cover2_round5_final.py and cover2_round6.py agree on all rule strings without 'n' (33/9/7/4; 37, 792; 130; 713).
 Extra universal tests: C10 (Lemma N-O) 4000+ instances, C11 ((P1)) 22000+ instances: 0 violations.

## Summary
 a: CORRECT (cosmetic gap in (A2), fixed above)      s: CORRECT (confirm Lean hypothesis covers pair-set-only users)
 b: CORRECT                                          n (§§6,7,9; cover2_round6.py): CORRECT (gap 1 cosmetic, gap 2 in (K2) fixed above)
 No unsound encoding found. Not refereed: "section 10" code in the live cover2.py. All valid steps use inputs of weight >= 2 or
 full-subcube restrictions (z = 1_{P(v)}, 1_W + sum e_b, x_W := 1, two-point zero restrictions), consistent with the barrier.
 Limits of this report: paper check + tests of universal sub-claims on non-minimal circuits; no SAT/Lean confirmation of a, b, n.
