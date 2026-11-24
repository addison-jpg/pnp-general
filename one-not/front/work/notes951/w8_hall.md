# w8_hall.md — Hall's condition for canonical counted sets (restart-safe log)

## R1 (PROVED, 3 lines) Output-privacy lemma — holds for ANY Lean test systems
For any test systems σ_w (z, atoms p_u with p_u∩Zero(z) = {u}): o_w ∈ cnt(σ_w) (o_w(z)=0, o_w(p_u)=1 all u, |S_w|>=2, o_w is a gate),
and o_w ∉ cnt(σ_w') for w' ≠ w: o_w = OR(S_w) true at p'_u, p'_v (u≠v ∈ S_w') and false at z' gives c ∈ S_w∩p'_u with z'(c)=0, so c=u (hT);
likewise v ∈ S_w: |S_w∩S_w'| >= 2, contradiction.
COROLLARY: if all |S_w| = 2 (graphs) Hall/MatchG is TRIVIAL (each set needs 1 gate, its own output). So all graph data
(K4-e, C5, K4 ..., incl. presumably most of the "63 hardest") is vacuous evidence for Hall. Hall can only fail with sets of size >= 3.

## R2 (COUNTEREXAMPLE, verified by w8/cx1.py) Hall's condition with the canonical choice is FALSE
on a correct, clean (all wire functions distinct, non-constant), all-gates-read, essential (C0 wrong and C1 wrong), h(0)=0 circuit
with 2 hard N-sets. n=9, sets a={0,1,2,3}, b={0,4,5,6}, c={7,8}; h = OR(x1..x6); s=22, base=7.
 p1=x1|x4, p2=x2|x5, p3=x3|x6, g=p1|p2, h=g|p3, N=¬h, g2=h|x0, r=x0|N, ka=((r|x1)|x2)|x3, kb=((r|x4)|x5)|x6,
 o_a=g2&ka, o_b=g2&kb;  gadget for c (makes NOT essential): o_c=((x7&h)|x8|N) & ((x7|h)|x8).
Canonical Q_a=Q_b={0..6} (unique smallest Good), cnt(a)={g,h,g2,o_a}, cnt(b)={g,h,g2,o_b}: union 5 < 6 = (|S_a|-1)+(|S_b|-1).
Mechanism: the three merges of a and of b are the SAME gates (g,h,g2: unit support has >=2 points in each set; their inputs p_i have
one unit per set so are uncounted); the outputs are obtained by an AND with k_w, and k_w is 1 at the zero point (contains N), so
nothing in k_w is counted. File w8/cx1.json.

## R3 (COUNTEREXAMPLE 2, n=7, three triples; w8/cx2.json, checker w8/verify.py)
Sunflower S_i={0,i,i+3}, i=1,2,3; h=OR(x1..x6); s=18, base=6; correct, clean, all read, C0 wrong, C1 wrong (no extra set needed).
 A=x1|x2, A2=A|x3, B=x4|x5, B2=B|x6, h=A2|B2, N=¬h, g2=h|x0, t=x0&h, r=N|t, k_i=(r|x_i)|x_{i+3}, o_i=g2&k_i.
Canonical Q_i={0..6}; cnt(i)={h,g2,o_i}; union over the 3 sets = 5 < 6; max b-matching 5 < base 6.

## R4 (data, w8/allsys.py = exhaustive enumeration of ALL Lean test systems: every z with z|S=0, every fat atom e_u+T, K=all or cone)
cx2: per set only 2 inclusion-maximal counted sets; of the 8 assignments 7 give a full matching; ONLY the all-canonical one fails.
Fix: z = z_{S_i} (or any z with h(z)=1), unit atoms (Good because only e_0 has N=1): counted gates are the k_i chain + o_i, private.
So MatchG (∃σ) is NOT refuted by cx1/cx2; only "canonical choice + Hall" is refuted.

## R5 (data) The Hall evidence was almost vacuous
w7/badT.jsonl (63 hardest): 40 have a canonical double count, but only 4 have one involving a set of size >= 3 (by R1 the other 36
are settled by "each set of size 2 takes its own output"). bad.jsonl (160): 53 shared, 4 involving a set >= 3.
Canonical-Hall counterexamples need s ~ base+12 (cx2: 18 vs 6); data only covers base+2..base+7.

## R6 (data) cx1 and cx3 under the full Lean menu
cx1 (n=9): all 18 maximal assignments give a full matching. Besides z=z_S/unit atoms, even Q=[n] with K = ALL gates works there
(junk outside the cone, e.g. the c-gadget gates x7|h, (x7|h)|x8, becomes counted by a and b). NOTE: TestSys.K may be any read-closed
set, so cnt may include gates outside the cone; hallcheck.canon is cone-only.
cx3 (w8/cx3.json, n=10, s=24, base=9): S_i={0,i,i+3,6+i}, h=OR(x1..x6); points 0 and 6+i are light (h(e)=0) so "z=z_S with unit atoms"
is NOT Good; o_i=(g2|x_{6+i}) & (r|x_i|x_{i+3}|x_{6+i}). Canonical: cnt(i)={h,g2,g2|x_{6+i},o_i}, union 8 < 9: Hall fails again.
Full menu: 26 of 27 maximal assignments match; fix = fat atom e_0+e_v with z having x_v=1 (h(z)=1), or Q=[n] for two of the sets.
No circuit found where MatchG (∃σ over the whole Lean menu) fails. Robust counterexample: NOT found, NOT excluded.

## R7 (PROVED) small positive lemmas (any Lean test systems unless said otherwise)
L1 (support, canonical): g ∈ cnt(w) ⇒ g(e_v)=0 for every v ∉ Q_w. [e_v <= z_Q and N(e_v) <= N(z_Q) by Good, or g not downstream of N]
L2 (Thm X form): g ∈ cnt(a)∩cnt(b) ⇒ B_a(g) ⊆ S_a∩Q_b and B_b(g) ⊆ S_b∩Q_a, unit support ⊆ Q_a∩Q_b.
L3 (pointwise-below privacy, generalises R1): if g <= OR(S_a) on all inputs then g ∉ cnt(σ_b) for every b ≠ a and every test system σ_b.
   Proof: g true at atoms p_u,p_v of b (u≠v), false at z_b; g<=OR(S_a) gives c∈S_a∩p_u; if z_b(c)=0 then c=u, so u∈S_a; if z_b(c)=1 ...
   CAREFUL: needs z_b(c)=0. Correct statement: g ∉ cnt(σ_b) whenever z_b vanishes on S_a (e.g. S_a ⊆ Q_b), OR atoms are units.
   For g = o_a it is unconditional?? NO — recheck: o_a(z_b)=0 forces z_b = 0 on S_a, then c=u. So R1 is unconditional (uses g(z_b)=0 with g = OR(S_a) exactly).
   For general g <= OR(S_a): unit atoms of b suffice (e_u ∈ S_a for two u ∈ S_b: contradiction). With fat atoms L3 can fail.
L4 (two triples, unit atoms): F={a,b}, |S_a|=|S_b|=3, unit-atom systems: Hall holds. Proof: else cnt(a)={m,o_a}, cnt(b)={m,o_b}; the two
   union-find merges of a are m then o_a=p∨q, and the input carrying the 2-block is counted hence = m; so m <= o_a pointwise, L3 ⇒ m∉cnt(b).
   Hence minimal canonical failures are three triples (cx2) or sizes (4,4) (cx1).
"A gate cannot merge for two sets of F while counted" is FALSE (h and g2 in cx2 merge for all three sets).

## STATUS / exact remaining statement
(B) delivered: Hall with canonical choice is false for correct+clean+read+essential circuits (cx1, cx2, cx3). Under s<base Hall for F=all
is literally the negation of the hypothesis, so a Hall proof must work for a size-independent class; canonical cannot be it.
OPEN (unproved, untested beyond cx*): MatchG with free choice: for every correct one-NOT circuit there are Lean test systems (z, fat atoms,
K read-closed) with a full matching. A choice rule must leave canonical when the merges sit above the cut k_w with k_w(z_Q)=1.

## R7' (clean restatement of L3/L4; supersedes the messy L3 text above)
R1 (unconditional, any systems): o_a ∈ cnt(σ_a); o_a ∉ cnt(σ_b), b≠a. [o_a(z_b)=0 forces z_b=0 on S_a, then hT gives two points in S_a∩S_b]
L3 (b has UNIT atoms): g <= OR(S_a) on all inputs ⇒ g ∉ cnt(σ_b). With fat atoms for b this can fail (c ∈ S_a∩p_u with z_b(c)=1).
L4: two triples a,b, at least one of them with unit atoms: |cnt(a) ∪ cnt(b)| >= 4. (proof as above; uses only union-find + L3)
Files: w8/cx1.py cx1.json, cx2.py cx2.json, cx3.py cx3.json, verify.py (correct/C0/C1/clean/read + canonical Hall), allsys.py (full Lean menu), stats.py.

## R8 (reply to coordinator: may assume a DD set exists) — does NOT help canonical Hall
DD(S): C1(z_S)(o_S)=1 and C0(e_u)(o_S)=0 for some u∈S. Computed: cx1 DD = [F,F,T] (the gadget set c), cx2 DD = [T,T,T], cx3 DD = [T,T,T]
(C1: o_i = g2 = OR(all) is 1 at z_S; C0: k_i = x0h|x_i|x_{i+3} is 0 at e_0). So all three counterexamples satisfy the extra hypothesis:
"exists a DD set" cannot rescue Hall with the canonical choice. It is only a case restriction for the open statement MatchG(∃σ).
