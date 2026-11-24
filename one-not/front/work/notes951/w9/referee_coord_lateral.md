# Referee report: agents/coord-lateral.md (board branch), claims (ii) AND-witness lemma, (iii) h = x_a OR x_b, comment on (i)
Referee log, 2026-11-24. Code: F/w9/rcl/ (rl.py lib, t2.py, lastfirst.py, cx3.py = claim ii; t5.py, adv5.py = claim iii; t3.py = claim i).
All tests are independent re-implementations (truth tables of the lifted circuit over 2^(n+1) points); counterexample circuits
are re-verified with F/w8/verify.py (correct, C0 wrong, C1 wrong = essential NOT). Nothing in Lean. No git writes.

## Verdicts
| claim | verdict |
|---|---|
| (i) defect form identity (S3) | CORRECT (identity + privacy), and, as the note says, a restatement of s-1 >= base, not a reduction |
| (ii) Lemma 2.3 as stated (with its hypothesis) | CORRECT WITH FIXABLE GAP (proof says "last" wire; must be "first") |
| (ii) "Use: every collision of S2.2 has AND gates below it" | WRONG (counterexamples below, incl. the note's own S5 collision g = h OR x_p) |
| (iii) S5.2-5.4, 5.7: s >= base+1-floor(K/2), K <= pi; 951 for pi <= 3; s >= base+1 for pi <= 1 | CORRECT (every step checked by hand and by assert) |

## (ii) AND-witness lemma
Statement (2.3). M lifted monotone circuit, Z := Z_a ∪ Z_b any point set, g a wire with g = 0 on Z, α a point with g(α)=1,
HYP: no input (x_v or y) that vanishes on Z is 1 at α. Then there is an AND gate G with G = 0 on Z, G(α)=1, having a child that
does not vanish on Z, and G is reachable from g downward through wires vanishing on Z.
Proof check. Walk down from g through wires that are 1 at α (OR: some child is 1; AND: both). It ends in an input that is 1 at α,
which by HYP does not vanish on Z. g vanishes, the end does not, so there is a FIRST wire on the walk that does not vanish; its
walk-parent G vanishes, as do all wires before it; G is a gate; an OR vanishing on Z has both children vanishing; so G is an AND. ∎
GAP: the note takes "the LAST wire on the walk that vanishes". That wire is also a vanishing AND with a non-vanishing child and
value 1 at α, but it need NOT be reachable from g through vanishing wires (vanishing is not monotone along the walk: below an AND
the walk may leave V and re-enter it). lastfirst.py: 7695 random walks on data, last != first in 36, and in 31 of them the "last" gate
is not reachable through vanishing wires by ANY path (e.g. srepay_ref/whole_worst.json, g=15, walk 15,14,8,2). FIX: replace "last
wire that vanishes" by "parent of the first wire that does not vanish". The lemma never uses join-closedness or (L); Z is arbitrary.
Numerics (t2.py, 3 seeds, 2569 one-NOT data circuits with h(0)=0 incl. n=15,16; ~38500 valid S2.3 configurations per seed, type 0 and
type 1, random atoms; S2.1 asserts all pass): ~885000 (g, α) instances per seed, HYP true in ~48000, conclusion false in 0.

"Use" line: WRONG. HYP is not implied by S2.2. With α an atom of a in B_a(g), inputs vanishing on Z_a ∪ Z_b can be 1 at α:
 - type 1 / type 1 with standard atoms (e_u,1): u ∈ P(a|b) means u ∈ S_a ∩ Q_b, so x_u vanishes on Z_a and on Z_b and is 1 at α.
   HYP fails for EVERY atom of EVERY collision (data: std11_coll 66/71/49, HYP fails in all). This is the Theorem-X setting.
 - the note's own S5.2 configuration: collision g ∈ Mg_w ∩ Mg_w', B_w(g)={a,p}, B_w'(g)={b,p}; x_a, x_b, x_p all vanish on
   Z_w ∪ Z_w' and cover all three atoms. HYP fails always. The model collision g = h ∨ x_p = (x_a ∨ x_b) ∨ x_p (named in 5.3 itself)
   has NO AND gate in its cone.
 Data, per seed: ~49000 whole-class collisions, ~18300 merge-set collisions; HYP fails for all atoms in ~46000 / ~18100;
 NO AND gate at all in the cone in ~35000 / ~17600.
Counterexample A (cx3.py; data circuit F/w9/p/cxP1.json, n=9, s=38, verify.py: correct, C0 False, C1 False, clean, read; h(0)=0):
 sets a = {5,0}, b = {6,1} (disjoint), Z_a = Z_b = {(0,0),(0,1)} (type 1, ceiling c = 0), atoms of a: (e_5,1),(e_0,1); atoms of b:
 (e_5+e_6,1),(e_0+e_1,1) (legal by S2.3: traces pairwise disjoint; (L) holds; S2.1 asserts pass). Gate 13 = x_5 ∨ x_0 is the merge
 gate of a AND of b: B_a = {0,5}, B_b = {1,6}. Its cone is {x_0, x_5, 13}: no AND. Saved: F/w9/rcl/cx_use_A.json.
Counterexample B (cx3.py; constructed, n=5, s=13, h = x_0 ∨ x_1, verify.py: correct, C0 False, C1 False, clean, read):
 sets [[0,2,3],[1,2]], outs [13,17], gates 5=or(0,1) 6=not(5) 7=or(5,2) 8=or(7,3) 9=or(2,3) 10=and(5,9) 11=or(10,0) 12=and(8,6)
 13=or(12,11) 14=and(5,2) 15=or(14,1) 16=and(7,6) 17=or(16,15). In the S5.2 configuration gate 7 = h ∨ x_2 lies in Mg_0 ∩ Mg_1
 (B = {0,2}, {1,2}); cone {x_0,x_1,x_2,h,7}: no AND; HYP fails at all four atoms. Saved: F/w9/rcl/cx_use_B.json.
What IS true (replacement for the Use line): a collision g has an AND witness whenever some atom α ∈ B_a(g) ∪ B_b(g) is 1 on no
 input vanishing on Z_a ∪ Z_b. Automatic case: type 0 / type 0 with all atoms at level 0 (doubly vanishing inputs are y, which is 0
 at level-0 atoms, and x_v, v ∈ S_a ∩ S_b, which hits at most one of the >= 2 atoms in B_a(g)). Data: 593/687/472 such collisions,
 HYP holds and an AND exists in every one (asserted). So 2.3 is a statement about type-0 (E0.1/B4) collisions; it is vacuous for
 type-1/type-1 and for S5. "AND gates lie in no merge class" is correct for merge SETS (merges are ORs); whole classes cl(Z,a) do
 contain ANDs. Nothing downstream uses the Use line: 5.4 finds its ANDs ABOVE the collision, by a separate argument.

## (iii) h = x_a ∨ x_b
Definitions (5.2-5.3). Sets pairwise meet in <= 1 point. A-set ∋a∌b, B-set ∋b∌a, N-set, at most one AB-set. c_w = complement of
S_w ∪ {a,b}, Z_w = ↓(c_w,1); atoms (e_a,0), (e_b,0), (e_u,1) (u ≠ a,b). R_w = wires vanishing on Z_w with an upward path to F_w
inside such wires; Mg_w = OR gates of R_w at which the S2.1 union-find (circuit order) merges two blocks. K = number of gates lying
in two merge sets. π = number of points p ∉ {a,b} lying on an A-set and on a B-set.
Step check (all CORRECT):
 1. Z_w join-closed set of forced zeros (c_w ∈ U0 avoids S_w); atoms are forced ones ((e_a,0): e_a ∈ U1 hits S_w); (L): inputs
    vanishing on Z_w are x_v, v ∈ S_w ∪ {a,b} (not y), each 1 at <= 1 atom. R_w is closed under the children S2.1 uses. |Mg_w| = d_w
    exactly (union-find ends with one block).
 2. Crossing table: atom of w lies in Z_w' iff it is (e_u,1) with u ∉ S_w'; so B_w(ξ) ⊆ S_w ∩ (S_w' ∪ {a,b}) for ξ vanishing on Z_w'.
    Case analysis (A/B/N/AB) gives: common merge gates only for A-set w, B-set w' with S_w ∩ S_w' = {p}; B_w(g) = {a,p}, B_w'(g) = {b,p};
    a gate is in <= 2 merge sets (a third set would have to be B w.r.t. w and A w.r.t. w').
 3. K <= π: for fixed (w,w') at most one gate (two merges of w cannot both join the blocks of a and p); a point p lies on at most one
    A-set and one B-set (two A-sets through p would share {a,p}). The second half is not written in the note but is immediate.
 4. 5.4: F_w(e_b,0) = 0 (forced zero), g_i(e_b,0) = 1, so the R_w-path g_i → F_w contains an AND; chain = g_i and the ORs before the
    first AND, all >= g_i, so {a,p_i} ⊆ B_w; no g_j on the chain of g_i; fan-in 2 gives #tops + #junctions = k_w exactly; a junction
    has both children in the block of a (not a w-merge) and p_i,p_j ∈ B_w, so it vanishes on no other Z_v (|P(w|v) ∖ {a}| <= 1):
    outside all merge sets, private to w; a top t of w cannot be a top of another A-set w2 (t ∈ V_w2 would force B_w(t) ⊆ {a});
    each first AND has two children, so <= 2 tops. K = Σ_A-sets k_w <= #junctions + 2 #ANDs <= 2 #outside.
 5. Count: |∪Mg| = base − K, so s − 1 >= base − K + ceil(K/2) = base − floor(K/2). π <= 3 ⇒ s >= base (951); π <= 1 ⇒ s >= base + 1.
 The proof does not use that h is a wire, only the interval spec with the FUNCTION h = x_a ∨ x_b (so it also bounds circuits not
 computing h; no conflict with the 1-slice remark, which concerns other h). Barrier: the tops (c_w,1) have weight n−|S_w ∪ {a,b}|,
 the argument is not a weight-<=1 argument, so the Wegener barrier does not apply.
Numerics (t5.py, every step above as an assert, random parent maps, restricted and unrestricted union-find):
 - data: 2115 of 2569 one-NOT data circuits have h ≡ x_a ∨ x_b as a function (173 with essential NOT); all asserts pass;
   K <= 1 on data (89 circuits with K = 1), π <= 2, min (s−1−base) = 1.
 - adversarial (adv5.py): grid systems (A-sets × B-sets, π up to 9, optional N-sets and AB-set), templates honest / W∧(y∨T) /
   (W∧y)∨T' with shared g_p = h∨x_p and hash-consed junctions, then random mutation walks (rewire, flip op, bypass, insert gate; accept
   only truth-table-correct circuits with NOT input ≡ x_0∨x_1; dead gates removed) under three objectives (distance to the claimed
   bound; outside−K; essential with K >= 2 minimising 2·outside−K). 11000 built + 1195253 mutated correct circuits checked (262477 with essential NOT), 10 runs, logs rcl/adv_*.log. 0 assert failures. K up to 6 reached.
   Smallest observed: (s−1)−(base−floor(K/2)) = 1 (K=0, NOT removable); with K >= 1 always outside−K >= 3; essential with K >= 2:
   2·outside−K >= 16. No evidence against H2 (K <= #outside), but mutation search is weak evidence; no exhaustive/SAT search was run.
Remarks. (a) the result is real but narrow: 5.4 loses the factor 2 exactly as 5.5 says; (b) "K" depends on the union-find order,
 the bound holds for every order; (c) 5.1's "all-type-0 classes collide on every A/B pair" was not refereed (not in scope).

## (i) defect form (brief)
V**_w = wires <= Ω_w = wires vanishing on ALL forced zeros of F_w. Privacy 3.1 is correct (level of α_u is ¬h(e_u), so Ω_w'(α_u) =
o_w'(e_u)); it needs |S_w ∩ S_w'| <= 1 (hypothesis h2 of 951) to conclude that gates with |B_w| >= 2 are private. Inputs in V**_w are
exactly x_u, u ∈ S_w (needs h(0)=0 for y). The union-find ends in one block, so |HM_w| + Σ_T m_w(T) = d_w EXACTLY, and
s−1−base = #rest − Σ_{T∈SD}(m(T)−1) follows by counting. t3.py: identity, privacy and exactness asserted on all 2569 data circuits
(incl. cxT4 n=15, cxP2 n=16, which the note skipped): 0 failures; 165 circuits with a defect AND, 14 with excess > 0 (max 12),
min(rest−excess) = 1. It is an identity: both sides are s−1−base, so "defect repay" is 951 rewritten; it locates the deficit
(split ANDs) but proves nothing. Consistent with the weight barrier (it uses all forced zeros, incl. weight >= 2 tops), and by the
same token gives no handle on it. defect.py asserts only ">= base" where "==" holds; cosmetic.
