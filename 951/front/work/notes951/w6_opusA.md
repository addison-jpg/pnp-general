# w6_opusA: frame theorem plus a cost bound (proved), special cases closed, an exact obstruction

Notation: Q is a set of variables; z_Q is the point that is 0 on Q and 1 elsewhere. Every wire is F_g(x, N(x)), where F_g is monotone in (x, N).

## 1. Frame Lemma (proved; no hypotheses beyond one NOT)
A frame for set S is a point P = z_Q with Q ⊇ S, plus atoms y_u (u ∈ S), such that:
- (L1) y_u ∩ Q = {u};
- (L2) if N(P) = 0 and N is in cone(o_S), then N(y_u) = 1 for at most one u.

Then cone(o_S) contains at least |S|-1 "merge" OR gates g with g(P) = 0.

Proof: union-find on S over the gates of cone(o_S) in order. For a wire i with i(P) = 0, let B(i) = {u : i(y_u) = 1}.
- Invariant: B(i) lies in one block.
- Leaves: an input x_v with v ∈ Q has |B| ≤ 1 by (L1). N, if it is 0 at P, has |B| ≤ 1 by (L2).
- OR gate a∨b that is 0 at P: a and b are both 0 at P, so B = B(a) ∪ B(b). If these lie in different blocks, merge them and charge the gate.
- AND gate that is 0 at P: some input c is 0 at P, and B ⊆ B(c).
- Output: o_S(P) = 0 and B(o_S) = S.

Only OR gates are ever charged.

Special cases of frames:
- Unit frames (y_u = e_u). Every hitting Q (h(z_Q) = 0) gives one; that is main_inv.
- New: Q = S is a valid frame when at most one u ∈ S has h(e_u) = 0. More generally, an atom may be e_u ∨ M for a minterm M of h that avoids Q \ {u}.

## 2. Collision bound (proved)
Comparability: if y ≤ P and (N(y) ≤ N(P), or g is not downstream of N), then g(y) ≤ g(P).

Let g be charged by both w and w'. For w, call atom u bad (against w') if y^w_u is not comparable with P_{w'}; write bad_w(w') for these atoms. Every comparable atom has g(y) ≤ g(P_{w'}) = 0, so B_w(g) ⊆ bad_w(w').

So g is a w-merge of two blocks that both meet bad_w(w'). Each such merge lowers the number of blocks meeting bad_w(w') by 1. Hence:

**#collisions(w, w') ≤ cost(w, w') := (min(|bad_w(w')|, |bad_w'(w)|) - 1)^+.**

Since k - 1 ≤ C(k, 2) for k ≥ 1, the excess satisfies excess ≤ Σ_pairs cost. N and every AND gate are uncharged. Therefore:

**(MASTER) s ≥ base + 1 + #AND - Σ_{pairs} cost(w, w'),** for any choice of frames.

In the target case (h(0) = 0 and an N-output exists), #AND ≥ 1: an OR-only path from N to an output o_w would give o_w ≥ N, so o_w(0) = 1. Hence **s ≥ base + 2 - Σ cost**, and **s ≥ base follows whenever some frame assignment has Σ cost ≤ 2.**

Unit frames with Q = S_w for easy and non-N sets always have cost 0 against any unit frame (the Theorem X argument). Theorem X is the case Σ cost = 0.

## 3. Closed special cases (complete proofs, under the ONLY-SORRY hypotheses)

**(A) Exactly two hard N-sets a, b.** For each hard set, let τ_a be the transversal number of the family of h-minterms contained in S_a \ S_b, and define τ_b symmetrically. Take Q_b = S_b ∪ ([n] \ (S_a ∪ S_b)) ∪ T_a, where T_a is a minimum transversal of those minterms. This Q_b is a hitting set: a minterm that avoids S_b either has an element outside S_a ∪ S_b or lies inside S_a \ S_b. Also |S_a ∩ Q_b| = |S_a ∩ S_b| + τ_a. All other sets use unit frames with Q = S and cost 0. Hence

**s ≥ base + 2 - (|S_a ∩ S_b| + min(τ_a, τ_b) - 1)^+.**

So s ≥ base whenever |S_a ∩ S_b| + min(τ_a, τ_b) ≤ 3. In particular s ≥ base + 2 when h has no minterm inside S_a \ S_b (or none inside S_b \ S_a).

**(B) h = x_a ∨ x_b, any linear system.** Use unit frames with Q = S ∪ {a, b} for hard sets. By hab L1, only crossing pairs collide: S ∋ a, S' ∋ b, S ∩ S' = {c} ∉ {a, b}. For such a pair the bad sets are {a, c} and {b, c}, so the cost is 1. Hence **s ≥ base + 2 - #crossing pairs**, and s ≥ base when there are at most 2 crossing pairs. That covers the K4-e double count. A crossing set of size 2, S = {a, c}, can instead use the frame Q = S with atoms e_a, e_c, which has cost 0.

**(C) All instances with n ≤ 4** (h monotone with h(0) = 0; every linear system with sets of size 2–3, which is all of them at n = 4; every set treated as an N-set, which is the worst case). An exhaustive search over frames (w6A/mincost.py) finds min Σ cost ≤ 2 in all 6012 instances that have ≥ 2 hard sets: 5993 cost 0, 18 cost 1, 1 cost 2 (K4 with h = threshold-2). So s ≥ base for n ≤ 4.

The search is a finite computation, not a hand proof. The two lemmas it relies on are proved above.

## 4. Checks
- MASTER was asserted on all 391 data circuits that have ≥ 2 hard N-sets: 0 failures. The excess was ≤ 1 everywhere and never larger than #AND.
- The Frame Lemma with generalised atoms was checked on 22,878 (circuit, set, random frame) triples: 0 failures.
- Random samples at n = 5:
  - graphs: cost 0 in 4543 instances and cost 1 in 4.
  - mixed systems with sets of size 2–4: cost 0 in 17412, cost 1 in 721, cost 2 in 41, cost 3 in 1.

## 5. Gaps (honest)
1. **The frame method alone cannot finish.**
   - With h = x_a ∨ x_b, triples S_i = {a, c_i, d_i} and S'_i = {b, c_i, e_i}, the exact minimum frame cost is k for k = 1 and k = 2 (computed in w6A/kpair.py). From the cost of 1 per crossing pair, it should be k for every k, but that is not proved.
   - At n = 5, one instance has minimum cost 3: minterms {0,2},{1,2},{0,3},{1,3},{0,4},{2,4}; sets (12),(14),(34),(013),(024).
   - So the AND payment is unavoidable. What remains to prove is **#AND + #uncharged OR ≥ Σ cost - 1**. In the crossing-pair setting, the collision gates g_c have B(g_c) = {a, b, c} exactly, so each c gives at most one collision gate. Each g_c has an AND on every path to o_S that kills e_b, and one on every path to o_S' that kills e_a.
   - It is not proved that distinct crossing points c get distinct kill ANDs. Hand attempts at sharing an AND always broke the output at e_b ∨ e_{c'}, which suggests that point is where a proof should look.
2. Claim (1) from the brief, "g ≥ h with g = x_c ∨ h", was not proved and is not needed above.
3. Section 3(C) is computational, not a hand proof.

## Files
w6A/assign.py, w6A/mincost.py, w6A/run5b.py, w6A/kpair.py, w6A/uf.py, w6A/framechk.py (all in the scratchpad).
