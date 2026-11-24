# Report from a parallel Opus agent (scaffold side) on the cone-D target. NOT proved, no counterexample.
(Its lemmas were brute-force checked by that agent on ~9,000 circuits, n <= 5; not independently re-verified.)

Notation: U={h=1}, L={h=0}, A_w={u: w(e_u)=1}, P={u: h(e_u)=1}, 'N-cone set' = N ∈ cone(o_S).

## Proved (short proofs)
L1. If h(e_u)=1 for all u then C0 is correct. So under 'C0 wrong', Good_i(Q) ⟺ N ∉ cone(o_i) ∨ h(z_Q)=0.
L2. y <= y', h(y)=h(y') ⇒ w(y) <= w(y') for every wire (same monotone circuit C0 or C1); for N-free wires no condition on h.
L3. Q ⊆ Q'', Q Good ⇒ Q'' Good and D_cone(Q,S) ⊆ D_cone(Q'',S). Min attained at inclusion-minimal Good Q; Q=S for easy or N-free S.
L4. w ∈ D_cone(Q,S), Q Good ⇒ A_w ⊆ Q.
L5. S easy ⇒ P ⊆ S.
L6. With Q_S=S for easy/N-free S: a gate in D_cone(Q_S,S) ∩ D_cone(Q_S',S') forces both hard N-cone sets,
    |S∩Q_S'| >= 2 and |S'∩Q_S| >= 2.
Cor 7. If every pair of hard N-cone sets has inclusion-minimal Good Q's with |S∩Q_S'| <= 1 or |S'∩Q_S| <= 1,
    the D's are disjoint and exclude N, so Σ min|D| <= s-1.

## New tool: generalized test systems
For S: a point z and points p_u (u∈S) with (T1) z=0 on S, (T2) p_u ⊆ z ∪ {u}, u ∈ p_u,
(T3) N ∉ cone(o_S) or h(z)=0 or |{u∈S: h(p_u)=0}| <= 1.
D_σ(S) = gates with w(z)=0 and >= 2 u with w(p_u)=1.
Lemma G: |D_σ^cone(S)| >= |S|-1 and N ∉ D_σ(S).
Lemma Sep: b∈S' is 'excluded by σ' if p'_b <= z and (not(h(z)=1 ∧ h(p'_b)=0) or one of S,S' is N-free);
if at most one b∈S' is not excluded then D_σ^cone(S) ∩ D_σ'^cone(S') = ∅ (by L2).
Thm 8: test systems for all sets, each pair separated in one direction ⇒ s >= 1 + Σ|D| >= base+1.

Types: M (easy/N-free): z_S, e_u. A(Q): z_Q, e_u. B (hard N-cone): z = z_S (in U), p_u = e_u for u∈P,
p_u = z_{S∖{u}} for u∉P (all in U, so T3 holds).
Separation table: N-free vs anything: always. A(Q) vs A(Q'): |S∩Q'| <= 1 or |S'∩Q| <= 1.
A-or-easy S vs B S': |S ∖ (P∖S')| <= 1. B vs B: |S' ∖ (P∖S)| <= 1 or |S ∖ (P∖S')| <= 1.
Cor 9: if the hard N-cone sets can be labelled A(Q_S) or B with every pair satisfying the table, s >= base+1.
A wire w >= h (h itself, x_c ∨ h) has w(z_S) >= h(z_S) = 1, so it is never in D_B(S): type B kills the observed doubles.

## Negative (verified by that agent)
1. No choice depending only on (sets, h) always separates: 9 of 1,162 (graph,h) pairs at n=4 fail
   (e.g. K4 with h minterms {0,2},{1,2},{0,3},{1,3},{2,3}); 4,569 of 197,054 at n=5. The proof must use circuit correctness.
2. Type B alone has doubles: K4, h=Th_2, T=Th_3, o_S=(x_u∨x_v)∨(T∧x_v)∨(N∧x_u), s=41, excess 9 under B, 0 under A.
3. Per-set minimizers are not automatically disjoint.
4. Circuit-dependent choice: SOME choice of generalized systems has excess 0 on all 33,096 tested circuits,
   incl. 117 where the min-choice has a double.

## Gaps
(Gap-G) every correct one-NOT circuit has test systems with pairwise disjoint D^cone (then Lemma G gives s >= base+1).
Only failing pairs: hard N-cone S,S' where no A/A choice has |S∩Q'| <= 1 or |S'∩Q| <= 1 AND both S∖(P∖S') and
S'∖(P∖S) have >= 2 elements. Candidates: kill points, or a circuit-dependent A/B choice per set. R1 unproved.
Stress (scaffold): widened DC + R1, essential, adversarial minimizer, base+5..+7: ~1.9k circuits, 0 doubles, 0 failures.
