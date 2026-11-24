# mergefrac_fable.md — referee of Lemma M + attack on MergeFrac (Fable). Restart-safe log. Code: w9/mf/
Tags: PROVED / CHECKED / CONJECTURE / REFUTED.

## M0 STEP 1 — referee of Lemma M and the load identity
LEMMA M (statement as refereed). Circuit: wires = inputs x_0..x_{n-1}, then gates in topological order, fan-in-2 AND/OR and any number of
gates N = NOT(h) whose input wire h is a MONOTONE function. Let S be a set, |S| >= 1, and o a wire with o(z)=0, o(z+e_u)=1 for all u in S
(here z is any point with z∩S = ∅). V_z = wires with value 0 at z; for g in V_z, B(g) = {u in S : g(z+e_u)=1}. Process gates in circuit order
with a union-find on S; M_z = OR gates g = s∨t in V_z with B(s), B(t) nonempty and in different current blocks (then merge the two blocks).
Then |M_z| = |S|-1 exactly, and M_z ⊆ {OR gates g <= position of o, g(z)=0, g(z+e_u)=1 for >= 2 u}.
PROOF (checked line by line). Invariant I: after processing a wire g in V_z, B(g) is contained in ONE current block (or is empty).
 (1) input x_v in V_z: B = {v}∩S, a singleton or empty. (2) OR g = s∨t in V_z: g(z)=0 forces s,t in V_z, and B(g) = B(s) ∪ B(t) pointwise;
 by I each of B(s), B(t) lies in one block; if both nonempty and the blocks differ, g is counted and the blocks are merged; in all cases I holds
 for g afterwards (blocks only grow, so I is preserved for earlier wires). (3) AND g = s∧t in V_z: one input, say s, is in V_z, and
 g(z+e_u)=1 => s(z+e_u)=1, so B(g) ⊆ B(s): I holds. (4) N = ¬h in V_z: h(z)=1, h monotone => h(z+e_u)=1 => N(z+e_u)=0: B(N) = ∅.
 Finally o in V_z with B(o) = S, so by I all of S is one block when o has been processed: exactly |S|-1 merges happened up to o, and no merge can
 happen after (one block). Each merge gate g has |B(g)| >= 2. QED.
 HYPOTHESES ACTUALLY USED: (a) gates in topological order; (b) every NOT input monotone IN THE DIRECTIONS e_u, u in S, AT z (h(z)=1 => h(z+e_u)=1)
 — automatic for one NOT; with several NOTs Lemma M FAILS in general (N2 = ¬N1 is not antitone); (c) only output w correct, and only at the
 |S|+1 points z, z+e_u. NOT used: Good condition, correctness of other outputs, h(0)=0, cleanness, |S∩S'| <= 1. No extra hypothesis is needed.
 The merge set depends on the gate ORDER (not only on the DAG) — any topological order works for the lemma.
LOAD IDENTITY (PROVED, trivial): Σ_g load(g) = Σ_w Σ_z μ_w(z) |M_z(w)| = Σ_w d_w Σ_z μ_w(z) = base; load lives on OR gates only (M_z ⊆ OR gates).
 Hence MergeFrac => base <= #{OR gates with positive load} <= #OR gates.
CHECKED (independent re-implementation w9/mf/core.py, numpy truth tables, not sharing code with w9/chist): n <= 7: 2555 circuits x 2 gate orders
 (given + 1 random topological re-ordering): |M_z(w)| = d_w for all (w,z), invariant I never violated, both inputs of a V_z OR gate in V_z; and
 MergeFrac LP optimum L* <= 1 on all 5110 runs (max 1.0).
