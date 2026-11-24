# REFEREE: PAPPUS-JUNK, Lemma D, Lemma R

Command: `python3 -I one-not/tools/kill_tests/referee_pappus.py one-not/data/witnesses/pappus_junk_gain.json`
(own script, brute force over all 512 inputs, written from the definitions in `opus-light-count.md` section 1; shares no code with light_cex.py / mu_light.py; reads only the json).
UC(D,Q) taken literally: OR gates g (all non-input OR wires), sets w with Q disjoint from S_w, a != b in S_w - D, Z contains Q, Z disjoint from D and S_w, face 1 / face 0 as stated.

## Numbers
* NOT gates: exactly 1. All 9 sums (outs[w] = OR of x over S_w) correct on all 512 inputs.
* Max |S_i meet S_j| = 1 (sets pairwise meet in at most one point).
* h(0) = 0; no point v has h(e_v) = 1; h is not identically 0 (light at Q = D = empty).
* |UC(empty,empty)| = 20, base = sum(|S_w|-1) = 18. UC wires: 27,28,33,34,38,39,43,44,48,49,53,54,58,59,63,64,68,69,73,74 (T = 27/28 pair-type gates, plus g_w, o_w).
* For every v = 0..8: gain of x_v := 1 = |UC(empty) \ UC(empty,{v})| = 5, cost sum over sets through v of (|S_w|-1) = 6 (so 5 < 6 at every v). The Lemma D count #{g in UC : v not in union of witness zero-points} is also 5 at every v (matches direct recomputation).
* gain of x_v := 0 = |UC(empty) \ UC({v},empty)| for v = 0..8: 2,2,1,0,2,0,1,0,1, against deg v = 3 at every v (all < 3).

## Verdicts
* **Witness (PAPPUS-JUNK): CORRECT.** Every claim in the notes reproduced exactly (20 vs 18, gain 5 vs cost 6 at all nine points, x := 0 gains 2,2,1,0,2,0,1,0,1 vs deg 3). I did not re-verify the paper proof of the Theorem (steps i-v); only the numbers, which are what refutes the count.
* **Lemma D: CORRECT.** A witness at (D,Q+v) has Z containing Q+v, Z disjoint from D and S_w, same a,b in S_w - D, so it is a witness at (D,Q) with v in Z, and v not in S_w is automatic from Z disjoint from S_w (w stays alive). Conversely a witness at (D,Q) with v in Z satisfies all conditions at (D,Q+v). Face conditions do not involve Q. Edge case v in D: no witness has v in Z, every g leaves, consistent. No gap.
* **Lemma R: CORRECT.** Uses (a) the NOT input h is built from AND/OR of inputs only (single NOT), hence monotone; (b) with the other gates monotone, C_1 >= real >= C_0 pointwise; (c) C_1 = real where h = 0 (NOT = 1), C_0 = real where h = 1 (NOT = 0). Case h(Z)=0: C_1(g)(Z) = real = 0, C_1(g)(Z+a), C_1(g)(Z+b) >= real = 1, face 1 holds. Case h(Z)=1: h(Z+a)=h(Z+b)=1 by monotonicity, C_0 = real at Z, Z+a, Z+b, face 0 holds. Relies on exactly one NOT gate, which is the setting.
