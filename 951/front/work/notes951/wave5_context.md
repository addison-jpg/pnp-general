# L-meta-951: exact remaining lemma (context for agents)

## Setting
Sets S_1..S_m ⊆ [n], |S_i| >= 2, |S_i ∩ S_j| <= 1. Circuit: gates in order; wire i < n is input x_i,
wire n+k is gate k; gates are AND/OR of <= 2 earlier wires, plus at most one NOT N = ¬h (h an earlier wire,
monotone in x). Outputs o_w = OR(S_w) on all 2^n inputs. s = #gates, base = Σ(|S_w| - 1). GOAL: s >= base.

## Definitions (exactly as in the Lean)
- z_Q = input 0 on Q, 1 outside Q. e_u = unit vector.
- Good(Q): every gate is AND/OR, or the NOT is true at z_Q (h(z_Q)=0), or the NOT is false at e_u for EVERY u ∈ [n].
- D(Q, S) = { gate wires i (n <= i < n+s) : wire_i(z_Q) = 0 and #{u ∈ S : wire_i(e_u) = 1} >= 2 }.
- Lean shows (main_inv): for Good(Q) with Q ⊇ S, |D(Q,S)| >= |S| - 1.
- So it suffices: Σ_w min_{Q ⊇ S_w, Good(Q)} |D(Q, S_w)| <= s.   (Q_w chosen independently per set.)

## Already formally proved in Lean (do NOT redo)
- NOT dead / h(0)=1 (NOT constant 0): all Q Good, sets pairwise |∩|<=1 give disjoint D's.
- All sets easy (h(z_S)=0): Q=S works, D's disjoint.
- At most one hard set (Theorem X: Q_w ⊇ S_w with pairwise |S_a ∩ Q_b| <= 1 or |S_b ∩ Q_a| <= 1 => disjoint D's).
- Cleanup: a gate whose function equals an earlier wire (inputs included) can be deleted (readers rerouted): induction on s.
- Removable NOT: if replacing N by constant 0 (C0) keeps every output correct, or by constant 1 (C1) does, the circuit is a
  NOT-free circuit of the same size: monotone bound applies.

## THE ONLY REMAINING CASE (charge_hard)
Assume all of:
1. h(0) = 0 (NOT true at the all-zero input);
2. at least two hard sets (no single w0 with all other sets easy), where S is hard iff h(z_S) = 1;
3. CLEAN: no gate computes the same Boolean function as an earlier wire (inputs included);
4. C0 WRONG: replacing N by 0 breaks some output; C1 WRONG: replacing N by 1 breaks some output.
Prove: Σ_w min_{Q ⊇ S_w, Good(Q)} |D(Q, S_w)| <= s.

Useful consequences of 4: g0 <= f <= g1 everywhere (outputs monotone in N); real circuit = C1 on {h=0}, = C0 on {h=1}.
C0 wrong => ∃ output w, x with h(x) = 0, f_w(x) = 1, g0_w(x) = 0.  C1 wrong => ∃ w', y with h(y) = 1, f_w'(y) = 0, g1_w'(y) = 1.

## Data (SAT-generated correct circuits, n <= 7)
- ~1,300 circuits satisfying 1-4 (K4-e, C5, gadget {x,a},{x,b},{c,d}, P2, triangle; base+2..+7): 0 violations; tightest slack 0
  (K4-e = sets (01)(02)(03)(12)(13), base+7).
- Without 4: 8+ clean violators (slack -1 / -2), ALL with C0 correct or C1 correct (removable NOT).
- 'No gate is in two D's' is FALSE even for clean essential circuits (double counting happens, but the sum still fits).
- No circuit with a live NOT exists at size <= base+1 in any tested system.

## Tools (run from /home/user/pequalnp-proofs)
- /tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/chk/gen_clean.py SYSTEM EXTRA CAP SECS
  (systems K4e, C5, gad, P2, tri): generates clean live-NOT circuits via SAT and reports slack for essential ones.
  Its function slack(n, sets, gates) computes s - Σ min|D| with gates as (op, a, b) tuples ('not', a, a).
- Python + pysat available. One heavy process at a time, keep each run under 5 minutes. No Lean.
