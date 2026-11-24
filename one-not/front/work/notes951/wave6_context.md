# L-meta-951, state for wave 6 (supersedes wave5_context.md where they differ; read that file too for basics)

Folder: /tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/

## Setting (short)
Sets S_w ⊆ [n], |S_w| >= 2, pairwise |∩| <= 1. Circuit of AND/OR gates (fan-in <= 2) + one NOT N = ¬h (h monotone).
Outputs o_w = OR(S_w) everywhere. s = #gates, base = Σ(|S_w|-1). GOAL: s >= base.
C1 = circuit with N:=1 (outputs g1 >= f, exact on {h=0}); C0 = N:=0 (g0 <= f, exact on {h=1}).
z_Q = 0 on Q, 1 outside. e_u unit vector. S hard iff h(z_S)=1. N-set: output cone contains N.

## Formally proved in Lean (all compile; do not redo)
NOT dead / h(0)=1; all sets easy; cleanup (gate equal to an earlier wire is deletable); unread gates deletable;
removable NOT (C0 correct or C1 correct => monotone case); Theorem X and its cone-restricted version:
if zero sets Q_w ⊇ S_w exist with Good and pairwise (|S_a∩Q_b| <= 1 or |S_b∩Q_a| <= 1) then s >= base;
<= 1 hard N-set.
Counting lemma (main_inv): for any monotone-or-Good circuit and Q ⊇ S with output false at z_Q and true at e_u (u ∈ S):
#{gate wires i : wire_i(z_Q)=0 and wire_i true at >= 2 units of S} >= |S|-1. This holds for the masked circuit
(gates outside cone(o_w) replaced by constants), giving D_cone(Q,S_w).

## THE ONLY SORRY (current shape)
Assume: clean (no gate equals an earlier wire as a function), every gate read or an output, C0 wrong and C1 wrong,
h(0)=0, >= 2 hard N-sets, no zero-set family satisfies the pairwise condition, AND s < base. Derive False.
(Equivalently prove s >= base in this case by any means. A sufficient route: Σ_w min_Q |D_cone(Q,S_w)| <= s.)

## Data
- ~335k SAT-generated correct circuits (n <= 7, sizes base+2..base+7): Σ_w min_Q |D_cone| <= s - 1 always.
- No circuit with a live NOT exists at size <= base+1 in any tested system (many exhaustive UNSATs).
- Double counts (a gate in D_cone of two sets) are rare (~0.3%), only between hard N-sets; in essential circuits every
  observed doubly counted gate equals x_c ∨ h (c = shared point of the two sets); in removable-NOT circuits it can be h itself.
- Rule R1 holds on all data: #(gates that are N or downstream of N, counted by no set) >= excess + 1,
  excess = Σ_g (mult(g)-1)^+.
- Typical double: K4-e sets (01)(02)(03)(12)(13): w4=x0|x2, w5=x0|x3 (=h), w6=¬w5, w7=x1|x2, w8=x1|w6, w9=x1|w5
  (counted by (01),(13) with Q={0,1,3}), w10=x0|w8, w11=x3|w8, w12=w9&w10 (o01), w13=w9&w11 (o13).

## Known dead ends (do not retry)
Full (non-cone) D counting: false. 'No double count ever': false. Per-read substitution of N: false at base+5.
Local top-down AND elimination (Wegener) with the NOT: fails for hard outputs. First-kill-AND injection: one AND
can kill for many. Variable-fixing induction: fan-out < degree obstruction.

## Tools
chk/conedbl.py: analyse(c) -> (slack, {gate: mult>1}, per-set (S, (Q, D), isNset)); circuits in chk/c.jsonl,
chk/k.jsonl, /tmp/w5ess.jsonl (JSON lines: n, sets, gates [op,a,b] / ['not',a], outs). chk/gen_clean.py generates more
(run from /home/user/pequalnp-proofs). Python + pysat ok, one process at a time, < 5 min each.
No Lean, no git commit/push, no websites.
