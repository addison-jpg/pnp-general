# w5_witness report
No proof via witnesses. Instead: the stated charge_hard inequality is FALSE, with a concrete circuit; and a repair (cone restriction) passes all data.

Counterexample (n=4, K4-e sets 01,02,03,12,13, s=12=base+7; wires 4..15):
4=or(0,1) 5=or(0,2) 6=or(1,3) 7=or(0,6) 8=or(2,4) 9=NOT 8 10=or(0,9) 11=or(3,10) 12=and(7,10) 13=or(1,2) 14=or(12,13) 15=and(11,14); outs=[4,5,15,13,6].
Correct; clean (all 16 wire truth tables distinct, inputs included); h=wire 8=x0|x1|x2 (hard for every set, h(0)=0); C0 wrong, C1 wrong (neither removes NOT).
Good(Q) forces Q ⊇{0,1,2} (N(e_3)=1 so no vacuous Good). min|D|: sets 01:{4,8}, 02:{5,8}, 03:{7,12,14,15}, 12:{8,13}, 13:{6,7,14}: total 2+2+4+2+3 = 13 > 12 = s. Slack -1.
Multiplicities: gate 8 (=h) x3, 7 x2, 14 x2; uncounted 9(N),10,11. Found by /tmp/claude-0/.../scratchpad/w5gen.py K4e 7 (gen_clean + dump), driver w5drv.py. 3 more circuits with slack 0 (similar: h gate counted 3x, one AND counted 3x).
So no rule "sum (c-1)^+ <= #uncounted" can hold for Lean's D: here sum(c-1)^+=4 > 3 uncounted.
Note: this circuit is far from tight for s>=base (12 vs 5); only the SUFFICIENT inequality fails.

Why: D counts gates outside cone(o_w). In the example, h (wire 8) is in D of sets 01,02,12 because h(z_Q)=0, h(e_u)=1 for u in S, but h is not downstream of o_w for... (it is an input of N, whose cone excludes it for outputs not using N).

Repair tested: D_cone(Q,S) = D(Q,S) ∩ cone(o_w). (a) Empirically |D_cone(Q,S)| >= |S|-1 for every Good Q ⊇ S: 43086 (circuit,set,Q) checks, 0 failures (3966 distinct clean essential K4e circuits, base+5..+7, incl. the above). (b) With min over Q of |D_cone|, slack s - Σ min over those circuits: min 3, distribution {3:2,4:65,5:1811,6:1738,7:350}; the slack -1 circuit becomes positive. Hard_kill.md item 1 argues the invariant proof (Theorem X union-find) is unchanged under cone restriction. Suggest: change Lean statement to cone-restricted D and prove Σ_w |D_cone| <= s; no tight cases seen, so more room (but double charging of gates in several cones persists, so a payment argument is still needed).
Witness-route status: C0-witness gives h(x)=0 with N needed; this does not prevent h's own gate being in D for hard sets (h(z_Q)=0 is exactly the Good condition) -- that is what produces the triple counting.
