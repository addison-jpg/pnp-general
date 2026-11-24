# w5 tight-case mining (report)

Data: 4161 circuits meeting hyps 1-4 (h(0)=0, >=2 hard, clean, C0/C1 wrong), K4-e / C5 / gadget
(base+3..+7; P2/tri generation too slow, only 4 P2 hits, not used). Own SAT runs (w5_gen.py: 129 K4e, C5 34, gad 18) plus
4083-row dump /tmp/w5ess.jsonl from a concurrent run (K4e base+5..+7). Script: w5_tight.py (analysis), w5_gen.py (generator),
w5_chk.py (independent re-verification of the violator).

## 0. HEADLINE: the charge inequality as stated is FALSE
K4-e, s=12 (base+7), clean, correct, C0 wrong, C1 wrong, h(0)=0, 5 hard sets, Sum min|D| = 13 > 12 (slack -1). Unique one in 4161.
Re-verified independently (correct on all 16 inputs, no two wires equal, C0/C1 both fail).
 w4=or(0,1) w5=or(0,2) w6=or(1,3) w7=or(0,6) w8=or(2,4)=h w9=not(8) w10=or(0,9) w11=or(3,10)
 w12=and(7,10) w13=or(1,2) w14=or(12,13) w15=and(11,14);  outputs {01}->w4 {02}->w5 {03}->w15 {12}->w13 {13}->w6
 per set min|D| (unique minimizer Q): {01}:{4,8} {02}:{5,8} {03}:{7,12,14,15} (Q=all) {12}:{8,13} {13}:{6,7,14}
 c: 8 counted 3x, 7 and 14 counted 2x, c=0 only for N=w9, w10, w11 (all above N): #c0=3 < 4 = Sum(c-1)^+.
Hence "Sum_w min_Q |D(Q,S_w)| <= s" with independent Q_w cannot be proved; the goal s>=base is still true there (12>=5).
(Note it needs h = a plain 3-input OR x0|x1|x2 shared by 3 sets; the 4th/5th sets pay 8 again.)

## 1. Slack distribution (all 4161): -1:1, 0:3, 1:24, 2:70, 3:240, 4:1436, 5:1251, 6:870, 7:266.
Slack-0 examples exist (K4e base+7), all with a DEAD gate that is double counted (dead gates make slack cheap).
Without dead gates (995 circuits): min slack -1 (the violator, which has no dead gate), next 1.

## 2. Candidate invariants (holds / total, all 4161; in brackets the 995 dead-free)
SURVIVE everything:
 D  NOT gate itself has c=0 : 4161/4161 (995/995)  [trivial: D needs >=2 unit ones; NOT=0 at e_u for Good(Q) via du or z_Q true]
 M  every double-counted gate (c>=2) is an OR gate : 4161/4161  (never an AND)
 P  max c <= 3 : 4161/4161
 R  #(c=0 gates) >= 2 : 4161/4161
FAIL (concrete counterexamples are printed by `python3 w5_tight.py ...`):
 G  #c0 >= Sum(c-1)^+ (= slack>=0): 4160/4161  FAILS exactly on the violator above
 A  double-counted gates lie above N: 2045/4161 (h itself and other ORs are double counted, e.g. h=w8 counted 3x)
 B  #c0 in cone(h)+N >= hard-1: 427/4161 ;  E h-gate has c=0: 722/4161 ;  F every c0 live gate in cone(h)+N+above: 897/4161
 H  #c0 not above N >= hard-1: 3196/4161
 C  Sum(c-1)^+ <= #AND above N: 4027/4161 ; C2 (<= #gates above N): 4132/4161 (fails slack 0/1/2 circuits) ; L (c0 above N or N): 4131/4161
 I  #c0 in cone(h)+N >= #dbl gates: 4073 ; J: 4032 ; Q (#c0 >= hard-1 + Sum(c-1)^+): 4023
Role of c=0 gates (4161 circ): NOT 4161, OR above N 5991, AND above N 2740, other AND 3376, other OR 2949, below h 753, h 722, dead 1712.
Double-counted gates: other OR 1966, above-N OR 131, h 119, dead 134, below_h 2. So double counting is mostly ordinary
"shared prefix OR" gates (an OR touching two sets' unit pairs, zero at both z_Q), and h itself.
Multiple minimizers: only 3 sets in 4161 circuits; irrelevant.

## 3. Interpretation
No gate-role invariant survives; the only surviving facts (D,M,P,R) are too weak, and the exact slack>=0 fails once. The
natural accounting (c=0 gates cover c>=2 excess) breaks because the surplus c=0 gates are exactly the gates above N
(w10,w11 here) which are only ever 'unused' when a hard set's cheapest Q is the full set Q=[n]; here Q=[n] for set {03} makes D contain
the whole AND chain 12,14,15 while 7,14 are re-used by {13} and 8 by three sets.
A proof therefore cannot use independent per-set minimizers verbatim: either (a) charge hard sets with a correlated Q
(e.g. sets sharing h's cone choose the same Q), (b) use Sum over sets of min|D| minus a global credit for N-cone gates
(here a credit of 1 fixes it), or (c) prove s>=base by another route (the circuit has 12 >= 5 with huge room).
No sketch of why an invariant holds is offered since none of the strong ones survive.
