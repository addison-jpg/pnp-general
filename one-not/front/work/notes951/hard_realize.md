# hard_realize report (script: hard_realize.py; run from /home/user/pequalnp-proofs: python3 <script> <system-name> <cap> <seconds>)
size s = total gates incl. NOT; NOT forced to read a gate and live. Enumerations capped (cap/time), so counts are lower bounds on circuit numbers.
Results (circuits / BAD):
K4-e: base5: s=6 0, s=7 0, s=8 (base+3) 500/304
C5: s=6 0, s=7 0, s=8 1000/0
tri+pend: base4: s=5 0, s=6 0, s=7 800/450
Pasch: base8: s=9 0, s=10 (base+2) 177/177, s=11 310/281
P2: base7: s=8 0, s=9 (base+2) 446/284, s=10 700/446
rand0 n6 {035..}: base5: s=6 0, s=7 (base+2) 320/109, s=8 400/181
rand1 n7 (4 edges): base4: s=5 0, s=6 0, s=7 320/0
rand2 n6: base5: s=6 0, s=7 320/0, s=8 400/0
rand3 n7: base4: s=5 0, s=6 (base+2) 90/30, s=7 320/124
Conclusion: no live circuit exists at base+1 (SAT empty, consistent with Theorem X + live argument), so BAD is never realized at base+1.
BAD IS realized at base+2 (Pasch: every circuit found is BAD; P2, rand0, rand3 too), so BAD does not force extra gates beyond base+2.
Typical BAD h: two-variable OR (x_a v x_b) or similar with 3-4 hard sets (e.g. Pasch h=x2 v x5, hard (012),(034),(135)).
