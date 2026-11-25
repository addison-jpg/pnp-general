# A2s: is B_w = {M_z(w)} a matroid base family? (data)
Code: /tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/w9/A2s/run.py (usage: python3 run.py files...). Outputs: out_main.jsonl, out_bad.jsonl, out_badT.jsonl; HARD4 circuit: hard4.json.
Method: truth tables as bigints; for each set w and each z (all 2^(n-|S_w|), z_v=0 on S_w) union-find over gates in order on wires 0 at z, block of wire = units u with wire=1 at z+e_u; OR gate merges if its children's blocks lie in different classes. Anomalies counted (merge set size != |S_w|-1, or a merge joining >2 classes): 0 everywhere.
Basis exchange tested over all pairs. Union test sum_w (r_w(G)-r_w(A)) <= |G\A|: exhaustive over all 2^|G| A when |G|<=18, else 20000 random A (varied density) + A = unions of one M_z per set (subset of sets; fully enumerated when the product of family sizes+1 <= 20000, else 20000 random combos). A matmul computes r_w(A)=max_B |A∩B|.
HARD4 (n=6; sets {0,1,2,3},{0,4,5}; 9 gates): truth-table-checked correct as given (g14 = x0|x1|x2; chain ORs; set1 = (x0|x4)|x5).

## Named circuits (k=#sets, nb = |B_w| per set, mat = exchange axiom per set)
| circuit | n | gates | correct | nb | matroid | union viol (A tested) |
|---|---|---|---|---|---|---|
| hard4 | 6 | 9 | y | 1,2 | T,T | 0 (512 exh) |
| w8/cx1 | 9 | 22 | y | 3,3,2 | F,F,T | 0 (14800) |
| w8/cx2 | 7 | 18 | y | 2,2,2 | F,F,F | 0 (262144 exh) |
| w8/cx3 | 10 | 24 | y | 2,2,2 | F,F,F | 0 (15485) |
| w8b/cxr | 8 | 24 | y | 9,9 | F,F | 0 (15546) |
| w9/p/cxP1 | 9 | 38 | y | 3,1,1,1,1 | F,T,T,T,T | 0 (18863) |
| w9/p/cxP2 | 16 | - | skipped n>12 | | | |
| w9/p/cxP3 | 5 | 14 | y | 2,1 | F,T | 0 (exh) |
| w9/p/cxP4 | 6 | 16 | y | 4,2 | F,F | 0 (exh) |
| w9/p/cxP5 | 8 | 32 | y | 3,1,1,1,1 | F,T,T,T,T | 0 (17712) |
| w9/p/cxP6 | 9 | 43 | y | 4,2,2,1x6 | F, then all T | 0 (22203) |
| w9/fc/cfgI | 9 | 25 | y | 5,3,2 | F,F,T | 0 (15825) |
| w9/fc/cx44_0 | 7 | 30 | y | 2,2 | F,F | 0 (17237) |
| w9/fc/cx44_1 | 7 | 32 | y | 2,2 | F,F | 0 (17664) |
| w9/fc/cxT2 | 9 | 29 | y | 16,10,13 | F,F,F | 0 (17496) |
| w9/fc/cxT4 | 15 | - | skipped | | | |
| w9/fc/cxe3 | 7 | 45 | y | 2,2,2,1,2 | all T | 0 (19623) |
| w9/tw/cxtw3, cxtw3c | 9 | 36, 34 | y | 2 each | all T | 0 |
| w9/tw/cxtw4, cxtw4c | 11 | 55, 51 | y | 2 each | all T | 0 |
| w9/chist/cxU6, cxU8, cxU_6_4, cxU_8_4 | 14,18,16,20 | - | skipped n>12 | | | |
(rnd_fail.json in w9/p is an empty list.)

## Jsonl (n=4, small), all exhaustive over A
| file | circuits | correct | sets | sets with matroid B_w | violations | max |B_w| |
|---|---|---|---|---|---|---|
| w7/badT.jsonl | 63 | 63 | 271 | 271 | 0 | 2 |
| w7/bad.jsonl | 160 | 160 | 662 | 662 | 0 | 2 |

## Summary
- Matroid axiom fails (for at least one set) on 13 of the 19 evaluated named circuits (cx1, cx2, cx3, cxr, cxP1/3/4/5/6, cfgI, cx44_0/1, cxT2); holds for every set in hard4, cxe3, cxtw*, and all 223 small bad/badT circuits. Non-matroid examples are typically two disjoint-ish bases (cx2 set0: {4,6},{9,10}; cxP4: {3,6},{3,7},{6,7},{7,9}; cx44_0: {7,11,15},{16,17,18}), so B_w is in general NOT a matroid base family.
- Despite that, the union inequality Σ_w (r_w(G)-r_w(A)) <= |G\A| had ZERO violations in all tests (exhaustive for cx2, cxP3, cxP4, hard4, and all small ones; sampled+structured elsewhere).
- No anomalies to Lemma M (|M_z(w)| = |S_w|-1 always, merges always of exactly 2 classes).
