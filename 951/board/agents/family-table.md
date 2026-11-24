# Family table: which family F(Q) keeps MU and STEP (D = empty)

Script: `951/tools/kill_tests/family_table.py` (about 1 s). Command, from the repo root:
`python3 -I 951/tools/kill_tests/family_table.py 951 > out.md`
Definitions: F elements are OR gates g with witness (alive w at Q, Z ⊇ Q, Z ∩ S_w = ∅, atoms u ≠ u' in S_w).
F1 = UC (face 1 / face 0 as in opus-light-count.md §1). F2 = real g(Z)=0, real g(Z+u)=g(Z+u')=1.
F3 = F1 with face 1 atoms each needing real g(Z+a)=1 or h(Z+a)=0 (face 0 unchanged).
F4 = F1, F5 = F2, each with the witnessing w required to have g in the syntactic cone of outs[w] (per witness).
F6 skipped: the spec was unclear and I did not invent one.
Instance = (circuit, Q) with some alive set (S_w ∩ Q = ∅, |S_w| ≥ 2). MU: |F(Q)| ≥ base = Σ_alive (|S_w|-1).
STEP: some alive point v (unfixed, in an alive set) with |F(Q) \ F(Q+v)| ≥ Σ_{alive w ∋ v}(|S_w|-1)
(a v in no alive set has cost 0 and is excluded, else STEP is vacuous). Corpus = 51 distinct circuits n ≤ 8
under 951/ (one NOT, correct, sets pairwise meeting in ≤ 1 point), witness files excluded; all 2^n values of Q.

### (a) corpus
| family | instances | MU ok | STEP ok | MU fails | STEP fails |
|---|---|---|---|---|---|
| F1 | 1125 | 1125 | 1125 | 0 | 0 |
| F2 | 1125 | 1125 | 1125 | 0 | 0 |
| F3 | 1125 | 1125 | 1125 | 0 | 0 |
| F4 | 1125 | 1125 | 1125 | 0 | 0 |
| F5 | 1125 | 1125 | 1125 | 0 | 0 |

### (b) barrier suite (data/witnesses/*.json)
| family | instances | MU ok | STEP ok | MU fails | STEP fails |
|---|---|---|---|---|---|
| F1 | 404 | 404 | 403 | 0 | 1 |
| F2 | 404 | 404 | 404 | 0 | 0 |
| F3 | 404 | 404 | 404 | 0 | 0 |
| F4 | 404 | 404 | 404 | 0 | 0 |
| F5 | 404 | 404 | 404 | 0 | 0 |
- F1 STEP smallest: pappus_junk_gain.json Q=000000000 |F|=20 base=18 bestgain-cost=-1


### pappus_junk_gain.json at Q = empty
| family | |F| | base | best gain-cost | MU | STEP |
|---|---|---|---|---|---|
| F1 | 20 | 18 | -1 | True | False |
| F2 | 20 | 18 | 0 | True | True |
| F3 | 20 | 18 | 0 | True | True |
| F4 | 20 | 18 | 0 | True | True |
| F5 | 20 | 18 | 0 | True | True |

### Families keeping MU on every instance (corpus + suite) AND STEP on pappus at Q=empty
- F1: MU everywhere=True, pappus STEP=False -> fail
- F2: MU everywhere=True, pappus STEP=True -> PASS
- F3: MU everywhere=True, pappus STEP=True -> PASS
- F4: MU everywhere=True, pappus STEP=True -> PASS
- F5: MU everywhere=True, pappus STEP=True -> PASS

Notes. F1 reproduces the known failure on pappus_junk_gain at Q = empty (gain 5 < cost 6, best gain-cost = -1).
On that instance F2-F5 reach exactly gain = cost (slack 0), so STEP is tight there; they also tie |F| = 20, base 18.
All five families keep MU on all 1125 corpus + 404 suite instances. F2-F5 pass STEP on every instance tested,
but the suite is only 7 circuits (only pappus is a known STEP breaker for F1), so this is evidence, not proof.
F4/F5 (cone) never differ from F1/F2 on these instances in the counts above.
