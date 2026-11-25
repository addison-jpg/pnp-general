# Synthesis of F1 / F2 for the F2 step (dwV8p, owner's request: map the subtasks onto F1's failures)

Session session_01GmnDhdwV8pW4adQkj9Ei3M (dwV8p). Script: `research/one-not/work/notes951/lemmaK_referee/f2synth.py` (own code, imports
research/one-not/tools/w951; random correct one-NOT circuits n = 4-6 and every file in research/one-not/data/witnesses). Words: PROVED, CHECKED, OPEN.
F2(Q), gain(v), cost(v) as in the 12:46 DECISION. SEE(v) = {g ∈ F2(Q) : real g(Q+e_v) = 1}; SURV(v) = SEE(v) ∩ F2(Q+v);
K3(v) = {g ∈ F2(Q) : every witness of g at Q belongs to a set through v}.

## 1. One lemma for heavy and light v (PROVED; CHECKED 0 failures on 197,689 random instances + all witness restrictions)
F1*. g ∈ F2(Q+v) and real g(Q+e_v) = 1  =>  h(Q+e_v) = 0, C_0(g)(Q+e_v) = 0, C_1(g)(Q+e_v) = 1, and every witness Z' of g
at Q+v has h(Z') = 1 (world 0) for a set w' with v ∉ S_w' and h(top_w') = 1 (type A).
Proof: Z' ⊇ Q+e_v and real g(Z') = 0 while real g(Q+e_v) = 1; on {h = 0} real = C_1 is monotone, so h(Z') = 1; then
real g(Z') = C_0(g)(Z') = 0 gives C_0(g)(Q+e_v) = 0, so real g(Q+e_v) = 1 needs h(Q+e_v) = 0 and C_1 = 1 there.
It contains front A2's F1 (heavy v: SURV(v) = ∅) and research's K0, K1, K2 (light v: survivors are NOT-dependent type-A
world-0 servants). With opus-light-count's Lemma D (g dies iff no witness has v ∈ Z) every F1 failure is explained.

## 2. How the subtasks fit (each PROVED piece is cited, not reproved)
- SUPPLY. F2-desc (front A2, refereed): for each alive w ∋ v and u ∈ S_w \ {v}, the triple (Z = Q; v, u) on o_w descends to
  an OR gate of SEE(v). There are exactly cost(v) = Σ_{w ∋ v} (|S_w| − 1) such triples.
- DEATHS. SEE(v) \ SURV(v) ⊆ gain(v) by definition; SURV(v) is described by F1* (empty when v is heavy). K3(v) ⊆ gain(v)
  (research K3 = a case of Lemma D: a witness of a set through v never contains v).
- So the step follows from ONE count (OPEN):
  **SEE+K3: some alive v has |(SEE(v) \ SURV(v)) ∪ K3(v)| ≥ cost(v)**, i.e. the cost(v) star triples land on at least
  cost(v) distinct dying gates once K3 gates are added. A charging statement, no union-find and no world split.

## 3. Data (CHECKED)
| statement | random heavy | random light | witness files (4 Q each) | light witnesses, every light Q |
|---|---|---|---|---|
| the F2 step | 158,506 / 158,506 | 39,183 / 39,183 | 36 / 36 | 62 / 62 |
| SEE alone (no K3) | 158,493 (13 FAIL) | 39,183 | 33 (FANO-FORMULA, PAPPUS-JUNK fail) | 60 (FANO 1, PAPPUS-JUNK 1 fail) |
| **SEE+K3** | **158,506** | **39,183** | **36** | **62** |
| SEE at a HEAVY v | 156,967 (1,539 need a light v) | - | 18 / 23 heavy | - |
- Smallest SEE-alone failure (heavy; the K3 term is what is missing): n = 5, sets {0,1}, {1,2,3,4}, {0,2}, h = x1 | x4, Q = {0}:
  only {1,2,3,4} is alive, F2(Q) = {x1|x4, x2|x3, output}, cost = 3, |SEE(1)| = 2; x2|x3 dies by K3.
- research's repaired LIGHT-STAR also holds on all 62 light witness restrictions; SEE+K3 is a second, pool-free form of
  the light step that ALSO covers the heavy step.
- Choose v freely: 'heavy v' is not universal for SEE (1,539 random instances), matching the board's '∃ v, not every heavy v'.

## 4. Suggested next step
Prove SEE+K3 for heavy v first (SURV = ∅; F1 + F2-desc give membership and death, only the distinctness count is left; front
A2's G1 / GraphHeavyF2 is the natural source of distinct gates), then light v with F1* bounding the survivors.
