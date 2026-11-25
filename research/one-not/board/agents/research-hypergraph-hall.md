# research: Hall's theorem for hypergraphs vs MergeSDR (coord assignment, board 10:00; Lean target no_minCE_of_mergeSDR)

MergeSDR: pick one merge set M_{z_w}(w) (|M| = d_w, Lemma M) for every output w, pairwise disjoint.
Status words: TXT (statement read in a paper's text), MEM (standard statement from memory, not re-read), CHECKED (computed;
research/one-not/tools/research951/charging/sdr.py on the 26 shared instances of research/tools/w951/tests/instances).

## 1. Reformulation used by this literature (independent transversals)
Vertex classes V_w = the distinct merge sets of output w; graph H joins two members of DIFFERENT classes that share a gate.
MergeSDR <=> H has an INDEPENDENT TRANSVERSAL (one vertex per class, pairwise non-adjacent). This is exactly the Santa Claus /
max-min allocation setting (players = outputs, configurations = merge sets, items = gates): Boehmer & Huang, 'Integrality gap
of 3.4 for Santa Claus: a topology-based analysis', arXiv 2611.15392 (TXT, §1-2), following Haxell & Szabó, Combinatorica 45
(2025) and Asadpour-Feige-Saberi, ACM TALG ('Santa Claus meets hypergraph matchings'). Our MergeFrac is their configuration LP.

## 2. Exact sufficient conditions
- Aharoni's topological Hall theorem (TXT, Boehmer-Huang Thm 2): if η(H|Q) >= |Q| for every set Q of classes, H has an
  independent transversal. η = homological connectivity (+2) of the independence complex.
- Lower bounds for η (TXT, Boehmer-Huang Thm 3, Thm 5): Meshulam: every edge e is deletable (η(G) >= η(G - e)) or explodable
  (η(G) >= η(G ⋇ e) + 1, ⋇ = remove both ends and all their neighbours); Aharoni-Berger-Meshulam: η(G) >= Γ(G) (a fractional
  domination parameter over vector representations). Combinatorial corollary (MEM): η(G) >= γ̃(G)/2 (total domination).
- Haxell (MEM; 'A note on vertex list colouring', Combin. Probab. Comput. 10 (2001) 345-347): if every class has >= 2Δ(H)
  vertices, an independent transversal exists (tight: Szabó-Tardos).
- Aharoni-Haxell (MEM; 'Hall's theorem for hypergraphs', J. Graph Theory 35 (2000) 83-88; combinatorial precursor Haxell, Graphs
  Combin. 11 (1995) 245-248): families H_1..H_m of sets of size <= r; if for every I ⊆ [m] the union ∪_{i∈I} H_i has a matching
  of size > r(|I| - 1) (stronger version: a matching that cannot be pinned by r(|I| - 1) of its edges), then a system of
  disjoint representatives exists.

## 3. Do they apply here? (CHECKED on the 26 instances)
- MergeSDR HOLDS on all 26 (exact backtracking).
- Haxell's 2Δ condition: true on 7 of 26 only.
- Aharoni-Haxell matching condition with r = max d_w: FAILS on 25 of 26, almost always already for |I| = 2: members of one
  family overlap heavily, so ν(∪_{w∈I} V_w) is tiny. The numeric conditions are far too strong for this structure.
- Universal merges U(w) (gates in every member of V_w): pairwise disjoint on all instances (as stated by coord) but EMPTY for
  most outputs (non-empty sizes 1-2), so removing them does not rescue the numeric conditions.
- The topological condition (η) is the right strength (it is how the Santa Claus gap is proved) but needs structure-specific
  η bounds; the Santa Claus results lose a constant factor (gap 3.4-4), so no exact statement follows from them directly.

## 4. Structure that may make MergeSDR provable: the world split is almost a 2-SAT
- Per world (agents/research-concave-dual.md, research-charging.md §d): the world-1 family is a SINGLE set for most outputs
  (exceptions on the data: cxr, relfail1, r_v1, ce3) and the world-0 family has 1-5 members (more on cxT2/cxT4).
- If every output has exactly two candidates (one per world), MergeSDR is 2-SAT over the world choices c(w) ∈ {0,1}: each
  conflicting pair of candidates gives a clause ¬(c(a) = i ∧ c(b) = j). 2-SAT is unsatisfiable iff the implication graph has
  a variable and its negation in one strongly connected component (Aspvall-Plass-Tarjan 1979, MEM): a CYCLE CERTIFICATE.
  So a proof of MergeSDR can aim at: 'no implication cycle c(w) = 0 => ... => c(w) = 1 => ... => c(w) = 0', i.e. a chain of
  forced world choices around a cycle of outputs, which should contradict pairwise |S_a ∩ S_b| <= 1 + minimality.
- With several world-0 members the choice inside world 0 is the near-matroid part (exchange holds for 73 of 82 world-0 families),
  i.e. a matroid-intersection-type step (Rado / Edmonds), which IS exact; the cross-world part is the 2-SAT part.
- Proof template for an inductive SDR in Lean: Haxell's alternating-tree (augmenting) argument (Haxell 1995; used in all
  Santa Claus papers): add outputs one by one, and when the new output's candidates are blocked, grow an alternating tree of
  blocking candidates; the counting that ends the tree is where |S_a ∩ S_b| <= 1 and Lemma M would be used.
Suggested next checks (scaffold, cheap): (i) on the 15,300-circuit corpus, the fraction of outputs with a single world-1 member;
(ii) build the 2-SAT implication graph restricted to world representatives and confirm no contradictory SCC; (iii) record
the longest forced implication chain (the object a proof must rule out).

## 5. Follow-up (09:55): scaffold's 2-SAT data + a 'free candidate' test (CHECKED)
- scaffold (75,619 one-NOT circuits, f15/twosat.py): |F^1| = 1 for 87.25% of (circuit, set) pairs (never 0: z = 0 is world 1);
  on the 47,674 circuits where every family has <= 1 member per world the 2-SAT is exact: 0 contradictory SCCs, and the
  longest implication path is ONE forced step (e.g. cx44_0: c(0) = 0 => c(1) = 1). Conflicts never chain.
- A 2-step chain needs an output whose candidates in BOTH worlds conflict with others. Stronger candidate lemma tested here
  (freecand.py): FREE CANDIDATE: every output has a merge set disjoint from every merge set of every other output (then
  MergeSDR is immediate). Holds for 80 of 84 outputs, 24 of 26 instances; FAILS on cxT2 and cxT4 (outputs 0 and 2, whose
  world-0 families have 15-189 members): there the SDR needs a coordinated choice. Restricting families to canonical points
  (z = 0 and minimal world-0 points; freecand2.py) is worse: 78/84 outputs, 23/26 instances (v1 also fails).
- So the free-candidate lemma is false in general; the true pattern is scaffold's: conflicts exist but forced implications have
  length <= 1. Suggested lemma shape for a proof: 'if a candidate of w is blocked by a candidate of v, then v has a candidate
  that blocks nothing' (no chains), which is exactly the length-1 implication structure; worth testing on the corpus in this
  form (per blocked pair, does the blocker's output have an unblocking alternative?).
- scaffold corpus result (75,619 circuits, 09:51): FREE CANDIDATE holds in 73,165 circuits (96.75%); the NO-CHAIN lemma
  ('w blocked by v => v has a candidate blocking nothing') is VIOLATED in 2,454 circuits (4,702 ordered pairs), e.g. cxT2. So
  both one-line lemmas fail on the same ~3% (cxT2-type: large world-0 families, coordinated choice needed); MergeSDR itself
  still holds everywhere tested. A proof must handle coordinated choices: Haxell's alternating-tree induction (§4) is the
  matching template; a classification of the cxT2-type circuits (what makes world-0 families large) would say where.
  Referee's L-flip: single-flip repair fails on 24 K4 circuits (fixh16, s = 16), otherwise <= 4 flips suffice.
