# Direct asks, answered

Rendered by the Python `asteroid` from `asks.ath` (`bin/asteroid --no-lean workshop/asks/asks.ath`). Each answer keeps the label asteroid gives it. The base `ast` binary cannot answer asks yet: it replies "not in the Lean version yet" to each one, so this page does not use it.

```
2: ask "status" (a question, not a claim)
   [checked] 100 findings recorded as checked, 91 verified
   [checked-finite] 58 findings recorded as checked-finite, 32 verified
   [open] 35 findings recorded as open, 0 verified
   [open] 5 findings recorded as paper, 0 verified
   [refuted] 13 findings recorded as refuted, 6 verified
   [tested] 51 findings recorded as tested, 12 verified
   [checked-finite] 94 frames labelled checked-finite (94 TRUE, 0 OPEN)
   [open] 67 frames labelled open (4 TRUE, 63 OPEN)
   [tested] 3 frames labelled tested (3 TRUE, 0 OPEN)
   [checked] 91 RESULTS.md rows labelled checked
   [checked-finite] 32 RESULTS.md rows labelled checked-finite
   [refuted] 6 RESULTS.md rows labelled refuted
   [tested] 12 RESULTS.md rows labelled tested
   [open] center nodes besides findings and frames: 109 cell, 49 fingerprint, 8 level
   [open] 12 modules in core/ontology read by their docstring (each line of theirs carries its own label)
   [proposed] 86 culture rows and 94 formal rows carry structure tags; status: proposed tags, unreviewed
3: ask "how many results are verified" (a question, not a claim)
   [checked] 91 verified findings recorded as checked
   [checked-finite] 32 verified findings recorded as checked-finite
   [tested] 12 verified findings recorded as tested
   [refuted] 6 verified findings recorded as refuted
   [open] 141 of 262 results are verified in all (verified = no why_not, and a word RESULTS.md lists); 121 are not verified: checked with why_not 9, checked-finite with why_not 26, open 35, paper 5, refuted 7, tested 39
4: ask "show open frames" (a question, not a claim)
   [open] 63 open frames (highest score first)
   [open] frame OPEN: A non-violent alternative: lateral links, mutual aid and community -> ANALOGY (a reading) of the same graph fact: build links between people until no centre is ... (claim none, score 0.0225; as recorded in frames.jsonl)
   [open] frame OPEN: Against the manifesto's strategy: attacking a hub while the base has n... -> ANALOGY (a reading) of the graph fact above: when people depend on the system and not on e... (claim none, score 0.0225; as recorded in frames.jsonl)
   [open] frame OPEN: Butler, Gender Trouble (1990; cited from memory): sex is constructed a... -> ANALOGY (a reading): the love model's two sides are a binary built into the mathematics; d... (claim none, score 0.0225; as recorded in frames.jsonl)
   [open] frame OPEN: Crenshaw 1989, Demarginalizing the Intersection of Race and Sex, Unive... -> ANALOGY (a reading): law and data that look only at margins (women, Black workers) miss th... (claim none, score 0.0225; as recorded in frames.jsonl)
   [open] frame OPEN: Critique of primitivism: romanticising primitive peoples is a racist m... -> ANALOGY (a reading): the noble savage and the savage are one gaze, the 2-chain again; it b... (claim none, score 0.0225; as recorded in frames.jsonl)
   [open] frame OPEN: Du Bois 1903, The Souls of Black Folk: double consciousness, looking a... -> ANALOGY (a reading): a one-way gaze is the 2-chain above; double consciousness is living o... (claim none, score 0.0225; as recorded in frames.jsonl)
   [open] frame OPEN: Kaczynski, Industrial Society and Its Future, published 1995; bombings... -> the violence is condemned without qualification; the numbers are from memory and not check... (claim none, score 0.0225; as recorded in frames.jsonl)
   [open] frame OPEN: Anais Nin: racist and exoticizing portrayals of people of colour in he... -> a case of the primitivist move: other peoples cast as closer to nature and the body. A rea... (claim none, score 0.015; as recorded in frames.jsonl)
   [open] frame OPEN: Candidate: Heider balance in culture/social -> culture/social has no balance script yet; the quadrants count balanced labellings 4, 36, 8... (claim none, score 0.015; as recorded in frames.jsonl)
   [open] frame OPEN: Candidate: preference profiles of culture/love (n + n people, each ran... -> ANALOGY (a reading): one side of a love profile reads as n voters ranking n options. Only ... (claim none, score 0.015; as recorded in frames.jsonl)
   [open] frame OPEN: Candidate: troll quadrants (culture/homestuck/quadrants/check.py) and ... -> the code link exists: culture/love/check.py imports the quadrant balance test. A record ne... (claim none, score 0.015; as recorded in frames.jsonl)
   [open] frame OPEN: Crenshaw 1989 (cited from memory) and culture/race: intersectionality ... -> ANALOGY (a reading): a joint table is not fixed by its margins (culture/race/race.py); sev... (claim none, score 0.015; as recorded in frames.jsonl)
   [open] ... and 51 more not shown (narrow the query)
5: ask "what is open about circuit" (a question, not a claim)
   [open] about circuit: 0 open frames, 39 unverified findings, 6 open center nodes, 0 open modules, 0 tag rows labelled open
   [tested] finding asteroid/cc05bfb4: 34 circuits converted to .bench (all witness circuits and 3 beyond_one_not circuits; fano_sat66.json is a list of 66 circuits, not converted); the Pyt... (not verified: needs a second seat in by; second seat: none; board)
   [tested] finding asteroid/ff1f357b: The Lean kernel rejects a false claim that is forced past Python (claim! witness(c) = 6 on a circuit with 5): the build fails with a kernel type misma... (not verified: needs a second seat in by; second seat: none; board)
   [open] finding culture/homestuck/8a00ca4e: alchemy.ath: the b = 3 alchemy circuit computes all seven nonempty unions on all 8 inputs, with 4 gates against a base of 5 (sharing, possible because... (recorded as checked-finite, not verified: checked-finite needs a runner (the exhaustive check, re-runnable); second seat: frame-review; board)
   [tested] finding math/worlds/63b81527: On the 21 stored circuits (PHC at point 0, Lemma D potential, all 621,808 payer subsets): split condition holds 21/21; unit truncation submodular, 0 v... (not verified: needs a second seat in by; second seat: none; board)
   [tested] finding one-not/data/beyond_one_not/2b499863: hunt.py 'Theorem: gates >= base' with at most 2, 3, 99 NOT gates, 45 s each, seed 11: 739,410 / 767,717 / 747,308 mutations, 0 circuits below base (hi... (not verified: needs a second seat in by; second seat: none; board)
   [open] finding one-not/data/beyond_one_not/368f7db9: S3 (rank 1) FlipClasses.count t: a correct circuit with at most t NOT gates has at least base flip classes; by the per-set lemma this is a statement a... (not verified: needs a second seat in by; second seat: none; board)
   [tested] finding one-not/data/beyond_one_not/6e5d40f1: Flip classes: the per-set lemma (at every zero point of every set at least |S|-1 flip classes; paper proof for every number of NOT gates in workshop/n... (not verified: needs a second seat in by; second seat: none; board)
   [tested] finding one-not/data/beyond_one_not/6f160d5e: World bound (#AND/OR gates >= largest base(Q,R) of a subcube with constant NOT outputs; paper proof from rung 0 for every t) holds on 19 of 19 corpus ... (not verified: needs a second seat in by; second seat: none; board)
   [open] finding one-not/data/beyond_one_not/88093cdf: S4 (rank 5) BoolSumNotLog: rung ceil(log2(n+1)) on projective planes would give (base - n - 2)/2 gates for ALL circuits (above 3.1 n from q = 8); not ... (not verified: needs a second seat in by; second seat: none; board)
   [tested] finding one-not/data/beyond_one_not/ab33680e: Exhaustive, ANY number of NOT gates: no correct circuit with at most base-1 gates on two triples (base 4), triangle of triples (6), two 4-sets (6), st... (not verified: needs a second seat in by; second seat: none; board)
   [tested] finding one-not/data/c4g/017aa1fd: No correct circuit with at most 4 NOT gates has fewer than base gates on K4-triples (n = 7, base 12): s = 11, t <= 4 is UNSAT (2,314 s, --sb). (not verified: needs a second seat in by; second seat: none; board)
   [tested] finding one-not/data/c4g/4b9ae585: No correct circuit with at most 2 NOT gates has fewer than base gates on K4-triples (n = 7, 6 triples, base 12; UNSAT at s = 11, 1,933 s) or on the Fa... (not verified: needs a second seat in by; second seat: none; board)
   [open] ... and 27 more not shown (narrow the query)
   [open] center cell circuits/32b46e20: A14 (container restart; partial A14_bottom_hall.py kept; reopen to continue): BOTTOM PAY (A10 §3, matroid form): at every mixed st... (cell STOPPED on board open-one-not line 20)
   [open] center cell circuits/4c460377: A13 (container restart; partial A10_bottom_hill.py kept; reopen to continue) (Sonnet): hill-climb for a BOTTOM PAY failure: mutate... (cell STOPPED on board open-one-not line 19)
   [open] center cell circuits/5b79c9c7: (Sonnet): top exclusion (F1 s5), paper proof or counterexample search: at a mixed state (Q, D) of a correct one-NOT circuit, for a... (cell OPEN on board open-one-not line 23)
   [open] center cell circuits/6d7bba97: S6 (Addison made S8 the priority; reopen later) (Sonnet): extend A14_bottom_hall.py to random and targeted DD states on larger cir... (cell STOPPED on board refuter-951 line 20)
   [open] center cell circuits/7d3a3be9: (Sonnet): BottomPay deletion form by size of the deleted set (F1 s2): for a correct one-NOT circuit at a DD state and every set R ... (cell OPEN on board open-one-not line 25)
   [open] center cell lateral/29dafa60: (Fable under the revised seat rule; low priority, idle compute): the asteroid Tarski instance. Gödel-number asteroid claims (Stmt)... (cell OPEN on board lateral-diagonal line 20)
6: ask "what is verified about circuit" (a question, not a claim)
   [open] 29 verified findings and 28 RESULTS.md rows mention circuit (frames and tags are not counted as verified)
   [checked] finding asteroid/31d6a07d: asteroid Semantics: eval_sound — a covered claim (correct, hyps, forall cubes slack >= 0, comparisons of gates/base/orwitness/slack with numbers, and ... (verified; second seat: none (a Lean check needs none); board)
   [checked] finding asteroid/3b46038e: asteroid Semantics: correct_bridge, slackNonnegAll_bridge, hypsB_bridge — the executable's light checkers on a circuit equal the project's checkers on... (verified; second seat: none (a Lean check needs none); board)
   [tested] finding asteroid/7d2be507: Python mixed slack from continuous.slack_table agrees with an independent naive implementation at all 81 + 243 states of two circuits (n = 4, 5; witne... (verified; second seat: seat A; board)
   [checked] finding asteroid/8d76417d: The kernel decides MixedStep (a paying 0-step or 1-step with mslack no larger at every state with positive base) and mslack >= 0 at all 3^5 = 243 mixe... (verified; second seat: none (a Lean check needs none); board)
   [tested] finding asteroid/fb772b9e: Native binary, interactive prompt (asteroid / asteroid repl): 4ST> prompt, :help :load :save :quit, circuit blocks; verdicts equal python3 -m asteroid... (verified; second seat: R1; board)
   [checked] finding asteroid/programs/37dcef35: The continuous form is in asteroid: for the Fano formula and a 5-input one-NOT circuit the kernel checks every cube and Lean states 0 <= Phi(p) for al... (verified; second seat: none (a Lean check needs none); board)
   [checked] finding asteroid/programs/4a95d48e: theorem.ath: 15 witness circuits (n<=9) correct and count slack>=0 by the kernel, gates>=base on all 15; a one-NOT script circuit and the Fano formula... (verified; second seat: none (a Lean check needs none); board)
   [checked] finding asteroid/programs/a023c28e: ladder.ath: rung 0 (2 circuits without NOT) count>=0 and gates>=base in the kernel; the 4 many-NOT files all have witness<base and gates>=base; 10 Pyt... (verified; second seat: none (a Lean check needs none); board)
   [checked] finding lean/PEqualNP/QuantumGravity/Open/8008158e: PSPACE in P_CTC up to one named lemma: any language with a polynomial-time step encoding (init, step, halt test, answer; every register halts; first h... (verified; second seat: none (a Lean check needs none); board)
   [tested] finding one-not/data/c4g/04a575bf: With exactly 2 NOT gates, neither feeding the other, the minimum circuit size is base + 3 on tri3, star3 and tri4 (UNSAT at base + 1, base + 2) and ab... (verified; second seat: coord (rerun tri3 --exact-not --no-nn: UNSAT at s=7, 8; SAT ...; board)
   [tested] finding one-not/data/c4g/1b00e1bc: No correct circuit of fan-in-2 AND/OR gates and at most 2 NOT gates has fewer than base gates on: triangle of triples (base 6), Pasch (8), star of 3 t... (verified; second seat: coord (rerun c4t_sat.py: tri3, star3, pasch, tri4, q4, fano5...; board)
   [tested] finding one-not/data/c4g/255631be: SAT with the witness count as a constraint (--wbelow: at most base - 1 gates satisfy D9) finds no correct circuit with at most 2 NOT gates and witness... (verified; second seat: coord (rerun: star44 s=10 t<=4 --wbelow SAT witness 5 < 6 co...; board)
   [open] ... and 17 more not shown (narrow the query)
   [checked] RESULTS.md asteroid: The continuous form is in asteroid: for the Fano formula and a 5-input one-NOT circuit the kernel checks every cube and Lean states 0 <= Phi(p) for al... (line 34; listed as verified)
   [checked] RESULTS.md asteroid: The kernel decides MixedStep (a paying 0-step or 1-step with mslack no larger at every state with positive base) and mslack >= 0 at all 3^5 = 243 mixe... (line 35; listed as verified)
   [checked] RESULTS.md asteroid: asteroid Semantics: correct_bridge, slackNonnegAll_bridge, hypsB_bridge — the executable's light checkers on a circuit equal the project's checkers on... (line 36; listed as verified)
   [checked] RESULTS.md asteroid: asteroid Semantics: eval_sound — a covered claim (correct, hyps, forall cubes slack >= 0, comparisons of gates/base/orwitness/slack with numbers, and ... (line 37; listed as verified)
   [checked] RESULTS.md asteroid: ladder.ath: rung 0 (2 circuits without NOT) count>=0 and gates>=base in the kernel; the 4 many-NOT files all have witness<base and gates>=base; 10 Pyt... (line 38; listed as verified)
   [checked] RESULTS.md asteroid: theorem.ath: 15 witness circuits (n<=9) correct and count slack>=0 by the kernel, gates>=base on all 15; a one-NOT script circuit and the Fano formula... (line 40; listed as verified)
   [tested] RESULTS.md asteroid: Native binary, interactive prompt (asteroid / asteroid repl): 4ST> prompt, :help :load :save :quit, circuit blocks; verdicts equal python3 -m asteroid... (line 41; listed as verified)
   [tested] RESULTS.md asteroid: Python mixed slack from continuous.slack_table agrees with an independent naive implementation at all 81 + 243 states of two circuits (n = 4, 5; witne... (line 43; listed as verified)
   [refuted] RESULTS.md circuits: Level means of slack are NOT nonincreasing on the twin trees: the mean slack over one-point cubes exceeds slack of the empty cube by 2.29 (so 'monoton... (line 65; listed as verified)
   [refuted] RESULTS.md circuits: Level means of the slack nonincreasing (m_0 ≥ m_1 ≥ …, hence Phi' ≤ 0) is FALSE on 8 of 23 witness circuits: m_0 = 6 < m_1 = 8.29 on the six twin tree... (line 66; listed as verified)
   [refuted] RESULTS.md circuits: The one-point step for real-witness gates fails for a correct one-NOT circuit (twin trees, n = 14). (line 67; listed as verified)
   [checked] RESULTS.md circuits: A circuit literal passing correctB and hypsB with fewer gates than the base is a counterexample (IsCE), yields a minimal counterexample, and refutes t... (line 70; listed as verified)
   [open] ... and 16 more not shown (narrow the query)
7: ask "list tags" (a question, not a claim)
   [proposed] 28 tags (unreviewed); 3 of them are new tags proposed and not adopted
   [proposed] absorbing-class: 2 culture rows, 2 formal rows
   [proposed] asymmetric-relation: 7 culture rows, 7 formal rows
   [proposed] branching-tree: 16 culture rows, 12 formal rows
   [proposed] bridge: 2 culture rows, 6 formal rows
   [proposed] counting-sequence: 1 culture rows, 28 formal rows
   [proposed] critical-part: 3 culture rows, 11 formal rows
   [proposed] dag-rejoining: 13 culture rows, 4 formal rows
   [proposed] diagonal: 1 culture rows, 0 formal rows (new tag, not adopted)
   [proposed] escape-velocity: 1 culture rows, 1 formal rows
   [proposed] exhaustive-check: 8 culture rows, 42 formal rows
   [proposed] fixed-point: 6 culture rows, 5 formal rows
   [proposed] game: 2 culture rows, 2 formal rows
   [proposed] halting-vs-lifetime: 2 culture rows, 3 formal rows
   [proposed] information-loss: 1 culture rows, 4 formal rows
   [proposed] linking-invariant: 1 culture rows, 5 formal rows
   [proposed] min-cut: 1 culture rows, 0 formal rows (new tag, not adopted)
   [proposed] modal-S4: 5 culture rows, 6 formal rows
   [proposed] modal-S5: 4 culture rows, 2 formal rows
   [proposed] mutual-binding: 7 culture rows, 5 formal rows
   [proposed] ordering-dependence: 2 culture rows, 9 formal rows
   [proposed] random-walk: 3 culture rows, 5 formal rows
   [proposed] salience-shift: 1 culture rows, 3 formal rows
   [proposed] self-map-vs-other-map: 4 culture rows, 2 formal rows
   [proposed] seriality: 1 culture rows, 0 formal rows (new tag, not adopted)
   [proposed] sphere-index: 1 culture rows, 8 formal rows
   [proposed] symmetric-relation: 6 culture rows, 4 formal rows
   [proposed] transport-map: 2 culture rows, 7 formal rows
   [proposed] two-versions: 3 culture rows, 4 formal rows
8: ask "list pillars" (a question, not a claim)
   [proposed] 5 pillars in the tag tables (unreviewed)
   [proposed] biology: 25 rows
   [proposed] computation: 16 rows
   [proposed] math: 19 rows
   [proposed] philosophy: 19 rows
   [proposed] physics: 15 rows
claims: 0 true, 0 false
```

Regenerate with the command above. Nothing here is a new claim: the answers are asteroid's own counts from the repo.
