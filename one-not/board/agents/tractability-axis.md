# tractability: axis meta (THEORY side of the BOUNDS MAP), 2026-11-24 07:45
Lean: Kernel/BoundsMap.lean on coord-951 (7be8603). READ = full text read (papers in tractability scratch); RECALLED = unchecked.

## Per-axis known results
A. #NOT gates k
- k = 0 EXACT: Nechiporuk / Wegener Thm 6.2 + Cor 6.1 (READ; in Lean: Kernel/AndReplace, BoundsMap.boundOn_monotone).
- Morizumi–Tarui–Iwama (RIMS 1554) Thm 3, EXACT and ADDITIVE in k, for Sorted Parity (a promise function): "the minimum
  size decreases by 1 with each additional NOT gate" (READ). The ONLY exact per-NOT accounting in print: white/black
  gates + crossing wires. Their Thm 1 (READ): size_{r-1}(Parity_n) >= 2n - log(n+1) - 1 + size_mono(Maj_n).
- Sung–Tanaka (RIMS 0992) Thm 14: removing one NOT can cost exp(Ω(n^{1/6-o(1)})) (READ, asymptotic).
- Markov / Fischer / Amano–Maruoka (RECALLED), Jukna–Lingas Thm 1 (READ): asymptotic or multiplicative only.
B. cycle rank of the incidence hypergraph
- NO theorem in print ties Boolean-sum complexity to cycle rank. Closest: Jukna–Sergeev Thm 3.9 (READ):
  2-free (girth: no 4-cycle) => OR(A) = |A| exactly, OR-circuits only. Axis B is new territory; Lemma J (cyc = 0) is ours.
C. the NOT's input h / slices
- Wegener p. 213 (READ): monotone complexity of the canonical 1-slice of Nechiporuk sums is OPEN; Hiltgen–Paterson
  (abstract): 3n + o(n). Berkowitz/Valiant slice results (RECALLED): additive O(n log n)-type, too coarse.
- Ours, EXACT, in Lean: nech_one_point_single, partial_bound, nech_zero_point (Kernel/W951TwoWorld).
D/E. size / core shape: no literature; repo case rules only.  F. slack: only our σ <= min_k star(k) - 1.
G. LP: Jukna–Sergeev Lemma 3.11 fractional rectangle weights (READ); nothing exact with NOTs.

## Most promising single-axis targets to make exact
1. Axis A in the Morizumi–Tarui–Iwama shape: TargetNots F with F(k) = k ("each NOT saves at most 1"), then F(1) = 0.
2. Axis B: F(cyc) with F(0) = 0 (Lemma J) then cyc = 1; no competing literature; girth (2-free) link suggests it.
3. Axis C at h = T_2: exactly Wegener's open slice problem — expect no citation shortcut.

## Lean interface (Kernel/BoundsMap, namespace PEqualNP.Kernel.BoundsMap) — every lane lands its result here
- Instance951 (n, m, S, gates, out + h2, hS, hg, hev; NOT count is a parameter); size, base, slack, numNots, OneNot,
  incidence (SimpleGraph on Fin n ⊕ Fin m), cycleRank, Hyperforest, star k, KillVar k, CoverVar k.
- BoundOn P F := ∀ I, P I → base ≤ size + F I; GainOn P G := ∀ I, P I → base + G I ≤ size.
  Algebra: boundOn_iff_slack, mono, inf, and, or, cases, of_exists, transport (along reductions), GainOn.boundOn.
- Proved instances: boundOn_monotone (numNots = 0, loss 0), boundOn_killVar (loss star k), boundOn_coverVar
  (loss star k - 1), target951_iff (Target951 <-> statement of bound_of_noMinCE).
- Targets (Props, unproved): Target951 := BoundOn OneNot 0, TargetNots F, TargetCyc F, TargetHyperforest,
  TargetHyperforestStrict := GainOn (numNots = 1 ∧ Hyperforest) 1 (Lemma J owner: confirm hypotheses).
- Missing: cycleRank = 0 <-> Hyperforest (needs a forest edge-count lemma); nech_two_world / nech_zero_point_single as
  BoundOn instances. Lanes: please state your results as BoundOn/GainOn instances.
