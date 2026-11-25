# Task: qg-frontier (the research frontier of quantum gravity, and the next formal targets)

- **Source:** Addison, 2026-11-25: "also a research agent pushing frontier of quant grav would be extremely good."
- **Already in the repository:** `lean/PEqualNP/QuantumGravity/`. L115 (Haar small ball), L116, L169 (P_CTC ⊆ EXP) and the 16k form of L119 are proved. The exact 9k+3n+1 form of L119 waits on the KAK decomposition.
- **Seat:** Q1 (Opus), DECIDED below: survey the frontier with honest read status, and add it to LITERATURE.md.
  - Topics: complexity = volume and complexity = action, the Brown–Susskind second law of complexity and linear growth, holographic quantum error-correcting codes, CTCs and computation, and the counting lower bounds for unitary complexity (Haferkamp et al. 2022, linear growth for random circuits).
  - Then rank three to five next formal targets by value and by how far current Mathlib can reach them. Each becomes a precise `OPEN (Sonnet)` line on this board.
  - Note: the repository's L115 and L119 are the counting core of the "most unitaries need exponential complexity" argument, so linear growth of complexity is a natural next target.

## Next formal targets (ranked by Q1; why in `lean/PEqualNP/QuantumGravity/FRONTIER.md`)

All names below live in `namespace PEqualNP.QuantumGravity.Open.<File>` with `open PEqualNP.QuantumGravity MeasureTheory`. Targets 1a to 1c are one chain (Knill's theorem for the continuous two-qubit gate set).

## OPEN / TAKEN


- TAKEN S7 (Sonnet): [O3 sub-lemma, clock] in `Open/PspaceCtc.lean` terms: `theorem stepEncoding_of_timed {L : Language Bool} (p q : Polynomial ℕ) (initL : List Bool → List Bool) (stepL : List Bool × List Bool → List Bool) (haltL outL : List Bool × List Bool → Bool) (hi : CPTb initL) (hs : ComputableInPolyTime encodePair (fun y : List Bool => y) stepL) (hh : ComputableInPolyTime encodePair Computability.encodeBool haltL) (ho : ComputableInPolyTime encodePair Computability.encodeBool outL) (htime : ∀ x, ∃ t < 2 ^ q.eval x.length, haltL (x, ((ctcRegisterMap stepL x (p.eval x.length))^[t] (startV initL x _)).toList) = true) (hcorr : ∀ x t, <first halt from startV at t> → (outL (x, …) = true ↔ x ∈ L)) : StepEncoding L` (prepend a q-bit counter, tick with `bitsSucc`, halt also on all-ones; gives the "every register halts" half of `EncodingSound`) -> lean/PEqualNP/QuantumGravity/Open/PspaceClock.lean
- TAKEN S8: [O3 sub-lemma, machine] every `L ∈ Library.PSPACE` (`Evasion/SpaceDraft.lean`, `Turing.FinTM2` with `UsesSpace`) has `p q initL stepL haltL outL` meeting the hypotheses of `stepEncoding_of_timed`: bit encoding of `FinTM2` configurations with stacks of length ≤ n^k + k padded to p(n) bits, one `FinTM2.step` polynomial-time on that encoding, halting test and answer read-out, and halting within 2^q steps (pigeonhole: at most 2^p distinct configurations on the start orbit). With the clock lemma this proves `PspaceStepEncodingLemma`, hence `PSPACE ⊆ PCTC` -> lean/PEqualNP/QuantumGravity/Open/PspaceTM2.lean

## Refuted / dead

- None recorded. The 9k+3n+1 form of L119 (KAK for U(4)) is a Mathlib gap, not a dead end; see `open-qg`.

## Decided (one line each; the file holds the proved statement)

- Q1 (Opus): survey in LITERATURE.md §I ("Frontier survey", 14 rows with read status; Haferkamp et al. 2022 main text TXT, appendices not read); four ranked targets (1: Knill count for continuous two-qubit gates, 2: CTC reset cycle, 3: two-level saturation, 4: L119 at 15k+1). Nothing formalised by Q1. -> `lean/PEqualNP/QuantumGravity/FRONTIER.md`
- Q2 rank 1a: `opNorm_gateMat_le`, operator norm of a gate matrix ≤ sum of entry norms (standard axioms only). -> `Open/GateNet.lean`
- Q2 rank 1b: `twoQubitGates_net`, entry-grid net of the two-qubit gates, card ≤ (n+1)^2 (C/δ)^32. -> `Open/GateNet.lean`
- Q2 rank 1c: `approx_count_twoQubit`, μ(ApproxReachableIn (twoQubitGates n) k ε) ≤ ((n+1)^2 (C(k+1)/ε)^32 + 1)^k (cε)^(4^n) (net from 1b, L-qg-113 with m = 1, then L116 via `Open.L115.haar_small_ball` + L117). -> `Open/ApproxCount.lean`
- Q3 rank 2: `reset_support_on_start_cycle`, the reset-to-start trick behind PSPACE ⊆ P_CTC (uses `Helpers.mem_range_iterate_of_consistent`). The PSPACE encoding itself is not done. -> `Open/CtcReset.lean`
- Q4 [DECIDED]: [rank 4] PROVED, no sorry, axioms propext/choice/Quot.sound: `theorem L119_fifteen (n k : ℕ) (μ : Measure (qubitUnitaryGroup n)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (hlt : 15 * k + 1 < 4 ^ n) : μ (ReachableIn (twoQubitGates n) k) = 0` (one global phase instead of one per gate; via `haar_null_of_cover` and a 15-parameter differentiable cover of the 4×4 unitaries up to phase; if the cover is the blocker, write that lemma down instead) -> lean/PEqualNP/QuantumGravity/Open/KnillParam15.lean (cover lemma `exists_trace_chart`: every unitary is a phase times a Cayley chart of a trace-zero skew matrix, by spectral theorem plus an intermediate-value step on a sum of cotangents)
- O3 (Opus): PSPACE ⊆ PCTC up to one named lemma. Proved (propext, choice, Quot.sound): `answer_eventually_const` (reset map with an answer bit: after a fixed T steps the bit is the first-halt answer from every point), `PCTC_of_stepEncoding` (the Aaronson–Watrous reset circuit is polynomial-time on the repo's exact PCTC: cut-or-pad register, `encodePair`, `encodeBool`), `PSPACE_subset_PCTC_of_stepEncoding`. Open: `PspaceStepEncodingLemma` (split into the two OPEN lines above). P_CTC = PSPACE would also need PCTC ⊆ PSPACE (only ⊆ EXP is proved). -> `Open/PspaceCtc.lean`
- S4 [DECIDED]: [rank 3] PROVED, no sorry, axioms propext/choice/Quot.sound: `def twoLevel (ι : Type) [Fintype ι] [DecidableEq ι] : Set (Matrix.unitaryGroup ι ℂ) := {U | ∃ a b : ι, ∀ x y : ι, (x ≠ a ∧ x ≠ b) ∨ (y ≠ a ∧ y ≠ b) → (U : Matrix ι ι ℂ) x y = (1 : Matrix ι ι ℂ) x y}` and `theorem reachable_twoLevel (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) : U ∈ ReachableIn (twoLevel (Fin d)) (d * (d + 1) / 2)` (Givens / Reck column elimination by induction on a Finset support; Givens rotation, phase gate, inverse closure) -> lean/PEqualNP/QuantumGravity/Open/TwoLevel.lean
