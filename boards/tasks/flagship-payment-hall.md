# Task: flagship-payment-hall (payment Hall implies negation-limited Boolean sums)

- **Source:** coord for Addison, 2026-11-25 (card approved as the flagship).
- **Target theorem.** State it in Lean as a Prop first, with no proof claimed. For Boolean sums with pairwise |S_a ∩ S_b| ≤ 1, every circuit with at most k NOT gates needs at least Σ(|S_w| − 1) gates.
  - k = 1 is `no_minCE`, reached through the checked chain `PaymentHall` → `BottomPay` → `LightAbsorb` → `DDAbsorb` → `MixedCount` → `no_minCE`.
  - General k is the several-NOT point lemma.
- **Unifying step:** U1's payment Hall condition (PHC; matroid-partition form, e679ae1). Prove or refute that both BottomPay and the point lemma follow from it.
  - PHC at the common point 0 implies the point lemma. Tested with 0 failures; not proved.
  - The OR-only version is false (5-line counterexample), so the NOT wire h has to appear in the statement.
- **State after F1 (Fable, f53a360). PHC is NOT proved.**
  - Lemma D: PHC ⟺ for every payer set J, Σ_w (c_w(J) − 1) ≤ |E∖J|. Necessity is checked in Lean (`Open/PHC.lean`); sufficiency rests on Rado and matroid union, cited from memory and not formalised.
  - The exact obstacle is the class point lemma for two sets.
  - Gap: BottomPay's per-set rank needs "top exclusion", which is tested only. See OPEN lines on open-one-not.md.
- **Positioning:** a standalone result in negation-limited circuit complexity. It bypasses P vs NP. In any README or external text, state no implication for P vs NP; the worlds-map card holds that context.
- **Claim at full strength, and no further:** if proved, this unifies BottomPay, the point lemma and `no_minCE` under one matroid condition.

## Seats
- F1 (Fable), the proof side: first pass DECIDED (above); the next proof attempt targets the class point lemma for two sets.
- OPEN (Sonnet) LIT1: literature check on negation-limited Boolean sums. Cover Markov 1958; Amano–Maruoka; Morizumi; Jukna, *Boolean Function Complexity* (the negation-limited chapter); Mehlhorn and Pippenger on monotone Boolean sums. Question: is the k-NOT statement known, open or false? This must be answered before any novelty claim. -> research note `one-not/research/open/LIT1_negation_limited.md`, plus LITERATURE.md rows.
- OPEN (Sonnet) REF1: the refuter lane pointed at PHC first, run on git-compute (`.github/workflows/compute.yml`) with the tensor backend: random and targeted payer sets on stored and generated instances, checking Lemma D's inequality. -> `one-not/research/open/REF1_phc.md`
  - Routing: REF1 records findings with `boards.py add ... --runner "<cmd>"` by default (tensor backend, `boards.py retest`); SAT cells keep SAT.

## Lines (TAKEN / DECIDED only)
- TAKEN LIT1 (Sonnet): literature check on negation-limited Boolean sums (known / open / false).
- TAKEN REF1 (Sonnet): refute PHC (Lemma D inequality) on BottomPay DD states, random one-NOT circuits on linear set systems, and two-set point programs, via git-compute. -> one-not/research/open/REF1_phc.py, REF1_phc.md
- DECIDED LIT1 (Sonnet) (was TAKEN): verdict OPEN. No source proves any k-NOT gate bound on (1,1)-disjoint Boolean sums, none contradicts it (Tardos/Razborov/merging savings need many NOTs and non-sum functions); k = 0 is Wegener/Mehlhorn/Pippenger; Jukna-Sergeev §7 asks it. Unchecked: Jukna errata 7.4/7.7 statements, Mehlhorn full text; Blum TR24-179 "open" claim unverified (abstract silent). Novelty not asserted. -> `one-not/research/open/LIT1_negation_limited.md`
- TAKEN LIT2 (Sonnet): Jukna errata 7.4/7.7, Jukna-Sergeev §7 exact quote, Mehlhorn 1979 / Guo et al. / Jukna ch. 10 reads. -> LIT1_negation_limited.md LIT2 section
