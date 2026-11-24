# pnp-general (by addison-jpg)

The higher level gist is: quantum/gravity relativity maps onto the relativity barrier to P/NP, and can help bypass it.

## Abstract

This repository is a machine-checked study of lower bounds for Boolean circuits built from AND, OR and NOT gates, organised around the number of NOT gates a circuit may use. Its central object is a family of functions for which the monotone case is classical: for a system of sets that pairwise share at most one point, computing the OR of every set requires exactly Σ(|S| − 1) gates when no NOT gate is allowed (Nechiporuk; Mehlhorn; Wegener). We ask whether a single NOT gate can reduce that count, an open question on which no result has been published. We prove that it cannot in three cases, reduce the general case to one explicit inequality, refute a series of natural proof strategies by explicit circuits, and place the question on a ladder that ends, after logarithmically many NOT gates, at unrestricted circuits. Alongside this we formalise the finite, classical cores of several arguments from quantum gravity that concern computational complexity. All theorems are verified in Lean 4 against a pinned version of Mathlib. Nothing here settles, or claims to approach, the P versus NP problem.

## 1. Background and motivation

A superpolynomial lower bound on the circuit size of an NP-complete problem would separate P from NP; the best bounds known for explicit functions over unrestricted circuits are linear. Three barriers explain why known techniques fall short: relativization, algebrization and natural proofs. For monotone circuits the situation is very different, and exact bounds are available. A theorem of Markov, made efficient by Fischer, shows that ⌈log₂(n+1)⌉ NOT gates suffice to simulate any circuit with polynomial overhead. The number of NOT gates therefore interpolates between a regime where exact bounds can be proved and the regime where almost nothing is known. This project studies the first step of that interpolation.

The second motivation is the thesis stated in the first line. Arguments in quantum gravity about the complexity of black-hole decoding, holographic dictionaries and closed timelike curves each fix a model of computation, and a proof technique that is indifferent to the model cannot separate P from NP. We treat this correspondence as a premise that organises which statements are worth formalising. It is not used as a step in any proof.

## 2. Results

**The one-NOT theorem: first results on an open question.** Let S_1, …, S_m be sets of size at least 2 that pairwise share at most one point, and let C be a circuit of fan-in-2 AND and OR gates with at most one NOT gate that computes the OR of each set. The conjecture is that C has at least Σ(|S_w| − 1) gates. This is proved when the NOT gate reads an input variable, when every set has at most three points, and whenever a certain pairwise test on the circuit obtained by replacing the NOT gate with a fresh input succeeds. The general case is reduced to a single statement: a minimal counterexample does not exist. That statement is further shown to be equivalent to one inequality, the non-negativity of a quantity we call the slack at the empty restriction.

**Structure of a minimal counterexample.** Such a circuit has no constant gate, no two gates computing the same function, no gate computing an input, no unread gate, an essential NOT gate, and admits no rewiring of a gate input that would leave a gate unread.

**The ladder.** The simulation of arbitrary circuits by circuits with logarithmically many NOT gates is formalised, so that a superpolynomial bound at that rung would be a bound for all circuits. A size hierarchy theorem and several exact small-case bounds are also formalised.

**Classical cores of quantum-gravity arguments.** Forty-seven statements are verified, among them: if P = NP then every polynomial-time length-preserving function can be inverted in polynomial time; NP and coNP are contained in the class decided with a closed timelike curve under Deutsch's consistency condition; counting bounds for words in a gate set; and the basic properties of the five-qubit code and the six-qubit perfect state.

## 3. Negative results

A recurring pattern in this work is that a strategy holds on every randomly generated circuit and fails on a constructed one. Each of the following was believed, tested at scale, and then refuted by an explicit circuit kept in the repository: induction by fixing one input at a time, to 0 or to 1; its generalisation to any bounded number of inputs; averaging over orders of the inputs; counting arguments over merge sets without a minimality hypothesis; and, for circuits with four or more NOT gates, the counting family used in the one-NOT case. The counting inequality itself has not failed on any circuit examined, roughly 85,000 in total. We regard the list of refuted strategies, with its counterexamples, as one of the durable outputs of the project.

## 4. Method

Every theorem is checked by the Lean 4 kernel. A verification file walks all theorems of the one-NOT development and fails unless each rests only on the three standard axioms; at the time of writing it covers 4,851 theorems, of which 22 are explicitly allowed to depend on the one open statement or belong to an unused draft.

Exploration is carried out in **asteroid**, a small domain-specific language written for this project. An asteroid program defines or loads circuits and states claims about them. Claims are evaluated numerically at once, and those marked for proof are translated and submitted to the proof checker. For claims of circuit correctness and for the counting inequality, a proved translation theorem guarantees that what is checked is a statement about the project's own definitions. asteroid is an instrument for finite questions about individual circuits. It cannot state or prove a general theorem, and its interpreter is not itself verified.

```
circuit hello 4
  a = or 0 1
  b = or a 2
  c = or 2 3
  set 0 1 2 -> b
  set 2 3 -> c
end
claim correct(hello) by lean
claim forall cubes slack(hello) >= 0 by lean
```

## 5. Open problems

1. The existence of a minimal counterexample to the one-NOT theorem. One local statement, a step that may fix an input to either value, is consistent with all data and would suffice.
2. Whether two, or any fixed number of, NOT gates can reduce the gate count for these functions. A positive lower bound for all circuits on dense set systems would be superlinear, which is beyond current knowledge for any explicit function; this question should be expected to be hard and may have a negative answer.
3. Whether the correspondence with physical models of computation can be made to yield a proof technique, as opposed to a classification of techniques that cannot work.
4. Four formal statements on the quantum-gravity side remain unproved, including the containment in exponential time of the class decided with a closed timelike curve.

## 6. Reproducing the results

```bash
pip install -e .
asteroid hello.ast
asteroid test
```

With Lean installed, claims marked for proof are checked; without it, asteroid reports that they were only evaluated. To verify every theorem of the one-NOT development with Lean alone:

```bash
cd one-not/lean && lake exe cache get && lake build PEqualNP.Verify.All
```

The larger Lean project under `lean/` (the general-circuit and quantum-gravity statements and the inherited library) builds row by row, for example `cd lean && lake build PEqualNP.General.L001`; a full verification pass over it has not yet been run.

## 7. Guide to the repository

| Path | Contents |
|---|---|
| [`one-not/`](one-not/README.md) | the one-NOT development: Lean proofs, counterexample circuits, search and test programs |
| `lean/` | general circuits, the quantum-gravity statements, the barrier theorems, the inherited library |
| [`asteroid/`](asteroid/README.md) | the language: manual, [grammar](asteroid/SPEC.md), example programs, and the results expressed as programs |
| [`LITERATURE.md`](LITERATURE.md) | sources consulted, with an indication of how closely each was read |
| [`SYNTHESIS.md`](SYNTHESIS.md), [`notes/`](notes/) | longer expositions, including a statement-by-statement account ([`notes/front-page-2026-11-24.md`](notes/front-page-2026-11-24.md)) |
| [`NAMES.md`](NAMES.md), [`BOARD.md`](BOARD.md), [`boards/`](boards/) | terminology; working records |

The one-NOT question for these functions is open. It is posed, in more general form, by Jukna and Sergeev (2013) and by Blum (2024), and no result on it has been published. The theorems of Section 2 are the first. This repository is public for reading and is not a work queue for automated agents ([`AGENTS.md`](AGENTS.md)).

## License
MIT; see [`LICENSE.md`](LICENSE.md). Exception: files taken or derived from [`brilliant-hq/pequalnp-proofs`](https://github.com/brilliant-hq/pequalnp-proofs) remain under the Apache License 2.0; see [`LICENSE-APACHE`](LICENSE-APACHE). These are the upstream Lean library under `lean/PEqualNP/` (`CircuitLowerBounds`, `Defs`, `Gct`, `Library`, `MetaComplexity`, `Outside`, `ProofComplexity`, `Search`), the copy of `Defs` in `one-not/lean/PEqualNP/Defs/`, upstream files modified here (e.g. `lean/PEqualNP.lean`, `lean/PEqualNP/Defs.lean`, `lean/CheckLemma.lean`, `one-not/lean/PEqualNP.lean`, `one-not/lean/PEqualNP/Defs.lean`), `tools/build.sh`, `one-not/tools/build.sh` and `notes/note-1-edge-function-exact-size.md` (with its copy in `one-not/notes/`). New work in this repository is by addison-jpg and contributors.
