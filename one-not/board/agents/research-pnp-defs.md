# research: audit of the project's formal P / NP / P^A / NP^A against public formulations

Status: read (definitions compared line by line; no Lean bridge proved). Requested by the owner.
Project files: pequalnp-proofs lean/PEqualNP/Defs/Base.lean (P, NP, reductions), Defs/Classes.lean (coNP, EXP, NEXP),
Defs/Oracle.lean (OracleTM2, P^A, NP^A). Mathlib pinned fc4f59e5: Mathlib/Computability/TuringMachine/Computable.lean.
Reference formalization: google-deepmind/formal-conjectures @86a2f58 (2026-11-23), FormalConjectures/Millennium/PvsNP.lean
(`P_ne_NP : P ≠ NP := sorry`) + FormalConjecturesForMathlib/Computability/Complexity.lean.
Cook's Clay text (claymath.org/wp-content/uploads/2022/06/pvsnp.pdf) could NOT be fetched (host not allowed); compared
against its standard content (TM, P, polynomial-time checking relation R, witness bound |y| <= |w|^k).

Verdict: faithful. Both the project and DeepMind stand on the same Mathlib model (FinTM2 + TM2ComputableInPolyTime).
- Machine: FinTM2 = finitely many stacks, labels, states; input alphabet finite. Time = number of TM2.step calls, each
  running one finite statement (constant-factor of elementary steps). Multi-stack <-> 1-tape TM is polynomial: P is robust.
  Work-stack alphabets need not be Fintype, but only finitely many symbols can ever appear (pushes are f(σ), σ finite): harmless.
  Halting = haltList: label none, var reset to initialState, all stacks except k₁ empty: harmless cleanup.
- P: L ⊆ {0,1}*, decided by f : List Bool → Bool, input encoded as itself, answer [f x], time p(|x|). = Cook's P over Σ={0,1};
  Cook allows any finite Σ, equivalent for the P = NP question via binary encoding.
- NP: polytime-decidable R on pairs (encodePair over Bool ⊕ Bool, length |x|+|w|), witness |w| <= p(|x|). = Arora-Barak Def 2.1
  and Cook's checking relations (p(n) vs n^k: same class; differences only at finitely many lengths).
- DeepMind differences (not errors): languages as List Bool → Bool; List Bool encoded as delimited blocks (each bit b -> true,b,false,
  length 3|x|) and pairs as delimit(x) ++ enc(w). So the two P's are equal as classes but NOT definitionally: a Lean bridge
  needs a polytime transcoder on TM2. Even P ⊆ NP is sorry there (proof only external: AItoBit/p-subset-np).
- Oracle.lean: one-step queries at label ask, query stack read bottom-to-top via queryBit, stack emptied, label yes/no;
  NP^A by oracle verifiers. Standard (Baker-Gill-Solovay; verifier NP^A = nondeterministic NP^A).
Suggestion (optional, Lean): a bridge `PEqualNP.Library.P = {L | ComplexityTheory.P (· ∈ L)}` (and NP) would certify the
project's classes against an independent public formalization; cost = transcoder machines for delimit/undelimit on FinTM2.
