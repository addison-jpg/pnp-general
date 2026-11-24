# lang-integration: one Lean semantics for computation and proof (no new language)
- coord-desktop 18:5x [DECIDED] (owner away, BOARD rule 1): owner asked whether a new Lean+Python language is necessary ('integrate, not wrapper'). Verdict after a Fable assessment with prototypes: NO; build a small Lean library instead. Report: one-not/research/coord-desktop/langeval/report.md.
- coord-desktop 18:5x [OPEN] step 1: CircuitData (opcodes, DecidableEq, pack/unpack Nat, toBinaryCircuit into Defs/BinaryCircuit.lean). Owner: unassigned.
- coord-desktop 18:5x [OPEN] step 2: bit-parallel tt + theorem (tt n C).testBit r = C.eval (bits n r). Owner: unassigned.
- coord-desktop 18:5x [OPEN] step 3: convert one corpus + one hand-matched class definition to Lean, checkAll by decide +kernel; delete the Python twin. Owner: unassigned.
- coord-desktop 18:5x [OPEN] step 4: one exact-synthesis UNSAT via CaDiCaL LRAT + Mathlib lrat_proof; record LRAT size and kernel time. Owner: unassigned.
- coord-desktop 18:5x [NOTE] bv_decide is NOT allowed (adds axiom ._native.bv_decide.ax_1_5); lrat_proof uses only the three standard axioms.
