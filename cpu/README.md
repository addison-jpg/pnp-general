# A small CPU in AND, OR and NOT

A 4-bit accumulator machine whose whole next-state logic is one ISCAS `.bench` circuit, `cpu.bench`: AND and OR with two inputs, NOT with one, and as few NOT gates as the design needs.

Run it (Python only, no Lean):

    bin/asteroid run-cpu cpu/cpu.bench --steps 24

It feeds the outputs back as inputs and prints PC and ACC at each step. The program is `cpu/cpu.asm` (count down from 5 to 0, then halt in a loop); `--prog FILE.asm` runs another. The default is the `.asm` beside the `.bench`.

## Machine

- State: PC (4 bits), ACC (4 bits). ROM: 16 words of 7 bits, opcode (3) and operand (4).
- Opcodes: 0 LOAD, 1 ADD, 2 SUB, 3 AND, 4 OR, 5 NOT (of ACC, operand ignored), 6 JMP, 7 JZ (jump if ACC is 0, tested before the instruction runs). ADD and SUB wrap modulo 16.
- Inputs of `cpu.bench` (120): `pc0..pc3`, `acc0..acc3` (least significant bit first), then the ROM as inputs `r<w>_<b>` (word w, bits 0..3 operand, 4..6 opcode). The program is not wired into the circuit: the runner holds the ROM inputs constant. This makes the circuit one CPU for every program, and the format has no constant gate.
- Outputs (8): `npc0..npc3`, `nacc0..nacc3`.
- `cpu/gen_cpu.py` writes `cpu.bench`; `python3 cpu/gen_cpu.py naive` prints the counts of the first design.

## Gate counts

| design | total | AND | OR | NOT |
|---|---|---|---|---|
| straightforward (a NOT at every use, XOR as (a OR b) AND NOT(a AND b)) | 424 | 221 | 158 | 45 |
| **`cpu.bench`** (negations pushed to the inputs by De Morgan, shared) | **443** | 238 | 190 | **15** |

The 15 NOT gates are the negations of the 4 PC bits, the 4 ACC bits and the 7 instruction bits (the ROM word after it is selected by PC). Everything after those literals is a monotone AND/OR circuit: each signal is built on the rail it is used on, a negated signal by the De Morgan dual, so no further NOT is needed. The price is 49 more AND/OR gates than the first design (428 against 379), the cost of building both polarities of the adder; the NOT count falls from 45 to 15.

## Fischer's bound

The repository checks the Markov and Fischer theorem that logarithmically many NOT gates suffice (`lean/PEqualNP/General/FischerMain.lean`, `PEqualNP.General.Gap.L104`: ⌈log₂(n + 1)⌉ NOT gates, up to a polynomial blow-up in size). For the 120 inputs of `cpu.bench` that is ⌈log₂ 121⌉ = 7; with the ROM held constant, the 8 state bits would give 4. Fischer's construction is not built here, and its size blow-up would cost far more AND/OR gates than the 49 saved above. 15 is the count of this hand design, not a lower bound.

## Test

`python3 asteroid/tests/test_cpu.py` runs the demo and 40 random programs against a pure-Python interpreter of the same instruction set, comparing PC and ACC at every step; `bin/asteroid run-cpu` is run as typed.
