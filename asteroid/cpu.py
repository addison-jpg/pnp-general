"""asteroid run-cpu: the state loop of cpu/cpu.bench (a 4-bit accumulator machine in AND, OR, NOT).

  asteroid run-cpu cpu/cpu.bench [--prog FILE.asm] --steps N

The circuit is combinational: inputs pc0..pc3, acc0..acc3 and the 16 ROM words r<w>_<b>, outputs npc0..3, nacc0..3.
This module feeds the outputs back as the inputs N times and prints PC and ACC at each step. Python only.
Assembly: one instruction per line, `MNEMONIC [operand]`, `#` comments; the rest of the ROM is `LOAD 0`.
"""
import os, sys
from asteroid import ext_bench as B

OPS = ["LOAD", "ADD", "SUB", "AND", "OR", "NOT", "JMP", "JZ"]


def assemble(text):
    """Program text to 16 (op, imm) pairs; the rest of the ROM is `LOAD 0`."""
    prog = []
    for ln, line in enumerate(text.splitlines(), 1):
        t = line.split("#")[0].split()
        if not t: continue
        if t[0].upper() not in OPS: raise SystemExit(f"line {ln}: unknown instruction {t[0]} (known: {' '.join(OPS)})")
        op = OPS.index(t[0].upper()); imm = int(t[1], 0) if len(t) > 1 else 0
        if not 0 <= imm < 16: raise SystemExit(f"line {ln}: operand {imm} is not in 0..15")
        prog.append((op, imm))
    if len(prog) > 16: raise SystemExit("the ROM has 16 words")
    return prog + [(0, 0)] * (16 - len(prog))


def reference_step(rom, pc, acc):
    """The instruction set, in plain Python."""
    op, imm = rom[pc]
    if op == 0: return (pc + 1) % 16, imm
    if op == 1: return (pc + 1) % 16, (acc + imm) % 16
    if op == 2: return (pc + 1) % 16, (acc - imm) % 16
    if op == 3: return (pc + 1) % 16, acc & imm
    if op == 4: return (pc + 1) % 16, acc | imm
    if op == 5: return (pc + 1) % 16, ~acc & 15
    if op == 6: return imm, acc
    return (imm if acc == 0 else (pc + 1) % 16), acc


class Cpu:
    def __init__(self, bench_src):
        nl = B.parse(bench_src); self.c = B.to_circ(nl); self.names = nl["inputs"]
        if self.c["sets"]: raise SystemExit("cpu.bench has directives; expected a plain circuit")

    def step(self, rom, pc, acc):
        env = {"pc%d" % i: pc >> i & 1 for i in range(4)}
        env.update({"acc%d" % i: acc >> i & 1 for i in range(4)})
        for w, (op, imm) in enumerate(rom):
            for b in range(4): env[f"r{w}_{b}"] = imm >> b & 1
            for b in range(3): env[f"r{w}_{b + 4}"] = op >> b & 1
        v = [env[x] for x in self.names]
        for g in self.c["gates"]:
            v.append(1 - v[g[1]] if g[0] == "not" else (v[g[1]] & v[g[2]] if g[0] == "and" else v[g[1]] | v[g[2]]))
        o = [v[w] for w in self.c["outs"]]
        return sum(o[i] << i for i in range(4)), sum(o[4 + i] << i for i in range(4))


def run(bench, prog, steps, out=print):
    cpu = Cpu(open(bench, encoding="utf-8").read()); rom = assemble(open(prog, encoding="utf-8").read())
    pc = acc = 0; out(f"step  0: PC={pc:2d} ACC={acc:2d}")
    for k in range(1, steps + 1):
        pc, acc = cpu.step(rom, pc, acc); out(f"step {k:2d}: PC={pc:2d} ACC={acc:2d}")
    return pc, acc


def main(argv, root):
    a = list(argv); steps = 40; prog = None
    if "--steps" in a: i = a.index("--steps"); steps = int(a[i + 1]); del a[i:i + 2]
    if "--prog" in a: i = a.index("--prog"); prog = a[i + 1]; del a[i:i + 2]
    if len(a) != 1: print("usage: asteroid run-cpu cpu/cpu.bench [--prog FILE.asm] --steps N"); return 2
    bench = a[0]; prog = prog or os.path.splitext(bench)[0] + ".asm"
    for f in (bench, prog):
        if not os.path.isfile(f): print(f"run-cpu: no file {f}"); return 1
    run(bench, prog, steps); return 0
