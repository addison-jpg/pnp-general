"""Generate cpu/cpu.bench: the next-state logic of a 4-bit accumulator machine, in AND, OR, NOT (fan-in 2).

  python3 cpu/gen_cpu.py            writes cpu/cpu.bench (few NOT gates)
  python3 cpu/gen_cpu.py naive      prints the gate counts of the straightforward design (a NOT at every use)

Inputs: pc0..pc3, acc0..acc3 (least significant bit first), then the ROM: r<w>_<b>, word w = 0..15, bit b = 0..6
(b = 0..3 the operand, b = 4..6 the opcode). Outputs: npc0..npc3, nacc0..nacc3.
Opcodes: 0 LOAD, 1 ADD, 2 SUB, 3 AND, 4 OR, 5 NOT, 6 JMP, 7 JZ.
"""
import os, sys


class Naive:
    """Wires are names. NOT is a real gate, one per use. XOR(a,b) = (a OR b) AND NOT(a AND b)."""
    def __init__(self): self.gates, self.n, self.memo = [], 0, {}
    def _g(self, op, *a):
        key = (op,) + (tuple(sorted(a)) if op != "NOT" else a)
        if op != "NOT" and key in self.memo: return self.memo[key]     # AND/OR shared; NOT is not
        self.n += 1; w = f"g{self.n}"; self.gates.append((w, op, a))
        if op != "NOT": self.memo[key] = w
        return w
    def AND(self, a, b): return self._g("AND", a, b)
    def OR(self, a, b): return self._g("OR", a, b)
    def NOT(self, a): return self._g("NOT", a)
    def XOR(self, a, b): return self.AND(self.OR(a, b), self.NOT(self.AND(a, b)))
    def inp(self, x): return x
    def out(self, x): return x
    def cut(self, x): return x


class Dual:
    """Negation is free in the description and pushed to the inputs (De Morgan): a signal is a pair of lazy
    rails (positive, negative); NOT swaps them, AND(a,b) = (a.p & b.p, a.n | b.n). Only the rails that are used
    are built. The only NOT gates are one per input literal that is used negatively, shared by every use."""
    def __init__(self): self.gates, self.n, self.memo, self.nots = [], 0, {}, {}
    def _g(self, op, a, b):
        key = (op,) + tuple(sorted((a, b)))
        if key not in self.memo:
            self.n += 1; w = f"g{self.n}"; self.gates.append((w, op, (a, b))); self.memo[key] = w
        return self.memo[key]
    def inp(self, x): return ("in", x)
    def NOT(self, s): return ("not", s)
    def AND(self, a, b): return ("and", a, b)
    def OR(self, a, b): return ("or", a, b)
    def XOR(self, a, b): return self.OR(self.AND(a, self.NOT(b)), self.AND(self.NOT(a), b))
    def rail(self, s, pos=True):
        k = s[0]
        if k == "not": return self.rail(s[1], not pos)
        if k == "in":
            if pos: return s[1]
            if s[1] not in self.nots:
                self.n += 1; w = f"g{self.n}"; self.gates.append((w, "NOT", (s[1],))); self.nots[s[1]] = w
            return self.nots[s[1]]
        a, b = self.rail(s[1], pos), self.rail(s[2], pos)
        return self._g("AND" if (k == "and") == pos else "OR", a, b)
    def out(self, s): return self.rail(s, True)
    def cut(self, s): return ("in", self.rail(s, True))     # build the signal, then treat its wire as an input literal


def build(B):
    I, A = B.inp, B.AND
    OR = B.OR
    def big(f, xs):
        r = xs[0]
        for x in xs[1:]: r = f(r, x)
        return r
    pc = [I(f"pc{i}") for i in range(4)]; acc = [I(f"acc{i}") for i in range(4)]
    rom = [[I(f"r{w}_{b}") for b in range(7)] for w in range(16)]
    inputs = [f"pc{i}" for i in range(4)] + [f"acc{i}" for i in range(4)] + [f"r{w}_{b}" for w in range(16) for b in range(7)]
    lit = lambda s, v: s if v else B.NOT(s)
    # fetch: select word pc, then the 7 bits of the instruction
    lo = [A(lit(pc[1], k >> 1 & 1), lit(pc[0], k & 1)) for k in range(4)]
    hi = [A(lit(pc[3], k >> 1 & 1), lit(pc[2], k & 1)) for k in range(4)]
    sel = [A(hi[w >> 2], lo[w & 3]) for w in range(16)]
    ins = [B.cut(big(OR, [A(sel[w], rom[w][b]) for w in range(16)])) for b in range(7)]
    imm, op = ins[:4], ins[4:]
    is_ = [big(A, [lit(op[j], k >> j & 1) for j in range(3)]) for k in range(8)]
    LOAD, ADD, SUB, AND_, OR_, NOT_, JMP, JZ = is_
    # arithmetic: acc + (imm xor sub) + sub
    sub = SUB; c = sub; s = []
    for j in range(4):
        b = B.XOR(imm[j], sub); p = B.XOR(acc[j], b)
        s.append(B.XOR(p, c)); c = OR(A(acc[j], b), A(c, OR(acc[j], b)))
    arith = B.OR(ADD, SUB)
    nacc = []
    for j in range(4):
        terms = [A(LOAD, imm[j]), A(arith, s[j]), A(AND_, A(acc[j], imm[j])), A(OR_, OR(acc[j], imm[j])),
                 A(NOT_, B.NOT(acc[j])), A(OR(JMP, JZ), acc[j])]
        nacc.append(big(OR, terms))
    # next pc: jump (to imm) or pc + 1
    zero = B.NOT(big(OR, acc))
    jump = OR(JMP, A(JZ, zero))
    carry = [pc[0], A(pc[0], pc[1]), A(A(pc[0], pc[1]), pc[2])]
    inc = [B.NOT(pc[0])] + [B.XOR(pc[j], carry[j - 1]) for j in range(1, 4)]
    npc = [OR(A(jump, imm[j]), A(B.NOT(jump), inc[j])) for j in range(4)]
    outs = npc + nacc
    return inputs, [B.out(o) for o in outs]


def counts(B):
    c = {"AND": 0, "OR": 0, "NOT": 0}
    for _, op, _ in B.gates: c[op] += 1
    return c


def write(B, inputs, outs, path):
    names = [f"npc{i}" for i in range(4)] + [f"nacc{i}" for i in range(4)]
    c = counts(B)
    L = [f"# cpu: 4-bit accumulator machine, next state; {len(B.gates)} gates: {c['AND']} AND, {c['OR']} OR, {c['NOT']} NOT"]
    L += [f"INPUT({x})" for x in inputs] + [f"OUTPUT({x})" for x in names]
    L += [f"{w} = {op}({', '.join(a)})" for w, op, a in B.gates]
    L += [f"{n} = BUFF({o})" for n, o in zip(names, outs)]
    open(path, "w", newline="\n").write("\n".join(L) + "\n")


if __name__ == "__main__":
    if sys.argv[1:] == ["naive"]:
        B = Naive(); build(B); print("naive", counts(B), len(B.gates))
    else:
        B = Dual(); ins, outs = build(B); c = counts(B); print("dual", c, len(B.gates))
        write(B, ins, outs, os.path.join(os.path.dirname(os.path.abspath(__file__)), "cpu.bench"))
