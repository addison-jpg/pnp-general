"""cpu/cpu.bench against a pure-Python interpreter of the same instruction set.
Runs the demo (cpu/cpu.asm, 30 steps) and 40 random programs of 30 steps. Standard library only.
   python3 asteroid/tests/test_cpu.py     (exit code 1 on any mismatch)"""
import os, random, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)
from asteroid import cpu

bench = os.path.join(ROOT, "cpu", "cpu.bench"); C = cpu.Cpu(open(bench).read()); bad = 0

def both(rom, steps):
    pc = acc = 0; rp = ra = 0
    for _ in range(steps):
        pc, acc = C.step(rom, pc, acc); rp, ra = cpu.reference_step(rom, rp, ra)
        if (pc, acc) != (rp, ra): return (pc, acc), (rp, ra)
    return (pc, acc), (rp, ra)

rom = cpu.assemble(open(os.path.join(ROOT, "cpu", "cpu.asm")).read())
got, want = both(rom, 30); ok = got == want == (4, 0); bad += not ok
print("demo   ", "PASS" if ok else "FAIL", f"final (PC, ACC) = {got}, reference {want}")
r = random.Random(1)
for t in range(40):
    rom = [(r.randrange(8), r.randrange(16)) for _ in range(16)]
    got, want = both(rom, 30)
    if got != want: bad += 1; print("random", t, "FAIL", got, want)
print("random  ", "PASS" if not bad else "FAIL", "40 programs, every step equal to the reference")
# SIMD: 4 lanes, masks, PRED; demo and 40 random programs with random lane data and masks
S = cpu.Simd(open(os.path.join(ROOT, "cpu", "simd.bench")).read())
def both_simd(rom, accs, ms, steps):
    a = (0, list(accs), list(ms)); b = (0, list(accs), list(ms))
    for _ in range(steps):
        a = S.step(rom, *a); b = cpu.simd_reference_step(rom, *b)
        if a != b: return a, b
    return a, b
rom = cpu.assemble(open(os.path.join(ROOT, "cpu", "simd.asm")).read())
a, b = both_simd(rom, [3, 7, 0, 12], [1] * 4, 60); ok = a == b and a[1] == [0, 0, 0, 0]; bad += not ok
print("simd demo", "PASS" if ok else "FAIL", f"final {a}, reference {b}")
nb = bad
for t in range(40):
    rom = [(r.randrange(8), r.randrange(16)) for _ in range(16)]
    a, b = both_simd(rom, [r.randrange(16) for _ in range(4)], [r.randrange(2) for _ in range(4)], 30)
    if a != b: bad += 1; print("simd random", t, "FAIL", a, b)
print("simd random", "PASS" if bad == nb else "FAIL", "40 programs, every step equal to the reference")
# the subcommand, as typed
p = subprocess.run([os.path.join(ROOT, "bin", "asteroid"), "run-cpu", "cpu/cpu.bench", "--steps", "30"], cwd=ROOT, capture_output=True, text=True)
last = p.stdout.strip().splitlines()[-1] if p.stdout.strip() else ""
ok = p.returncode == 0 and last == "step 30: PC= 4 ACC= 0"; bad += not ok
print("command ", "PASS" if ok else "FAIL", last or p.stderr[-200:])
sys.exit(1 if bad else 0)
