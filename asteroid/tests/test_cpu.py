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
# the subcommand, as typed
p = subprocess.run([os.path.join(ROOT, "bin", "asteroid"), "run-cpu", "cpu/cpu.bench", "--steps", "30"], cwd=ROOT, capture_output=True, text=True)
last = p.stdout.strip().splitlines()[-1] if p.stdout.strip() else ""
ok = p.returncode == 0 and last == "step 30: PC= 4 ACC= 0"; bad += not ok
print("command ", "PASS" if ok else "FAIL", last or p.stderr[-200:])
sys.exit(1 if bad else 0)
