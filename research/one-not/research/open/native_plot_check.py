"""Check that the native `plot phi` (Lean, SVG) matches Python's Phi to 1e-9 at all 101 points.
Run from the repository folder after: lake exe asteroid hello.ath --no-proof (and first.ath).
  python3 research/one-not/research/open/native_plot_check.py [PROGRAM.ath ...]
The SVG holds the 101 Lean values as 12-place decimals in its <desc>."""
import os, re, sys, subprocess
from fractions import Fraction
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path[:0] = [ROOT, os.path.join(ROOT, "research", "one-not", "tools", "search")]
import numpy as np
import asteroid.asteroid as A, continuous as C

def main(progs):
    bad = 0
    for prog in progs:
        prog = os.path.join(ROOT, prog) if not os.path.isabs(prog) else prog
        svg = os.path.join(ROOT, "asteroid", "out", "native_check_" + os.path.basename(prog)[:-4] + ".svg")
        text = open(prog, encoding="utf-8").read()
        names = re.findall(r"^(?:let (\w+) = load|circuit (\w+))", text, re.M); names = [a or b for a, b in names]
        tmp = os.path.join(os.path.dirname(prog), "_native_plot_check.ath")
        open(tmp, "w", encoding="utf-8").write(re.sub(r"(?m)^plot .*\n", "", text) + f"plot phi {' '.join(names)} -> {svg}\n")
        try:
            r = subprocess.run([os.path.join(ROOT, "asteroid/native/.lake/build/bin/asteroid"), tmp, "--no-proof"], capture_output=True, text=True)
        finally:
            os.remove(tmp)
        desc = re.search(r"<desc>(.*?)</desc>", open(svg, encoding="utf-8").read(), re.S).group(1).strip().splitlines()[1:]
        lean = {l.split()[0]: [Fraction(x) for x in l.split()[2:]] for l in desc}
        py = python_circuits(prog, names)
        for nm in names:
            c = py[nm]; n = c["n"]
            m = C.level_means(C.slack_table(c, 0, any_gate=False), n)
            worst = max(abs(float(C.bern_eval(m, Fraction(k, 100)) - lean[nm][k])) for k in range(101))
            ok = worst < 1e-9 and len(lean[nm]) == 101
            bad += not ok
            print(f"{os.path.basename(prog)} {nm}: n={n}, max |Python - Lean| over 101 points = {worst:.2e}  {'OK' if ok else 'MISMATCH'}")
    return 1 if bad else 0

def python_circuits(prog, names):
    """The circuits as the Python asteroid defines them (its `run` on the program without plot lines)."""
    import io, contextlib, tempfile
    A.NO_LEAN = True
    src = re.sub(r"(?m)^plot .*\n", "", open(prog, encoding="utf-8").read())
    tmp = os.path.join(os.path.dirname(prog), "_native_plot_py.ath")
    open(tmp, "w", encoding="utf-8").write(src)
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            A.run(tmp)
    finally:
        os.remove(tmp)
    return dict(A.env)

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:] or ["hello.ath", "asteroid/examples/first.ath"]))
