"""asteroid extension (stand-in, NOT "Eureka"; see asteroid/EUREKA.md):
  prove "STATEMENT" by TACTIC
STATEMENT is a Lean proposition (e.g. 2 ^ 10 = 1024, or  ∀ n : Nat, n + 0 = n); TACTIC is one of
decide, omega, simp, aesop, norm_num, rfl, or `decide +kernel`. The statement becomes
`theorem t : STATEMENT := by TACTIC` in a scratch module (imports Mathlib) and `lake env lean` checks it.
Under --no-lean, or when lake is missing, the verb prints that it was skipped and succeeds."""
import re, os, shutil, subprocess, tempfile
import asteroid.asteroid as A

TACTICS = {"decide", "omega", "simp", "aesop", "norm_num", "rfl", "decide +kernel", "simp_arith", "trivial"}

def handle(line, api):
    m = re.fullmatch(r'prove "([^"\n]+)" by ([\w +]+?)', line)
    if not m: return False
    stmt, tac, ln = m.group(1), m.group(2).strip(), api["ln"]
    if tac not in TACTICS: raise SystemExit(f"{api['script']}:{ln}: prove: tactic must be one of {sorted(TACTICS)}")
    text = f"prove {stmt} by {tac}"
    if A.NO_LEAN or not shutil.which("lake"):
        print(f"{ln}: {text}: skipped ({'--no-lean' if A.NO_LEAN else 'lake not found'})"); return True
    src = f"import Mathlib\n\ntheorem asteroid_prove : {stmt} := by {tac}\n"
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "Prove.lean"); open(p, "w").write(src)
        r = subprocess.run(["lake", "env", "lean", p], cwd="one-not/lean", capture_output=True, text=True, timeout=600)
    ok = r.returncode == 0
    api["results"].append((ln, text, ok, True))
    print(f"{ln}: {text}: kernel {'ACCEPTED' if ok else 'REJECTED'}" + ("" if ok else ": " + (r.stdout + r.stderr).strip().splitlines()[0][:160]))
    return True
