"""asteroid extension: the base verifier. The check itself is PURE LEAN (`PEqualNP/Verify/Axioms.lean`: the command
`#verify_axioms` walks every theorem of every module and fails the build on any axiom besides propext,
Classical.choice, Quot.sound, except `sorryAx` for the names listed after `allowing`). asteroid only starts it
and reads its one summary line.

  verify lean PROJECT_DIR [within SECONDS]     e.g.  verify lean proofs/w951
  theorem FULL.NAME from MODULE in PROJECT_DIR e.g.  theorem SearchCheck.correctB_sound_project from PEqualNP.W951.AsteroidSound in proofs/w951
"""
import re, os, subprocess, glob, time
from asteroid import asteroid as A

STD = {"propext", "Classical.choice", "Quot.sound"}
def _env():
    return A.lake_env()

def write_all(proj):
    """Regenerate the import list of PEqualNP/Verify/All.lean, keeping its `#verify_axioms` line and comment."""
    p = os.path.join(proj, "PEqualNP/Verify/All.lean"); old = open(p, encoding="utf-8").read()
    tail = old[old.index("import PEqualNP.Verify.Axioms"):]
    files = [f.replace(os.sep, "/") for f in glob.glob(os.path.join(proj, "PEqualNP/**/*.lean"), recursive=True)]
    mods = sorted(f[len(proj) + 1:-5].replace("/", ".") for f in files if "/Verify/" not in f)
    new = "".join(f"import {m}\n" for m in mods) + tail
    if new != old: open(p, "w", encoding="utf-8", newline="\n").write(new)
    return len(mods)

def handle(line, api):
    ln = api["ln"]
    if m := re.fullmatch(r"verify lean (\S+)(?: within (\d+))?", line):
        proj = m.group(1).rstrip("/"); text = f"verify lean {proj}"
        if A.NO_LEAN: print(f"{ln}: {text}: skipped (--no-lean)"); return True
        n = write_all(proj); t0 = time.time()
        try: r = subprocess.run([A.lake(), "build", "PEqualNP.Verify.All"], cwd=proj, env=_env(), capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=int(m.group(2) or 1500))
        except subprocess.TimeoutExpired:
            api["results"].append((ln, text, False, True)); print(f"{ln}: {text}: NOT FINISHED within the time limit ({n} modules); no verdict"); return True
        out = r.stdout + r.stderr; s = re.search(r"verify_axioms \S+: (\d+) modules, (\d+) theorems; (\d+) on propext[^;]*; (\d+) allowed to depend on sorryAx", out)
        ok = r.returncode == 0 and s is not None
        api["results"].append((ln, text, ok, True))
        if ok: print(f"{ln}: {text}: PURE LEAN OK in {time.time() - t0:.0f} s: {s.group(1)} modules, {s.group(2)} theorems, {s.group(3)} on the three standard axioms only, {s.group(4)} on the allow-list for sorryAx")
        else: print(f"{ln}: {text}: FAILED\n" + "\n".join(l for l in out.splitlines() if "error" in l or "depend on other axioms" in l or "(module" in l)[:2500])
        return True
    if m := re.fullmatch(r"theorem (\S+) from (\S+) in (\S+)", line):
        name, mod, proj = m.groups(); text = f"theorem {name}"
        if A.NO_LEAN: print(f"{ln}: {text}: skipped (--no-lean)"); return True
        tmp = os.path.abspath("asteroid/out/_thm.lean"); open(tmp, "w", encoding="utf-8", newline="\n").write(f"import {mod}\n#print axioms {name}\n")
        r = subprocess.run([A.lake(), "env", "lean", tmp], cwd=proj, env=_env(), capture_output=True, text=True, encoding="utf-8", errors="replace"); os.remove(tmp)
        out = (r.stdout + r.stderr).replace("\n", " "); a = re.search(r"depends on axioms: \[([^\]]*)\]", out)
        ax = {x.strip() for x in a.group(1).split(",")} if a else (set() if "does not depend on any axioms" in out else None)
        ok = r.returncode == 0 and ax is not None and ax <= STD
        api["results"].append((ln, text, ok, True))
        print(f"{ln}: {text}: " + (f"CHECKED, axioms {sorted(ax) or 'none'}" if ok else f"NOT ACCEPTED ({sorted(ax) if ax is not None else out[:200]})"))
        return True
    return False
