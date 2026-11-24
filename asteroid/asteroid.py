#!/usr/bin/env python3
"""asteroid: one small language over three engines.
  Python      fast evaluation, search, background jobs      (one-not/tools/search)
  Lean        the kernel decides                             (one-not/lean, SearchCheck.lean, `decide +kernel`)
  matplotlib  pictures                                       (asteroid/out/*.png)
A script is a list of lines; `#` starts a comment. The verbs:

  let NAME = load FILE.json                  a circuit {"n","sets","gates","outs"}
  circuit NAME N                             a circuit written in the script, N inputs named 0 .. N-1, until `end`:
    W = or X Y | W = and X Y | W = not X       a gate; X, Y are inputs or earlier gate names
    set I J K -> W                             the output for the set {I, J, K} is the wire W
  end
  show NAME                                  n, gates, NOT gates, base, witness counts, slack
  claim EXPR [by lean]                       EXPR is  correct(NAME)  or  F(NAME) OP RHS
                                             F in gates nots base witness orwitness slack anyslack margin["conjecture"]
                                             OP in = != < <= > >= ; RHS an integer or F(NAME)
                                             Python evaluates every claim. `by lean` also makes it a Lean theorem
                                             (supported in Lean: correct(NAME); witness / orwitness / slack (NAME) OP integer or base(NAME)).
  claim! EXPR by lean                        send the claim to Lean even when Python says it is false (to watch the kernel reject it)
  claim forall cubes slack(NAME) >= 0 [by lean]   slack at EVERY cube; `by lean` is brute force in the kernel (small n only)
  plot phi NAME [NAME ...] -> FILE.png       expected slack Phi(p) and level means
  hunt "CONJECTURE" SECONDS MAXNOT [SEED] [&]   mutation search; `&` runs it in the background, log in asteroid/out/
  (extensions)                               a file asteroid/ext_NAME.py with `handle(line, api) -> bool` adds verbs
  record DIR ITEM WORD "STATEMENT"           a finding (boards.py) citing this script and, if built, its Lean module

Run from the repository root:
  python3 -m asteroid run SCRIPT.ast [--no-lean]     run one program
  python3 -m asteroid test [--no-lean]               run every program under asteroid/examples
  python3 -m asteroid version
Python proposes, Lean decides: a `by lean` claim counts only if the generated module builds."""
import sys, os, re, json, subprocess, shlex, operator, time
ROOT = os.getcwd(); S = os.path.join(ROOT, "one-not/tools/search"); sys.path.insert(0, S); sys.path.insert(0, ROOT)
import core
from conjectures import REGISTRY
OPS = {"=": operator.eq, "!=": operator.ne, "<": operator.lt, "<=": operator.le, ">": operator.gt, ">=": operator.ge}
LEANOP = {"=": "=", "!=": "≠", "<": "<", "<=": "≤", ">": ">", ">=": "≥"}
env, src, lean_claims, results = {}, {}, [], []

def F(name, arg, conj=None):
    c = env[arg]
    return {"gates": lambda: len(c["gates"]), "nots": lambda: core.nots(c), "base": lambda: core.base(c),
            "witness": lambda: len(core.witness(c, 0, any_gate=True)), "orwitness": lambda: len(core.witness(c, 0, any_gate=False)),
            "slack": lambda: core.slack(c, 0, any_gate=False), "anyslack": lambda: core.slack(c, 0, any_gate=True),
            "correct": lambda: core.correct(c), "margin": lambda: REGISTRY[conj](c)[0]}[name]()

TERM = r'(?:(\w+)(?:\["([^"]+)"\])?\((\w+)\)|(-?\d+))'
def term(m, i):
    f, conj, arg, num = m.group(i), m.group(i + 1), m.group(i + 2), m.group(i + 3)
    return (int(num), None) if num is not None else (F(f, arg, conj), (f, arg))

def do_claim(text, lean):
    m = re.fullmatch(r'forall cubes slack\((\w+)\)\s*>=\s*0', text)
    if m:
        c = env[m.group(1)]; n = c["n"]
        import continuous as C
        sl = C.slack_table(c, 0, any_gate=False); alive = [Q for Q in range(1 << n) if core.base(c, Q) > 0]
        worst = min(int(sl[Q]) for Q in range(1 << n)); ok = worst >= 0
        if lean and (ok or FORCE): lean_claims.append((m.group(1), "claim", f"slackNonnegAll {m.group(1)} = true", text))
        return ok, f"least slack over {1 << n} cubes = {worst} ({len(alive)} cubes with positive base)"
    m = re.fullmatch(r'correct\((\w+)\)', text)
    if m:
        v = F("correct", m.group(1)); ok = v is True
        if lean and (ok or FORCE): lean_claims.append((m.group(1), "correct", f"correctB {m.group(1)} = true", text))
        return ok, f"correct = {v}"
    m = re.fullmatch(TERM + r'\s*(=|!=|<=|>=|<|>)\s*' + TERM, text)
    if not m: raise SystemExit("cannot parse claim: " + text)
    (lv, lt), op, (rv, rt) = term(m, 1), m.group(5), term(m, 6)
    ok = OPS[op](lv, rv)
    if lean and (ok or FORCE):
        if lt and lt[0] in ("witness", "orwitness") and (rt is None or rt[0] == "base"):
            fn = "witnessCount" if lt[0] == "witness" else "(fun C => orWitnessAt C 0)"
            lean_claims.append((lt[1], "claim", f"{fn} {lt[1]} {LEANOP[op]} {rv}", text))
        elif lt and lt[0] == "slack" and rt is None and op in (">=", "<=", "="):
            forms = {">=": [f"slackGe {lt[1]} 0 ({rv}) = true"], "<=": [f"slackLe {lt[1]} 0 ({rv}) = true"]}
            forms["="] = forms[">="] + forms["<="]
            for st in forms[op]: lean_claims.append((lt[1], "claim", st, text))
        else: return ok, f"{lv} {op} {rv}  (NO LEAN FORM for this expression yet: Python only)"
    return ok, f"{lv} {op} {rv}"

def lean_literal(name):
    d = env[name]; op = {"and": 0, "or": 1, "not": 2}
    gl = ", ".join(f"⟨{op[g[0]]}, {g[1]}, {g[2] if len(g) > 2 else g[1]}⟩" for g in d["gates"])
    return f"def {name} : Circ := ⟨{d['n']}, {json.dumps(d['sets'])}, {json.dumps(d['outs'])}, [{gl}]⟩"

def build_lean(script):
    if not lean_claims: return None
    mod = "Asteroid_" + re.sub(r"\W", "_", os.path.splitext(os.path.basename(script))[0])
    path = f"one-not/lean/PEqualNP/W951/{mod}.lean"; names = []
    out = ["import PEqualNP.W951.Asteroid"] + [f"import {i}" for i in dict.fromkeys(EXTRA_LEAN["imports"])] + [ f"/-! Generated by asteroid/asteroid.py from {script}. Do not edit.",
           "Statements about SearchCheck's bit-parallel evaluator (not yet tied to the project's Circuit.eval). -/",
           f"namespace SearchCheck.{mod}"]
    for n in dict.fromkeys(c for c, *_ in lean_claims): out.append(lean_literal(n))
    out += EXTRA_LEAN["decls"]
    for i, (c, kind, stmt, text) in enumerate(lean_claims):
        t = f"{c}_claim{i}"; names.append(t); out.append(f"/-- asteroid: `claim {text}` -/\ntheorem {t} : {stmt} := by decide +kernel")
    out.append(f"end SearchCheck.{mod}")
    open(path, "w").write("\n".join(out) + "\n")
    local = "/home/user/pequalnp-proofs/tools/bin"
    envp = dict(os.environ, PATH=(local + ":" if os.path.isdir(local) else "") + os.environ["PATH"]); t0 = time.time()
    r = subprocess.run(["lake", "build", f"PEqualNP.W951.{mod}"], cwd="one-not/lean", env=envp, capture_output=True, text=True)
    ok = r.returncode == 0
    ax = ""
    if ok:
        tmp = os.path.join(ROOT, "asteroid/out/_axioms.lean")
        open(tmp, "w").write(f"import PEqualNP.W951.{mod}\n" + "".join(f"#print axioms SearchCheck.{mod}.{t}\n" for t in names))
        a = subprocess.run(["lake", "env", "lean", tmp], cwd="one-not/lean", env=envp, capture_output=True, text=True).stdout
        ax = "; ".join(sorted(set(re.findall(r"axioms: \[([^\]]*)\]", a.replace("\n", " "))))) or "none"; os.remove(tmp)
    else: print("\n".join(l for l in (r.stdout + r.stderr).splitlines() if "error" in l)[:1500])
    return {"module": path, "ok": ok, "seconds": round(time.time() - t0, 1), "theorems": names, "axioms": ax}

def plot_phi(names, out):
    import continuous as C, matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    ps = [i / 200 for i in range(201)]; fig, ax = plt.subplots(1, 2, figsize=(12, 4.6))
    for nme in names:
        c = env[nme]; n = c["n"]; m = C.level_means(C.slack_table(c, 0, any_gate=core.nots(c) > 1), n)
        ax[0].plot(ps, [C.bern_eval(m, p) for p in ps], label=f"{nme} (n={n})"); ax[1].plot(range(n + 1), m, marker="o", ms=3, label=nme)
    for a in ax: a.axhline(0, color="k", lw=0.8)
    ax[0].set_xlabel("p"); ax[0].set_ylabel("Phi(p) = expected slack"); ax[1].set_xlabel("points set to 1"); ax[1].set_ylabel("mean slack")
    ax[0].legend(fontsize=7); fig.tight_layout(); fig.savefig(out, dpi=150)

NO_LEAN = False
FORCE = False
EXTRA_LEAN = {"imports": [], "decls": []}   # extensions may add Lean imports and declarations to the generated module
def run(script):
    records = []
    block = None
    for ln, raw in enumerate(open(script), 1):
        line = raw.split("#", 1)[0].strip()
        if not line: continue
        if block is not None:
            name, n, wires, gates, sets, outs = block
            W = lambda x: int(x) if x.isdigit() else wires[x]
            if line == "end":
                env[name] = {"n": n, "sets": sets, "gates": gates, "outs": outs}; block = None
                print(f"{ln}: {name} defined ({n} inputs, {len(gates)} gates, correct {core.correct(env[name])})"); continue
            if m := re.fullmatch(r"(\w+) = (or|and) (\w+) (\w+)", line): gates.append([m.group(2), W(m.group(3)), W(m.group(4))]); wires[m.group(1)] = n + len(gates) - 1
            elif m := re.fullmatch(r"(\w+) = not (\w+)", line): gates.append(["not", W(m.group(2))]); wires[m.group(1)] = n + len(gates) - 1
            elif m := re.fullmatch(r"set ([\d ]+) -> (\w+)", line): sets.append([int(x) for x in m.group(1).split()]); outs.append(W(m.group(2)))
            else: raise SystemExit(f"{script}:{ln}: cannot parse inside circuit: {line}")
            continue
        if m := re.fullmatch(r"circuit (\w+) (\d+)", line): block = (m.group(1), int(m.group(2)), {}, [], [], []); continue
        if m := re.fullmatch(r"let (\w+) = load (\S+)", line):
            d = json.load(open(m.group(2))); env[m.group(1)] = {k: d[k] for k in ("n", "sets", "gates", "outs")}; src[m.group(1)] = m.group(2)
            print(f"{ln}: {m.group(1)} loaded ({d['n']} inputs, {len(d['gates'])} gates)")
        elif m := re.fullmatch(r"show (\w+)", line):
            a = m.group(1); print(f"{ln}: {a}: " + ", ".join(f"{f} {F(f, a)}" for f in ("gates", "nots", "base", "witness", "orwitness", "correct")))
        elif not re.match(r"claim!? (forall c in |forall states |mslack\()", line) and (m := re.fullmatch(r"claim(!?) (.+?)(\s+by lean)?", line)):
            global FORCE
            FORCE = bool(m.group(1)); m = re.fullmatch(r"claim!? (.+?)(\s+by lean)?", line)
            ok, detail = do_claim(m.group(1).strip(), bool(m.group(2)))
            results.append((ln, m.group(1).strip(), ok, bool(m.group(2)))); print(f"{ln}: claim {m.group(1).strip()}: python {'TRUE' if ok else 'FALSE'} ({detail})")
        elif m := re.fullmatch(r"plot phi (.+?) -> (\S+)", line):
            plot_phi(m.group(1).split(), m.group(2)); print(f"{ln}: wrote {m.group(2)}")
        elif m := re.fullmatch(r'hunt "([^"]+)" (\d+) (\d+)(?: (\d+))?(\s*&)?', line):
            cmd = [sys.executable, "-I", "one-not/tools/search/hunt.py", m.group(1), m.group(2), m.group(3), m.group(4) or "0"]
            if m.group(5):
                log = f"asteroid/out/hunt_{int(time.time())}.log"; subprocess.Popen(cmd, stdout=open(log, "w"), stderr=subprocess.STDOUT, start_new_session=True)
                print(f"{ln}: hunt started in the background, log {log}")
            else: print(f"{ln}: " + subprocess.run(cmd, capture_output=True, text=True).stdout.strip().splitlines()[-1])
        elif m := re.fullmatch(r'record (\S+) (\S+) (\w+) "(.+)"', line): records.append(m.groups())
        else:
            import glob, importlib
            api = {"env": env, "src": src, "lean_claims": lean_claims, "results": results, "core": core, "F": F, "ln": ln, "script": script, "extra_lean": EXTRA_LEAN}
            for f in sorted(glob.glob(os.path.join(ROOT, "asteroid", "ext_*.py"))):
                if importlib.import_module("asteroid." + os.path.basename(f)[:-3]).handle(line, api): break
            else: raise SystemExit(f"{script}:{ln}: cannot parse: {line}")
    L = None if NO_LEAN else build_lean(script)
    if NO_LEAN and lean_claims: print(f"lean: skipped (--no-lean); {len(lean_claims)} claims wait for the kernel")
    if L: print(f"lean: {L['module']} {'BUILT' if L['ok'] else 'FAILED'} in {L['seconds']} s; {len(L['theorems'])} theorems; axioms: {L['axioms']}")
    bad = [r for r in results if not r[2]]
    for d, item, word, stmt in records:
        if bad or (word == "checked" and not (L and L["ok"])): print(f"record skipped ({stmt[:40]}...): a claim failed or Lean did not build"); continue
        import boards
        ev = [script] + ([f"{L['module']}::{L['theorems'][-1]}"] if L and L["ok"] else []) + list(dict.fromkeys(src.values()))
        boards.add(d, "asteroid", item, word, stmt, ev); boards.build()
    print(f"claims: {len(results) - len(bad)} true, {len(bad)} false" + (f"; Lean decided {len(L['theorems'])}" if L and L["ok"] else ""))
    return 1 if bad or (L and not L["ok"]) else 0

VERSION = "asteroid 0.3 (Python + Lean kernel + matplotlib)"
def main(argv):
    global NO_LEAN
    NO_LEAN = "--no-lean" in argv; argv = [a for a in argv if a != "--no-lean"]
    if argv[:1] == ["version"]: print(VERSION); return 0
    if argv[:1] == ["run"] and len(argv) == 2: return run(argv[1])
    if argv[:1] == ["test"]:
        import glob; bad = 0
        for f in sorted(glob.glob("asteroid/examples/*.ast")):
            r = subprocess.run([sys.executable, "-m", "asteroid", "run", f] + (["--no-lean"] if NO_LEAN else []), capture_output=True, text=True)
            print(("ok   " if r.returncode == 0 else "FAIL ") + f + "  |  " + (r.stdout.strip().splitlines() or ["(no output)"])[-1]); bad += r.returncode != 0
        return 1 if bad else 0
    if len(argv) == 1 and argv[0].endswith(".ast"): return run(argv[0])
    print(__doc__); return 2

if __name__ == "__main__": sys.exit(main(sys.argv[1:]))
