#!/usr/bin/env python3
"""asteroid: one small language over three engines.
  Python      fast evaluation, search, background jobs      (one-not/tools/search)
  Lean        the kernel decides                             (one-not/lean, SearchCheck.lean, `decide +kernel`)
  matplotlib  pictures                                       (asteroid/out/*.png)
A script is a list of lines; `#` starts a comment. The verbs:

  let NAME = load FILE.bench                 a circuit in the ISCAS .bench format (asteroid/BENCH.md); also FILE.json
  save NAME -> FILE.bench                    write a circuit as a .bench file
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
  conjecture NAME: EXPR                      EXPR with the circuit variable c; then NAME(X) is a claim expression
  hunt NAME SECONDS MAXNOT [SEED]            search for a circuit where the conjecture NAME fails; binds NAME_cex
  hunt "CONJECTURE" SECONDS MAXNOT [SEED] [&]   mutation search; `&` runs it in the background, log in asteroid/out/
  (extensions)                               a file asteroid/ext_NAME.py with `handle(line, api) -> bool` adds verbs
  record DIR ITEM WORD "STATEMENT"           a finding (boards.py) citing this script and, if built, its Lean module

Run from anywhere with the launcher in the repository's bin folder (bin/asteroid; on Windows also bin\\asteroid.cmd
and bin\\asteroid.ps1). Nothing is installed outside the repository. Below, `asteroid` stands for that launcher:
  asteroid                          the interactive prompt (also: asteroid repl); asteroid idle is the window
  asteroid FILE.ath                 run one program (also: asteroid run FILE.ath)
  asteroid setup                    once: numpy and matplotlib in a .venv inside the repository
  asteroid demo                     a tiny built-in program: start here
  asteroid test                     run every program under asteroid/examples and asteroid/programs
  asteroid version
  asteroid doctor                   (also --doctor) what this machine has: Python, numpy, matplotlib, Lean, and what a run will do
  --no-lean  (--no-proof)           evaluate only, prove nothing. Chosen automatically when Lean is not installed.
  --no-color                        no colours (also automatic when piped or NO_COLOR is set)
  --show-lean                       also print the generated Lean files and the axioms used
Python proposes, Lean decides: a `by lean` claim counts only if the generated module builds."""
import sys, os, re, json, subprocess, shlex, operator, time, shutil, functools
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))   # the repository, wherever the command is typed
CALLER_DIR = os.getcwd()
os.chdir(ROOT)
S = os.path.join(ROOT, "one-not/tools/search"); sys.path.insert(0, S); sys.path.insert(0, ROOT)
import core
from conjectures import REGISTRY
OPS = {"=": operator.eq, "!=": operator.ne, "<": operator.lt, "<=": operator.le, ">": operator.gt, ">=": operator.ge}
LEANOP = {"=": "=", "!=": "≠", "<": "<", "<=": "≤", ">": ">", ">=": "≥"}
env, src, lean_claims, results = {}, {}, [], []

EXTRA_F = {}     # name -> function of a circuit; extensions add first-class terms here (ext_edges: flip, flipclasses, flipslack)
def F(name, arg, conj=None):
    c = env[arg]
    if not EXTRA_F: _exts()
    if name in EXTRA_F: return EXTRA_F[name](c)
    return {"gates": lambda: len(c["gates"]), "nots": lambda: core.nots(c), "base": lambda: core.base(c),
            "witness": lambda: len(core.witness(c, 0, any_gate=True)), "orwitness": lambda: len(core.witness(c, 0, any_gate=False)),
            "slack": lambda: core.slack(c, 0, any_gate=False), "anyslack": lambda: core.slack(c, 0, any_gate=True),
            "correct": lambda: core.correct(c), "margin": lambda: REGISTRY[conj](c)[0]}[name]()

TERM = r'(?:(\w+)(?:\["([^"]+)"\])?\((\w+)\)|(-?\d+))'
def term(m, i):
    f, conj, arg, num = m.group(i), m.group(i + 1), m.group(i + 2), m.group(i + 3)
    return (int(num), None) if num is not None else (F(f, arg, conj), (f, arg))

RESERVED = ["tt", "varTT", "correctB", "witnessCount", "hasWitness", "Gate", "Circ", "def", "theorem", "end", "open", "import", "namespace", "by", "at", "in", "if", "then", "else", "let", "have", "show", "from", "do", "fun", "Type", "Prop", "true", "false"]
def check_name(name, where):
    if name in RESERVED: raise SystemExit(f"{where}: the name `{name}` is taken by the proof library; pick another name for this circuit")

def lake_env():
    """The environment for Lean: PATH as it is, then two fallbacks: the folder used in the project's own container
    (if it exists) and the standard elan folder (~/.elan/bin, on Windows %USERPROFILE%\\.elan\\bin)."""
    home = [os.environ.get("ELAN_HOME"), os.path.join(os.path.expanduser("~"), ".elan"),
            os.path.join(os.environ["USERPROFILE"], ".elan") if os.environ.get("USERPROFILE") else None]
    # the container's folder holds a wrapper that queues builds; it exists nowhere else, so elsewhere elan's is used
    dirs = ["/home/user/pequalnp-proofs/tools/bin"] + [os.path.join(h, "bin") for h in home if h]
    path = [x for x in os.environ.get("PATH", "").split(os.pathsep) if x]
    return dict(os.environ, PATH=os.pathsep.join(path + [d for d in dict.fromkeys(dirs) if os.path.isdir(d) and d not in path]))

@functools.lru_cache(maxsize=None)
def lake():
    """Full path of the `lake` command, or None. A full path, because Windows does not search the child's PATH."""
    return shutil.which("lake", path=lake_env()["PATH"])

LEAN_DIR = os.path.join(ROOT, "one-not", "lean")
def mathlib_cache():
    b = os.path.join(LEAN_DIR, ".lake", "packages", "mathlib", ".lake", "build", "lib")
    return any(os.path.isfile(os.path.join(b, sub, "Mathlib.olean")) for sub in ("", "lean"))

def need(mod, what):
    """Import numpy or matplotlib when a line needs it. Missing: the line is skipped with one message (see run)."""
    import importlib
    try: return importlib.import_module(mod)
    except ImportError as e:
        e.asteroid = f"{what} needs {mod}: run bin/setup"; raise

PROG_DIR = ROOT   # the folder of the program being run (set by run)
def _plain(p):
    p = p.strip(); return p[1:-1] if len(p) >= 2 and p[0] == p[-1] and p[0] in "\"'" else p
def in_path(p):
    """A file a program reads: a path with spaces is fine, quotes are optional. A relative path is looked for
    beside the program first, then in the repository (the shipped programs name their files from the repository)."""
    p = _plain(p)
    if os.path.isabs(p): return p
    a = os.path.join(PROG_DIR, p)
    return a if os.path.exists(a) or not os.path.exists(p) else p
def out_path(p):
    """A file a program writes: from the repository for a program inside it, else beside the program. Folders are made."""
    p = _plain(p)
    inside = os.path.commonpath([ROOT, PROG_DIR]) == ROOT if os.path.splitdrive(ROOT)[0].lower() == os.path.splitdrive(PROG_DIR)[0].lower() else False
    if not os.path.isabs(p) and not inside: p = os.path.join(PROG_DIR, p)
    os.makedirs(os.path.dirname(os.path.abspath(p)), exist_ok=True); return p

CONJ = {}      # name -> expression with the circuit variable `c`
API = {}
def _exts():
    import glob, importlib
    return [importlib.import_module("asteroid." + os.path.basename(f)[:-3]) for f in sorted(glob.glob(os.path.join(ROOT, "asteroid", "ext_*.py")))]

def do_claim(text, lean):
    if text.startswith("not "):                         # negation: Python only
        ok, detail = do_claim(text[4:].strip(), False); return (not ok), "not: " + detail
    m = re.fullmatch(r'(\w+)\((\w+)\)', text)
    if m and m.group(1) in CONJ:                       # a conjecture applied to a circuit
        return do_claim(re.sub(r"\(c\)", f"({m.group(2)})", CONJ[m.group(1)]), lean)
    for e in _exts():                                  # claim forms added by extensions (mixed slack, ...)
        if hasattr(e, "claim_expr"):
            r = e.claim_expr(text, lean, API, force=FORCE)
            if r is not None: return r[0], r[1]
    m = re.fullmatch(r'forall cubes slack\((\w+)\)\s*>=\s*0', text)
    if m:
        c = env[m.group(1)]; n = c["n"]
        try: import continuous as C; sl = C.slack_table(c, 0, any_gate=False)
        except ImportError: sl = [core.slack(c, Q, any_gate=False) for Q in range(1 << n)]   # no numpy: the same numbers, slower
        alive = [Q for Q in range(1 << n) if core.base(c, Q) > 0]
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

def hunt_conjecture(name, secs, max_not, seed):
    """Mutation search for a circuit on which the conjecture is false. Starts from every circuit in scope.
    A counterexample is bound to NAME_cex and saved under asteroid/out/. Finding nothing proves nothing."""
    import random, copy, hunt as H
    rng = random.Random(seed); starts = [copy.deepcopy(c) for c in env.values() if c["n"] <= 8]
    starts += [H.or_tree(c["n"], c["sets"]) for c in starts]
    if not starts: return f"hunt {name}: no circuit with at most 8 inputs in scope"
    def margin(c):
        """lhs - rhs for `F(c) >= G(c)` or `F(c) >= k` (below 0 = counterexample); else 0 / -1 for true / false."""
        env["_h"] = c
        try:
            ex = re.sub(r"\(c\)", "(_h)", CONJ[name]); m = re.fullmatch(TERM + r"\s*(>=|>)\s*" + TERM, ex)
            if m:
                (lv, _), (rv, _) = term(m, 1), term(m, 6); return lv - rv - (1 if m.group(5) == ">" else 0)
            return 0 if do_claim(ex, False)[0] else -1
        finally: env.pop("_h", None)
    t0 = time.time(); tried = 0
    while time.time() - t0 < secs:
        cur = copy.deepcopy(rng.choice(starts)); mc = margin(cur); stall = 0
        while time.time() - t0 < secs and stall < 300:
            new = (H.rewrite if rng.random() < 0.4 else H.mutate)(cur, rng, max_not); tried += 1
            if len(new["gates"]) > 70 or core.nots(new) > max_not or not core.correct(new): stall += 1; continue
            new = core.prune(new); mn = margin(new)
            if mn > mc: stall += 1; continue
            stall = 0 if mn < mc else stall + 1; cur, mc = new, mn
            if mn < 0:
                env[name + "_cex"] = new; p = f"asteroid/out/{name}_cex.json"; json.dump(new, open(p, "w", encoding="utf-8", newline="\n")); src[name + "_cex"] = p
                return f"hunt {name}: COUNTEREXAMPLE after {tried} moves ({new['n']} inputs, {len(new['gates'])} gates, {core.nots(new)} NOT), bound to {name}_cex, saved {p}"
    return f"hunt {name}: no counterexample in {tried} moves ({secs} s, at most {max_not} NOT gates); this proves nothing"

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
    open(path, "w", encoding="utf-8", newline="\n").write("\n".join(out) + "\n")
    envp = lake_env(); t0 = time.time()
    r = subprocess.run([lake(), "build", f"PEqualNP.W951.{mod}"], cwd=LEAN_DIR, env=envp, capture_output=True, text=True, encoding="utf-8", errors="replace")
    ok = r.returncode == 0
    ax = ""
    if ok:
        tmp = os.path.join(ROOT, f"asteroid/out/_axioms_{os.getpid()}.lean")
        open(tmp, "w", encoding="utf-8", newline="\n").write(f"import PEqualNP.W951.{mod}\n" + "".join(f"#print axioms SearchCheck.{mod}.{t}\n" for t in names))
        a = subprocess.run([lake(), "env", "lean", tmp], cwd=LEAN_DIR, env=envp, capture_output=True, text=True, encoding="utf-8", errors="replace").stdout
        ax = "; ".join(sorted(set(re.findall(r"axioms: \[([^\]]*)\]", a.replace("\n", " "))))) or "none"; os.remove(tmp)
    else: print("\n".join(l for l in (r.stdout + r.stderr).splitlines() if "error" in l)[:1500])
    res = {"module": path, "ok": ok, "seconds": round(time.time() - t0, 1), "theorems": names, "axioms": ax, "sound": None}
    if ok: res["sound"] = build_sound(mod, names, envp)
    return res

def build_sound(mod, names, envp):
    """The same claims read in the PROJECT's definitions (Circuit.eval, F2, baseDQ), through AsteroidSound(2).lean."""
    out, made, done_ok = [f"import PEqualNP.W951.{mod}", "import PEqualNP.W951.AsteroidCheap",
        f"/-! Generated by asteroid/asteroid.py. The claims of `{mod}` in the project's own definitions. Do not edit. -/",
        "namespace SearchCheck", "open PEqualNP.CircuitLowerBounds (Circuit GateOp)",
        "open PEqualNP.Outside.L_meta_951_aux (F2 baseDQ MUF2 slack Phi Phi_zero)", f"open {mod}", f"namespace {mod}_sound"], [], set()
    for t, (c, kind, stmt, text) in zip(names, lean_claims):
        if FORCE_SEEN.get(t): continue
        need_ok = stmt.startswith("slackNonnegAll") or stmt == f"slackGe {c} 0 (0) = true"
        if need_ok and c not in done_ok:
            done_ok.add(c); out.append(f"theorem {c}_setsOk : Circ.SetsOk {c} := by unfold Circ.SetsOk; decide")
        if stmt == f"correctB {c} = true":
            n = f"{t}_project"; made.append(n)
            out.append(f"/-- `{text}`: the project's `Circuit.eval` computes the OR of every set. -/\ntheorem {n} (w_ : Fin {c}.sets.length) (x_ : Fin {c}.n → Bool) :\n    Circuit.eval ⟨{c}.toGates, {c}.outs.getD w_ 0⟩ (List.ofFn x_) = decide (∃ v_ ∈ {c}.setFin w_, x_ v_ = true) :=\n  correctB_sound_project {c} {t} (by decide) w_ x_")
        elif stmt.startswith("slackNonnegAll"):
            n = f"{t}_project"; made.append(n)
            out.append(f"/-- `{text}`: base ≤ |F2| at every cube, in the project's definitions. -/\ntheorem {n} (Q_ : Finset (Fin {c}.n)) :\n    baseDQ {c}.setFin ∅ Q_ ≤ (F2 {c}.toGates {c}.setFin Q_).card :=\n  slackNonnegAll_sound {c} {c}_setsOk {t} Q_")
        if stmt.startswith("slackNonnegAll"):
            n2 = f"{t}_phi"; made.append(n2)
            out.append(f"/-- the continuous form: the expected slack Φ(p) is nonnegative on [0, 1], in the project's `Phi`. -/\ntheorem {n2} (p_ : ℝ) (h0_ : 0 ≤ p_) (h1_ : p_ ≤ 1) : 0 ≤ Phi {c}.toGates {c}.setFin p_ :=\n  Phi_nonneg_of_slackNonnegAll {c} {c}_setsOk {t} h0_ h1_")
            n3 = f"{t}_phi_zero"; made.append(n3)
            out.append(f"/-- the line the remaining `sorry` asks for, for THIS circuit: 0 ≤ Φ(0). -/\ntheorem {n3} : 0 ≤ Phi {c}.toGates {c}.setFin 0 :=\n  Phi_nonneg_of_slackNonnegAll {c} {c}_setsOk {t} le_rfl zero_le_one")
        elif stmt == f"slackGe {c} 0 (0) = true":
            n = f"{t}_project"; made.append(n)
            out.append(f"/-- `{text}`: the sum of (|S| − 1) is at most the number of gates of this circuit. -/\ntheorem {n} : ∑ w_, (({c}.setFin w_).card - 1) ≤ {c}.toGates.length :=\n  base_le_gates_of_slackGe {c} {c}_setsOk {t}")
    if not made: return None
    out.append(f"end {mod}_sound"); out.append("end SearchCheck"); smod = mod + "_sound"; path = f"one-not/lean/PEqualNP/W951/{smod}.lean"
    open(path, "w", encoding="utf-8", newline="\n").write("\n".join(out) + "\n"); t0 = time.time()
    r = subprocess.run([lake(), "build", f"PEqualNP.W951.{smod}"], cwd=LEAN_DIR, env=envp, capture_output=True, text=True, encoding="utf-8", errors="replace")
    if r.returncode != 0: print("\n".join(l for l in (r.stdout + r.stderr).splitlines() if "error" in l)[:1500])
    return {"module": path, "ok": r.returncode == 0, "seconds": round(time.time() - t0, 1), "theorems": made}

def plot_phi(names, out):
    need("numpy", "plot"); matplotlib = need("matplotlib", "plot"); import continuous as C
    matplotlib.use("Agg"); import matplotlib.pyplot as plt
    ps = [i / 200 for i in range(201)]; fig, ax = plt.subplots(1, 2, figsize=(12, 4.6))
    for nme in names:
        c = env[nme]; n = c["n"]; m = C.level_means(C.slack_table(c, 0, any_gate=core.nots(c) > 1), n)
        ax[0].plot(ps, [C.bern_eval(m, p) for p in ps], label=f"{nme} (n={n})"); ax[1].plot(range(n + 1), m, marker="o", ms=3, label=nme)
    for a in ax: a.axhline(0, color="k", lw=0.8)
    ax[0].set_xlabel("p"); ax[0].set_ylabel("Phi(p) = expected slack"); ax[1].set_xlabel("points set to 1"); ax[1].set_ylabel("mean slack")
    ax[0].legend(fontsize=7); fig.tight_layout(); fig.savefig(out, dpi=150)

NO_LEAN = False
SHOW_LEAN = False
FORCE = False
FORCE_SEEN = {}
SKIPPED = []     # lines skipped because numpy or matplotlib is not installed
RUNNERS = []     # repo check commands that passed in this run (ext_finite); a record carries them as its runner
EXTRA_LEAN = {"imports": [], "decls": []}   # extensions may add Lean imports and declarations to the generated module
def reset():
    """Forget every name and claim: a fresh run in the same process (the window's Run button)."""
    for d in (env, src, CONJ, FORCE_SEEN): d.clear()
    for l in (lean_claims, results, SKIPPED, RUNNERS): l.clear()

class Session:
    """The state of one run: the open `circuit ... end` block and the `record` lines. A file run makes one; the interactive prompt keeps one."""
    def __init__(self): self.block = None; self.records = []

def say(text=""):
    """Every line a program prints goes through here, so colours and the interactive prompt (ui.py) can sit on top."""
    try: from asteroid import ui; text = ui.paint(str(text))
    except ImportError: pass
    print(text)

def exec_line(st, raw, ln, script):
    """Run ONE line against the persistent environment. `run` calls this for each line of a file; the prompt for each line typed."""
    line = raw.split("#", 1)[0].strip()
    if not line: return
    API.update({"env": env, "src": src, "lean_claims": lean_claims, "results": results, "core": core, "F": F, "ln": ln, "script": script, "extra_lean": EXTRA_LEAN})
    try:
        if st.block is not None:
            name, n, wires, gates, sets, outs = st.block
            W = lambda x: int(x) if x.isdigit() else wires[x]
            if line == "end":
                env[name] = {"n": n, "sets": sets, "gates": gates, "outs": outs}; st.block = None
                say(f"{ln}: {name} defined ({n} inputs, {len(gates)} gates, correct {core.correct(env[name])})"); return
            if m := re.fullmatch(r"(\w+) = (or|and) (\w+) (\w+)", line): gates.append([m.group(2), W(m.group(3)), W(m.group(4))]); wires[m.group(1)] = n + len(gates) - 1
            elif m := re.fullmatch(r"(\w+) = not (\w+)", line): gates.append(["not", W(m.group(2))]); wires[m.group(1)] = n + len(gates) - 1
            elif m := re.fullmatch(r"set ([\d ]+) -> (\w+)", line): sets.append([int(x) for x in m.group(1).split()]); outs.append(W(m.group(2)))
            else: raise SystemExit(f"{script}:{ln}: cannot parse inside circuit: {line}")
            return
        if m := re.fullmatch(r"circuit (\w+) (\d+)", line): check_name(m.group(1), f"{script}:{ln}"); st.block = (m.group(1), int(m.group(2)), {}, [], [], []); return
        if m := re.fullmatch(r"let (\w+) = load (.+\.json[\"']?)", line):
            check_name(m.group(1), f"{script}:{ln}")
            f = in_path(m.group(2)); d = json.load(open(f, encoding="utf-8")); env[m.group(1)] = {k: d[k] for k in ("n", "sets", "gates", "outs")}; src[m.group(1)] = f
            say(f"{ln}: {m.group(1)} loaded ({d['n']} inputs, {len(d['gates'])} gates)")
        elif m := re.fullmatch(r"show (\w+)", line):
            a = m.group(1); say(f"{ln}: {a}: " + ", ".join(f"{f} {F(f, a)}" for f in ("gates", "nots", "base", "witness", "orwitness", "correct")))
        elif not re.match(r"claim!? forall c in ", line) and (m := re.fullmatch(r"claim(!?) (.+)", line)):
            global FORCE
            FORCE = bool(m.group(1)); body, lean = _by_lean(m.group(2))   # no regex here: `.+?\s+` is quadratic on long lines
            ok, detail = do_claim(body, lean)
            results.append((ln, body, ok, lean)); say(f"{ln}: claim {body}: python {'TRUE' if ok else 'FALSE'} ({detail})")
        elif m := re.fullmatch(r"plot phi (.+?) -> (.+)", line):
            o = out_path(m.group(2)); plot_phi(m.group(1).split(), o); say(f"{ln}: wrote {o}")
        elif m := re.fullmatch(r"conjecture (\w+):\s*(.+)", line):
            CONJ[m.group(1)] = m.group(2).strip(); say(f"{ln}: conjecture {m.group(1)}(c) := {m.group(2).strip()}")
        elif (m := re.fullmatch(r"hunt (\w+) (\d+) (\d+)(?: (\d+))?", line)) and m.group(1) in CONJ:
            say(f"{ln}: " + hunt_conjecture(m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4) or 0)))
        elif m := re.fullmatch(r'hunt "([^"]+)" (\d+) (\d+)(?: (\d+))?(\s*&)?', line):
            cmd = [sys.executable, "-I", "-X", "utf8", "one-not/tools/search/hunt.py", m.group(1), m.group(2), m.group(3), m.group(4) or "0"]
            if m.group(5):
                log = f"asteroid/out/hunt_{int(time.time())}.log"; detach = {"creationflags": subprocess.CREATE_NEW_PROCESS_GROUP | subprocess.DETACHED_PROCESS} if os.name == "nt" else {"start_new_session": True}
                subprocess.Popen(cmd, stdout=open(log, "wb"), stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, **detach)
                say(f"{ln}: hunt started in the background, log {log}")
            else: say(f"{ln}: " + subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace").stdout.strip().splitlines()[-1])
        elif m := re.fullmatch(r'record (\S+) (\S+) ([\w-]+) "(.+)"', line): st.records.append(m.groups())
        else:
            import glob, importlib
            api = API; api.update({"env": env, "src": src, "lean_claims": lean_claims, "results": results, "core": core, "F": F, "ln": ln, "script": script, "extra_lean": EXTRA_LEAN})
            for f in sorted(glob.glob(os.path.join(ROOT, "asteroid", "ext_*.py"))):
                if importlib.import_module("asteroid." + os.path.basename(f)[:-3]).handle(line, api): break
            else: raise SystemExit(f"{script}:{ln}: cannot parse: {line}")
    except ImportError as e:               # numpy or matplotlib missing: skip this line, keep going
        mod = (getattr(e, "name", None) or "").split(".")[0]
        if mod not in ("numpy", "matplotlib"): raise
        SKIPPED.append(ln); say(f"{ln}: " + getattr(e, "asteroid", f"{line.split()[0]} needs {mod}: run bin/setup") + "  (line skipped)")

def _by_lean(t):
    """Split a trailing `by lean` off a claim body (the old regex `(.+?)(\\s+by lean)?`, in linear time)."""
    t = t.strip()
    if t.endswith("by lean") and len(t) > 7 and t[-8].isspace(): return t[:-7].strip(), True
    return t, False

NEST_DEPTH, NEST_RUNS = 3, 64   # child runs (frame files, check, seq run) nest at most 3 deep and number at most 64 per top run
def child_env(where):
    """The environment for one child run. Refuses past the depth or the count limit, so a loop of files or of checks halts."""
    import tempfile, atexit
    depth = int(os.environ.get("ASTEROID_NEST_DEPTH", "0") or 0)
    if depth >= NEST_DEPTH: raise SystemExit(f"{where}: runs nest more than {NEST_DEPTH} deep (a loop?)")
    f = os.environ.get("ASTEROID_NEST_RUNS")
    if not f or not os.path.isfile(f):
        fd, f = tempfile.mkstemp(prefix="asteroid_runs_"); os.close(fd); os.environ["ASTEROID_NEST_RUNS"] = f
        atexit.register(lambda: os.path.exists(f) and os.remove(f))
    with open(f, "a") as fh: fh.write("x")
    if os.path.getsize(f) > NEST_RUNS: raise SystemExit(f"{where}: more than {NEST_RUNS} child runs in one top run")
    return dict(os.environ, ASTEROID_NEST_DEPTH=str(depth + 1), ASTEROID_NEST_RUNS=f)

def run(script):
    global PROG_DIR
    if not os.path.isfile(script): raise SystemExit(f"asteroid: no such program: {os.path.abspath(script)}")
    PROG_DIR = os.path.dirname(os.path.abspath(script))
    st = Session()
    for ln, raw in enumerate(open(script, encoding="utf-8"), 1): exec_line(st, raw, ln, script)
    records = st.records
    L = None if NO_LEAN else build_lean(script)
    if NO_LEAN and lean_claims: say(f"not proved: {len(lean_claims)} claims were only evaluated (no proof checker in this run)")
    if L:
        if L["ok"]: say(f"proved: {len(L['theorems'])} claims accepted by the proof checker in {L['seconds']} s")
        else: say(f"NOT PROVED: the proof checker rejected this program's claims ({L['seconds']} s)")
        if SHOW_LEAN: say(f"  lean module {L['module']}; axioms: {L['axioms']}")
    if L and L.get("sound"):
        Sd = L["sound"]
        say((f"proved: {len(Sd['theorems'])} of them also hold in the project's own definitions" if Sd["ok"] else "NOT PROVED: the restatement in the project's own definitions failed") + f" ({Sd['seconds']} s)")
        if SHOW_LEAN: say(f"  lean module {Sd['module']}")
    bad = [r for r in results if not r[2]]
    for d, item, word, stmt in records:
        if bad or (word == "checked" and not (L and L["ok"])): say(f"record skipped ({stmt[:40]}...): a claim failed or Lean did not build"); continue
        if not results: say(f"record skipped ({stmt[:40]}...): the program has no claim, so nothing supports it"); continue
        if word not in ("checked", "checked-finite", "tested", "refuted", "open", "premise", "paper"):
            say(f"record skipped ({stmt[:40]}...): {word} is not a word a run can give (checked-infinite needs a reduction)"); continue
        import boards
        if os.path.isfile(os.path.join(d, "findings.jsonl")) and any(r.get("statement") == stmt for r in boards.load(d)): say(f"record kept ({stmt[:40]}...): already in {d}/findings.jsonl"); continue
        ev = [script] + ([f"{L['module']}::{L['theorems'][-1]}"] if L and L["ok"] else []) + list(dict.fromkeys(src.values()))
        boards.add(d, "asteroid", item, word, stmt, ev, runner=" && ".join(dict.fromkeys(RUNNERS)) or "bin/asteroid --no-lean " + os.path.relpath(script, ROOT)); boards.build()
    say(f"claims: {len(results) - len(bad)} true, {len(bad)} false" + (f"; {len(L['theorems'])} proved" if L and L["ok"] else "")
          + (f"; {len(SKIPPED)} lines skipped (numpy or matplotlib missing: run bin/setup)" if SKIPPED else ""))
    return 1 if bad or (L and not L["ok"]) or (L and L.get("sound") and not L["sound"]["ok"]) else 0

VERSION = "asteroid 0.3 (Python + Lean kernel + matplotlib)"
def doctor():
    """What this machine has, and what a run will do. Changes nothing."""
    import platform, importlib.util
    venv = os.path.join(ROOT, ".venv"); inside = os.path.realpath(sys.prefix) == os.path.realpath(venv)
    print(VERSION); print(f"repository   {ROOT}")
    print(f"system       {platform.system()} {platform.release()} ({platform.machine()})")
    ms = os.environ.get("MSYSTEM")
    print("shell        " + (f"Git Bash / MSYS ({ms})" if ms else "PowerShell or cmd" if os.name == "nt" else os.environ.get("SHELL", "unknown")))
    print(f"python       {platform.python_version()}  {sys.executable}")
    print("             " + ("this is the repository's own .venv" if inside else
          "this is NOT the repository's .venv (" + ("there is one, but the launcher did not use it" if os.path.isdir(venv) else "none yet: bin/setup makes it") + ")"))
    have = {}
    for mod in ("numpy", "matplotlib"):
        try: spec = importlib.util.find_spec(mod)
        except Exception: spec = None
        have[mod] = spec is not None
        try:
            from importlib import metadata; ver = metadata.version(mod) if spec else ""
        except Exception: ver = ""
        print(f"{mod:<12} " + (f"present {ver}  {os.path.dirname(spec.origin or '')}" if spec else "MISSING: run bin/setup"))
    lk = lake(); cache = mathlib_cache()
    print("lake (Lean)  " + (lk or "NOT FOUND (looked on PATH and in ~/.elan/bin). Install elan: https://lean-lang.org/install/"))
    print("Mathlib      " + ("cache present in one-not/lean/.lake" if cache else "NO CACHE in one-not/lean/.lake: run `lake exe cache get` in one-not/lean (needs lake)"))
    print("a run will   " + ("PROVE: `by lean` claims go to the proof checker" if lk and cache else
          "PROVE, but SLOWLY: without the Mathlib cache the first proof compiles Mathlib (hours). Get the cache first, or use --no-lean" if lk else
          "EVALUATE ONLY: no Lean here, so claims are computed in Python and nothing is proved"))
    miss = [m for m in have if not have[m]]
    print("             " + ("plots and the continuous and mixed lines work" if not miss else
          f"without {' and '.join(miss)}: " + ("plot lines are skipped; " if not have["matplotlib"] or not have["numpy"] else "")
          + ("continuous, mixed, bernstein, phi and corpus lines are skipped; " if not have["numpy"] else "") + "everything else runs"))
    return 0

def main(argv):
    global NO_LEAN, SHOW_LEAN
    for st in (sys.stdout, sys.stderr):                 # Windows consoles and pipes: always UTF-8, never a crash on a symbol
        try: st.reconfigure(encoding="utf-8", errors="replace")
        except Exception: pass
    os.makedirs(os.path.join(ROOT, "asteroid", "out"), exist_ok=True)
    if "--doctor" in argv or argv[:1] == ["doctor"]: return doctor()
    if argv[:1] == ["run-cpu"]:                         # the 4-bit CPU of cpu/: Python only, no Lean
        from asteroid import cpu; os.chdir(CALLER_DIR); return cpu.main(argv[1:], ROOT)
    NO_LEAN = any(a in argv for a in ("--no-lean", "--no-proof")); SHOW_LEAN = "--show-lean" in argv   # --no-proof: the same flag, quiet alias
    from asteroid import ui; ui.setup(no_color="--no-color" in argv)
    argv = [a for a in argv if a not in ("--no-lean", "--no-proof", "--show-lean", "--no-color")]
    if argv[:1] in (["--version"], ["-V"]): argv = ["version"]
    if argv[:1] == ["--doctor"]: argv = ["doctor"]
    def prog(a):                                        # a program path is read from where the command was typed
        if not a.endswith((".ath", ".ast")): return a
        p = os.path.normpath(os.path.join(CALLER_DIR, a))
        try: p = os.path.relpath(p, ROOT)
        except ValueError: pass                         # Windows, another drive: keep the full path
        return p.replace(os.sep, "/")
    argv = [prog(a) for a in argv]
    prompt = not argv or argv[:1] == ["repl"]
    if not NO_LEAN and not lake() and not prompt:
        NO_LEAN = True
        print("note: Lean (the command `lake`) is not installed here, so this run is Python only: claims are evaluated, nothing is formally checked.\n      To let the Lean kernel decide: install elan, then `cd one-not/lean && lake exe cache get`.")
    if argv[:1] == ["version"]: print(VERSION); return 0
    if prompt: from asteroid import repl; return repl.main()
    if argv[:1] == ["idle"]: from asteroid import idle; return idle.main(argv[1:])
    if argv[:1] == ["setup"]: print("asteroid: `setup` is run by the launcher: bin/asteroid setup (or bin/setup)"); return 2
    if argv[:1] == ["demo"]:
        print("asteroid demo: the program is asteroid/demo.ath (a 4-input circuit, three true claims, one false on purpose)\n")
        run("asteroid/demo.ath"); good = [r[2] for r in results] == [True, True, True, False]
        print("\n" + ("demo OK: three claims TRUE and the last one FALSE, as written." if good else "demo FAILED: expected three TRUE claims and one FALSE.")
              + ("" if not NO_LEAN else "\nNothing was proved in this run (no Lean here, or --no-lean): the claims were computed in Python."))
        print("Try next:\n  bin/asteroid hello.ath     a program that loads a circuit file and draws a plot\n  bin/asteroid --doctor      what this machine has\n  bin/setup                  once, for plots: numpy and matplotlib in a .venv inside this folder")
        return 0 if good else 1
    if argv[:1] == ["run"] and len(argv) == 2: return run(argv[1])
    if argv[:1] == ["test"]:
        import glob; bad = 0
        for f in sorted(glob.glob("asteroid/examples/*.ath") + glob.glob("asteroid/programs/*.ath")):
            f = f.replace(os.sep, "/")
            r = subprocess.run([sys.executable, "-X", "utf8", os.path.join(ROOT, "asteroid", "__main__.py"), "run", f] + (["--no-lean"] if NO_LEAN else []), cwd=ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace")
            last = (r.stdout.strip().splitlines() or (r.stderr.strip().splitlines() or ["(no output)"])[-1:])[-1]
            print(("ok   " if r.returncode == 0 else "FAIL ") + f + "  |  " + last); bad += r.returncode != 0
        return 1 if bad else 0
    if len(argv) == 1 and argv[0].endswith((".ath", ".ast")): return run(argv[0])   # .ast: the old extension, still read
    print(__doc__); return 2

if __name__ == "__main__": sys.exit(main(sys.argv[1:]))
