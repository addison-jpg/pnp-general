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
  conjecture NAME: EXPR                      EXPR with the circuit variable c; then NAME(X) is a claim expression
  hunt NAME SECONDS MAXNOT [SEED]            search for a circuit where the conjecture NAME fails; binds NAME_cex
  hunt "CONJECTURE" SECONDS MAXNOT [SEED] [&]   mutation search; `&` runs it in the background, log in asteroid/out/
  (extensions)                               a file asteroid/ext_NAME.py with `handle(line, api) -> bool` adds verbs
  record DIR ITEM WORD "STATEMENT"           a finding (boards.py) citing this script and, if built, its Lean module

Run from anywhere (after `pip install -e .` in the repository; or `python3 -m asteroid …` from its root):
  asteroid FILE.ast                 run one program (also: asteroid run FILE.ast)
  asteroid test                     run every program under asteroid/examples and asteroid/programs
  asteroid version
  --no-lean                         evaluate only, prove nothing. Chosen automatically when Lean is not installed.
  --show-lean                       also print the generated Lean files and the axioms used
Python proposes, Lean decides: a `by lean` claim counts only if the generated module builds."""
import sys, os, re, json, subprocess, shlex, operator, time
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

RESERVED = ['Bool', 'Circ', 'F2_chain_sum', 'Fin', 'Gate', 'Int', 'LMeta951Stmt', 'List', 'MUF2_of_slackGe', 'MUF2_of_slackNonnegAll', 'Nat', 'Phi_nonneg_of_slackNonnegAll', 'Prop', 'Q', 'Type', 'aliveMixed', 'alive_iff', 'allStates', 'anyPair', 'any_testBit_ofBits', 'at', 'atMostOneNot_of_notCount', 'baseAt', 'baseAt_eq_baseDQ', 'baseMixed', 'baseMixed_zero', 'base_le_gates_of_LMeta951Stmt', 'base_le_gates_of_no_minCE', 'base_le_gates_of_slackGe', 'bitStep_testBit_succ', 'bitStep_testBit_zero', 'by', 'c', 'card_F2_eq_orWitnessAt', 'card_setFin', 'cellAt', 'correctB', 'correctB_sound', 'correctB_sound_project', 'def', 'do', 'else', 'end', 'exists_minCE_of_hunt_hit', 'exists_two_of_filter', 'false', 'first_ast_fano_hypsB', 'first_ast_tiny_concrete', 'first_ast_tiny_correct', 'first_ast_tiny_kstep', 'first_ast_tiny_setsOk', 'first_ast_tiny_slack', 'foldl_add_eq_sum', 'foldl_filter_ge_two', 'foldl_lor_testBit', 'foldl_snoc_length', 'foldl_ttStep_map', 'foldr_bits_testBit', 'from', 'full_testBit', 'fun', 'gateVal', 'gateVal_eq_eval', 'getD_map_testBit', 'hasWitness', 'hasWitnessAt', 'hasWitnessAt_iff', 'hasWitnessAt_iff_F2Wit', 'hasWitnessMixed', 'hasWitnessMixedNaive', 'hasWitnessMixedNaive_zero', 'have', 'hypsB', 'hypsB_sound', 'if', 'import', 'in', 'ins_getD_testBit', 'inter_card_le', 'iota_of_notCount', 'isCE_of_checks', 'isOrAt_toGates', 'lMeta951Stmt_of_L_meta_951', 'land_testBit', 'let', 'lor_testBit', 'maskOf', 'maskOf_empty', 'mem_setFin', 'mixPre', 'mixedStepAll', 'mixedStepAllWith', 'mslackGe', 'mslackGe_zero', 'mslackLe', 'mslackNonnegAll', 'mslackNonnegAllWith', 'mslackVal', 'mslackValWith', 'mslackVal_zero', 'naiveAgrees', 'namespace', 'notCount', 'not_LMeta951Stmt_of_hunt_hit', 'not_isCE_of_slackGe', 'not_minCE_of_slackGe', 'ofBits_rowOf', 'ofFn_eq_range_testBit', 'open', 'orTables', 'orWitnessAt', 'orWitnessAtWith', 'orWitnessAt_chain_sum', 'orWitnessAt_eq', 'or_two_pow_lt', 'p', 'payingStepAt', 'rowOf', 'rowOf_ofBits', 'rowOf_or', 'setsOkB', 'setsOk_of_setsOkB', 'show', 'slackGe', 'slackGe_sound', 'slackLe', 'slackNonnegAll', 'slackNonnegAllWith', 'slackNonnegAll_sound', 'slack_eq_asteroid', 'slack_nonneg_of_slackNonnegAll', 'sum_filter_map', 'sum_fin_getElem', 't4', 't4_below_base', 't4_correct', 't4_witness', 'table_val', 'tables_length', 'tables_map_testBit', 'tables_testBit', 'testBit_eq_false_of_ge', 'testBit_maskOf', 'then', 'theorem', 'toGate_not_iff', 'toGate_or_iff', 'toGates_wf', 'true', 'tt', 'ttStep', 'ttStep_testBit', 'tt_eq', 'tt_foldl_toList', 'two_le_filter', 'varTT', 'varTT_testBit', 'varTT_testBit_gen', 'w', 'wiresAt_eq_wires', 'wiresFrom', 'wiresFrom_eq_wires', 'witnessCount', 'witnessMixedWith', 'witnessTable', 'x', 'xor_testBit']
def check_name(name, where):
    if name in RESERVED: raise SystemExit(f"{where}: the name `{name}` is taken by the proof library; pick another name for this circuit")

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
                env[name + "_cex"] = new; p = f"asteroid/out/{name}_cex.json"; json.dump(new, open(p, "w")); src[name + "_cex"] = p
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
    open(path, "w").write("\n".join(out) + "\n")
    local = "/home/user/pequalnp-proofs/tools/bin"
    envp = dict(os.environ, PATH=(local + ":" if os.path.isdir(local) else "") + os.environ["PATH"]); t0 = time.time()
    r = subprocess.run(["lake", "build", f"PEqualNP.W951.{mod}"], cwd="one-not/lean", env=envp, capture_output=True, text=True)
    ok = r.returncode == 0
    ax = ""
    if ok:
        tmp = os.path.join(ROOT, f"asteroid/out/_axioms_{os.getpid()}.lean")
        open(tmp, "w").write(f"import PEqualNP.W951.{mod}\n" + "".join(f"#print axioms SearchCheck.{mod}.{t}\n" for t in names))
        a = subprocess.run(["lake", "env", "lean", tmp], cwd="one-not/lean", env=envp, capture_output=True, text=True).stdout
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
    open(path, "w").write("\n".join(out) + "\n"); t0 = time.time()
    r = subprocess.run(["lake", "build", f"PEqualNP.W951.{smod}"], cwd="one-not/lean", env=envp, capture_output=True, text=True)
    if r.returncode != 0: print("\n".join(l for l in (r.stdout + r.stderr).splitlines() if "error" in l)[:1500])
    return {"module": path, "ok": r.returncode == 0, "seconds": round(time.time() - t0, 1), "theorems": made}

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
SHOW_LEAN = False
FORCE = False
FORCE_SEEN = {}
EXTRA_LEAN = {"imports": [], "decls": []}   # extensions may add Lean imports and declarations to the generated module
def run(script):
    records = []
    block = None
    for ln, raw in enumerate(open(script), 1):
        line = raw.split("#", 1)[0].strip()
        if not line: continue
        API.update({"env": env, "src": src, "lean_claims": lean_claims, "results": results, "core": core, "F": F, "ln": ln, "script": script, "extra_lean": EXTRA_LEAN})
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
        if m := re.fullmatch(r"circuit (\w+) (\d+)", line): check_name(m.group(1), f"{script}:{ln}"); block = (m.group(1), int(m.group(2)), {}, [], [], []); continue
        if m := re.fullmatch(r"let (\w+) = load (\S+)", line):
            check_name(m.group(1), f"{script}:{ln}")
            d = json.load(open(m.group(2))); env[m.group(1)] = {k: d[k] for k in ("n", "sets", "gates", "outs")}; src[m.group(1)] = m.group(2)
            print(f"{ln}: {m.group(1)} loaded ({d['n']} inputs, {len(d['gates'])} gates)")
        elif m := re.fullmatch(r"show (\w+)", line):
            a = m.group(1); print(f"{ln}: {a}: " + ", ".join(f"{f} {F(f, a)}" for f in ("gates", "nots", "base", "witness", "orwitness", "correct")))
        elif not re.match(r"claim!? forall c in ", line) and (m := re.fullmatch(r"claim(!?) (.+?)(\s+by lean)?", line)):
            global FORCE
            FORCE = bool(m.group(1)); m = re.fullmatch(r"claim!? (.+?)(\s+by lean)?", line)
            ok, detail = do_claim(m.group(1).strip(), bool(m.group(2)))
            results.append((ln, m.group(1).strip(), ok, bool(m.group(2)))); print(f"{ln}: claim {m.group(1).strip()}: python {'TRUE' if ok else 'FALSE'} ({detail})")
        elif m := re.fullmatch(r"plot phi (.+?) -> (\S+)", line):
            plot_phi(m.group(1).split(), m.group(2)); print(f"{ln}: wrote {m.group(2)}")
        elif m := re.fullmatch(r"conjecture (\w+):\s*(.+)", line):
            CONJ[m.group(1)] = m.group(2).strip(); print(f"{ln}: conjecture {m.group(1)}(c) := {m.group(2).strip()}")
        elif (m := re.fullmatch(r"hunt (\w+) (\d+) (\d+)(?: (\d+))?", line)) and m.group(1) in CONJ:
            print(f"{ln}: " + hunt_conjecture(m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4) or 0)))
        elif m := re.fullmatch(r'hunt "([^"]+)" (\d+) (\d+)(?: (\d+))?(\s*&)?', line):
            cmd = [sys.executable, "-I", "one-not/tools/search/hunt.py", m.group(1), m.group(2), m.group(3), m.group(4) or "0"]
            if m.group(5):
                log = f"asteroid/out/hunt_{int(time.time())}.log"; subprocess.Popen(cmd, stdout=open(log, "w"), stderr=subprocess.STDOUT, start_new_session=True)
                print(f"{ln}: hunt started in the background, log {log}")
            else: print(f"{ln}: " + subprocess.run(cmd, capture_output=True, text=True).stdout.strip().splitlines()[-1])
        elif m := re.fullmatch(r'record (\S+) (\S+) (\w+) "(.+)"', line): records.append(m.groups())
        else:
            import glob, importlib
            api = API; api.update({"env": env, "src": src, "lean_claims": lean_claims, "results": results, "core": core, "F": F, "ln": ln, "script": script, "extra_lean": EXTRA_LEAN})
            for f in sorted(glob.glob(os.path.join(ROOT, "asteroid", "ext_*.py"))):
                if importlib.import_module("asteroid." + os.path.basename(f)[:-3]).handle(line, api): break
            else: raise SystemExit(f"{script}:{ln}: cannot parse: {line}")
    L = None if NO_LEAN else build_lean(script)
    if NO_LEAN and lean_claims: print(f"not proved: {len(lean_claims)} claims were only evaluated (no proof checker in this run)")
    if L:
        if L["ok"]: print(f"proved: {len(L['theorems'])} claims accepted by the proof checker in {L['seconds']} s")
        else: print(f"NOT PROVED: the proof checker rejected this program's claims ({L['seconds']} s)")
        if SHOW_LEAN: print(f"  lean module {L['module']}; axioms: {L['axioms']}")
    if L and L.get("sound"):
        Sd = L["sound"]
        print((f"proved: {len(Sd['theorems'])} of them also hold in the project's own definitions" if Sd["ok"] else "NOT PROVED: the restatement in the project's own definitions failed") + f" ({Sd['seconds']} s)")
        if SHOW_LEAN: print(f"  lean module {Sd['module']}")
    bad = [r for r in results if not r[2]]
    for d, item, word, stmt in records:
        if bad or (word == "checked" and not (L and L["ok"])): print(f"record skipped ({stmt[:40]}...): a claim failed or Lean did not build"); continue
        import boards
        ev = [script] + ([f"{L['module']}::{L['theorems'][-1]}"] if L and L["ok"] else []) + list(dict.fromkeys(src.values()))
        boards.add(d, "asteroid", item, word, stmt, ev); boards.build()
    print(f"claims: {len(results) - len(bad)} true, {len(bad)} false" + (f"; {len(L['theorems'])} proved" if L and L["ok"] else ""))
    return 1 if bad or (L and not L["ok"]) or (L and L.get("sound") and not L["sound"]["ok"]) else 0

VERSION = "asteroid 0.3 (Python + Lean kernel + matplotlib)"
def main(argv):
    global NO_LEAN, SHOW_LEAN
    NO_LEAN = "--no-lean" in argv; SHOW_LEAN = "--show-lean" in argv; argv = [a for a in argv if a not in ("--no-lean", "--show-lean")]
    # a program path is read from where the command was typed
    argv = [os.path.relpath(os.path.join(CALLER_DIR, a), ROOT) if a.endswith(".ast") and not os.path.isabs(a) else a for a in argv]
    import shutil
    local = "/home/user/pequalnp-proofs/tools/bin"
    if not NO_LEAN and not shutil.which("lake", path=(local + ":" if os.path.isdir(local) else "") + os.environ.get("PATH", "")):
        NO_LEAN = True
        print("note: Lean (the command `lake`) is not installed here, so this run is Python only: claims are evaluated, nothing is formally checked.\n      To let the Lean kernel decide: install elan, then `cd one-not/lean && lake exe cache get`.")
    if argv[:1] == ["version"]: print(VERSION); return 0
    if argv[:1] == ["run"] and len(argv) == 2: return run(argv[1])
    if argv[:1] == ["test"]:
        import glob; bad = 0
        for f in sorted(glob.glob("asteroid/examples/*.ast") + glob.glob("asteroid/programs/*.ast")):
            r = subprocess.run([sys.executable, "-m", "asteroid", "run", f] + (["--no-lean"] if NO_LEAN else []), capture_output=True, text=True)
            print(("ok   " if r.returncode == 0 else "FAIL ") + f + "  |  " + (r.stdout.strip().splitlines() or ["(no output)"])[-1]); bad += r.returncode != 0
        return 1 if bad else 0
    if len(argv) == 1 and argv[0].endswith(".ast"): return run(argv[0])
    print(__doc__); return 2

if __name__ == "__main__": sys.exit(main(sys.argv[1:]))
