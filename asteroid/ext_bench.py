"""asteroid extension: circuits as ISCAS `.bench` files. The grammar is asteroid/BENCH.md.

  let NAME = load FILE.bench        read a circuit
  save NAME -> FILE.bench           write a circuit (inputs x0 x1 ..., gates g0 g1 ...)

This is the same reader as the Lean module one-not/lean/PEqualNP/AsteroidLang/Bench.lean, function for
function: parse, print_netlist, to_circ, of_circ. A netlist is a dict
{"name": str, "inputs": [str], "outputs": [str], "gates": [[signal, OP, [operand]]], "ors": [[output, [input]]]}.

As a command, it converts JSON circuits and writes the `.bench` file next to each:
  python3 -I asteroid/ext_bench.py FILE.json ...
"""
import re, json, os, sys

IDENT = re.compile(r"[A-Za-z0-9_.\[\]]+")
PUNCTUATION = ["(", ")", ",", "="]


class BenchError(Exception):
    """An error in a `.bench` file. `signal` is the signal whose assignment line is at fault."""
    def __init__(self, msg, signal=None):
        super().__init__(msg); self.msg, self.signal = msg, signal


def is_ident(s): return bool(IDENT.fullmatch(s))


def words(marks, s):
    for m in marks: s = s.replace(m, f" {m} ")
    return [w for w in re.split(r"[ \t\r\n]", s) if w]


def show_gate(g): return f"{g[0]} = {g[1]}({', '.join(g[2])})"


def parse_args(toks):
    if len(toks) == 2 and toks[1] == ")":
        if is_ident(toks[0]): return [toks[0]]
        raise BenchError("expected a signal name before ')'")
    if len(toks) >= 2 and toks[1] == ",":
        if is_ident(toks[0]): return [toks[0]] + parse_args(toks[2:])
        raise BenchError("expected a signal name before ','")
    raise BenchError("expected operands 'NAME, NAME, ...' and a closing ')'")


def parse_line(line):
    """One line to ("blank",) | ("comment", text) | ("input", x) | ("output", x) | ("gate", x, OP, args) | ("or", out, ins)."""
    t = line.strip(" \t\r\n")
    if t.startswith("#@"):
        w = words(["="], t[2:])
        if len(w) >= 3 and w[0] == "or" and w[2] == "=":
            out, ins = w[1], w[3:]
            if not is_ident(out): raise BenchError(f"directive '#@ or': '{out}' is not a signal name")
            if not ins: raise BenchError("directive '#@ or': no inputs after '='")
            for x in ins:
                if not is_ident(x): raise BenchError(f"directive '#@ or': '{x}' is not a signal name")
            return ("or", out, ins)
        if w and w[0] == "or": raise BenchError("directive '#@ or': expected '#@ or OUTPUT = INPUT INPUT ...'")
        if w: raise BenchError(f"unknown directive '#@ {w[0]}' (the only directive is '#@ or')")
        raise BenchError("empty directive '#@'")
    if t.startswith("#"): return ("comment", t[1:].strip(" \t\r\n"))
    code = t.split("#")[0].strip(" \t\r\n")
    if not code: return ("blank",)
    toks = words(PUNCTUATION, code)
    for tok in toks:
        if tok not in PUNCTUATION and not is_ident(tok): raise BenchError(f"unexpected character in '{tok}'")
    if len(toks) == 4 and toks[1] == "(" and toks[3] == ")":
        kw, x = toks[0], toks[2]
        if not is_ident(x): raise BenchError("expected a signal name between '(' and ')'")
        if kw.upper() == "INPUT": return ("input", x)
        if kw.upper() == "OUTPUT": return ("output", x)
        raise BenchError(f"expected INPUT(NAME), OUTPUT(NAME) or NAME = OP(...), found '{kw}(...)'")
    if len(toks) >= 4 and toks[1] == "=" and toks[3] == "(":
        if not is_ident(toks[0]): raise BenchError("expected a signal name before '='")
        if not is_ident(toks[2]): raise BenchError("expected an operator name after '='")
        return ("gate", toks[0], toks[2].upper(), parse_args(toks[4:]))
    raise BenchError("expected INPUT(NAME), OUTPUT(NAME) or NAME = OP(NAME, ...)")


def parse(src):
    """Read a `.bench` file. Errors name the line."""
    nl = {"name": "", "inputs": [], "outputs": [], "gates": [], "ors": []}
    for i, line in enumerate(src.split("\n")):
        try: s = parse_line(line)
        except BenchError as e: raise BenchError(f"line {i + 1}: {e.msg}")
        if s[0] == "comment" and i == 0: nl["name"] = s[1]
        elif s[0] == "input": nl["inputs"].append(s[1])
        elif s[0] == "output": nl["outputs"].append(s[1])
        elif s[0] == "gate": nl["gates"].append([s[1], s[2], s[3]])
        elif s[0] == "or": nl["ors"].append([s[1], s[2]])
    return nl


def print_netlist(nl):
    """Write a netlist: the name as a comment, the inputs, the outputs, the directives, the gates."""
    ls = ["# " + nl["name"]] if nl["name"] else []
    ls += [f"INPUT({x})" for x in nl["inputs"]] + [f"OUTPUT({x})" for x in nl["outputs"]]
    ls += [f"#@ or {o} = {' '.join(ins)}" for o, ins in nl["ors"]] + [show_gate(g) for g in nl["gates"]]
    return "".join(l + "\n" for l in ls)


def first_dup(xs):
    for i, x in enumerate(xs):
        if x in xs[i + 1:]: return x


def to_circ(nl):
    """The circuit a netlist denotes: {"n", "sets", "gates", "outs"}; wire i < n is input i, wire n + k is gate k."""
    n = len(nl["inputs"]); defined = [g[0] for g in nl["gates"]]
    if (x := first_dup(nl["inputs"])) is not None: raise BenchError(f"input {x} is declared twice")
    if (x := first_dup(nl["outputs"])) is not None: raise BenchError(f"output {x} is declared twice")
    if (x := first_dup(defined)) is not None: raise BenchError(f"signal {x} is assigned twice", x)
    for x in defined:
        if x in nl["inputs"]: raise BenchError(f"signal {x} is an input and is also assigned", x)
    for g in nl["gates"]:
        x, op, args = g
        if op in ("AND", "OR"):
            if len(args) != 2: raise BenchError(f"{show_gate(g)}: {op} takes exactly 2 operands, found {len(args)}", x)
        elif op in ("NOT", "BUFF"):
            if len(args) != 1: raise BenchError(f"{show_gate(g)}: {op} takes exactly 1 operand, found {len(args)}", x)
        else: raise BenchError(f"{show_gate(g)}: operator {op} is not accepted (asteroid accepts AND, OR, NOT and BUFF)", x)
    known = set(nl["inputs"]) | set(defined)
    for g in nl["gates"]:
        for a in g[2]:
            if a not in known: raise BenchError(f"{show_gate(g)}: signal {a} is never defined", g[0])
    input_env = {x: i for i, x in enumerate(nl["inputs"])}
    env, gates, todo = dict(input_env), [], list(nl["gates"])
    while todo:                       # one pass places every gate whose operands have wires; a file in order needs one pass
        later = []
        for g in todo:
            x, op, args = g
            if any(a not in env for a in args): later.append(g); continue
            ws = [env[a] for a in args]
            if op == "BUFF": env[x] = ws[0]; continue
            env[x] = n + len(gates)
            gates.append(["not", ws[0]] if op == "NOT" else [op.lower(), ws[0], ws[1]])
        if len(later) == len(todo): raise BenchError(f"{show_gate(todo[0])}: this gate is on a cycle", todo[0][0])
        todo = later
    def wire(x):
        if x not in env: raise BenchError(f"output {x} is never defined")
        return env[x]
    out_wires = [wire(x) for x in nl["outputs"]]
    if not nl["ors"]: return {"n": n, "sets": [], "gates": gates, "outs": out_wires}
    with_dir = [o for o, _ in nl["ors"]]
    for x in nl["outputs"]:
        if x not in with_dir: raise BenchError(f"output {x} has no '#@ or' directive (every output needs one, or none)")
    sets, outs = [], []
    for o, ins in nl["ors"]:
        if o not in nl["outputs"]: raise BenchError(f"directive '#@ or {o} = ...': {o} is not declared with OUTPUT({o})")
        for x in ins:
            if x not in input_env: raise BenchError(f"directive '#@ or {o} = ...': {x} is not an input")
        sets.append([input_env[x] for x in ins]); outs.append(wire(o))
    return {"n": n, "sets": sets, "gates": gates, "outs": outs}


def read(src):
    """parse then to_circ. An error about a gate names the line of the file that defines it."""
    nl = parse(src)
    try: return to_circ(nl)
    except BenchError as e:
        for i, line in enumerate(src.split("\n")):
            try: s = parse_line(line)
            except BenchError: continue
            if e.signal is not None and s[0] == "gate" and s[1] == e.signal: raise BenchError(f"line {i + 1}: {e.msg}")
        raise


def of_circ(c, name=""):
    """The netlist of a circuit: inputs x0 ... x(n-1), gate k named gk, one `#@ or` directive per set."""
    n = c["n"]; w = lambda i: f"x{i}" if i < n else f"g{i - n}"
    gates = [[w(n + k), "NOT", [w(g[1])]] if g[0] == "not" else [w(n + k), g[0].upper(), [w(g[1]), w(g[2])]] for k, g in enumerate(c["gates"])]
    return {"name": name, "inputs": [w(i) for i in range(n)], "outputs": list(dict.fromkeys(w(o) for o in c["outs"])),
            "gates": gates, "ors": [[w(o), [w(u) for u in S]] for S, o in zip(c["sets"], c["outs"])]}


def handle(line, api):
    if m := re.fullmatch(r"let (\w+) = load (.+\.bench[\"']?)", line):
        import asteroid.asteroid as A
        A.check_name(m.group(1), f"{api['script']}:{api['ln']}")
        f = A.in_path(m.group(2))
        if not os.path.isfile(f): raise SystemExit(f"{api['script']}:{api['ln']}: load: no file {A._plain(m.group(2))} (looked beside the program and in the repository)")
        try: c = read(open(f, encoding="utf-8").read())
        except BenchError as e: raise SystemExit(f"{f}: {e.msg}")
        api["env"][m.group(1)] = c; api["src"][m.group(1)] = f
        print(f"{api['ln']}: {m.group(1)} loaded ({c['n']} inputs, {len(c['gates'])} gates)"); return True
    if m := re.fullmatch(r"save (\w+) -> (.+\.bench[\"']?)", line):
        if m.group(1) not in api["env"]: raise SystemExit(f"{api['script']}:{api['ln']}: save: no circuit named {m.group(1)}")
        import asteroid.asteroid as A
        f = A.out_path(m.group(2)); open(f, "w", encoding="utf-8", newline="\n").write(print_netlist(of_circ(api["env"][m.group(1)], m.group(1))))
        print(f"{api['ln']}: wrote {f}"); return True
    return False


def describe(d, path):
    """The first comment line of a converted file: what the circuit is."""
    name = " ".join(str(d.get("name") or os.path.splitext(os.path.basename(path))[0]).split())
    t = sum(g[0] == "not" for g in d["gates"])
    return f"{name}: {d['n']} inputs, {len(d['sets'])} sets, {len(d['gates'])} gates, {t} NOT gate{'' if t == 1 else 's'}"


def main(argv):
    for f in argv:
        d = json.load(open(f, encoding="utf-8")); c = {k: d[k] for k in ("n", "sets", "gates", "outs")}
        out = os.path.splitext(f)[0] + ".bench"; text = print_netlist(of_circ(c, describe(d, f)))
        back = read(text)
        if back != {**c, "gates": [list(g) for g in c["gates"]]}: raise SystemExit(f"{f}: the round trip changed the circuit; nothing written")
        open(out, "w", encoding="utf-8", newline="\n").write(text); print(f"wrote {out}")


if __name__ == "__main__": main(sys.argv[1:])
