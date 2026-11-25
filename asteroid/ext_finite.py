"""asteroid extension: exact finite claims about integer sequences, for any level of the repository.
  seq NAME = from PATH ["KEY"]              a .json list, or the entry of a fingerprints.json whose name contains KEY
  seq NAME = run "CMD" ["KEY"]              run a repo check (must exit 0), then read the fingerprints.json beside it
  seq NAME = [1, 2, 5, 15]                  a literal sequence
  claim NAME = [1, 2, 5, 15]                the first terms of NAME are exactly these
  claim NAME matches NAME2 [FORM]           FORM(NAME) and NAME2 agree on their common prefix (>= 5 terms);
                                            FORM is as-is | diff | partial | plus1 (the centre's matcher forms)
  claim formula NAME = "EXPR" [from K]      every term equals EXPR at n = K, K+1, ... (K defaults to 1)
  check "CMD"                               a repo check that must exit 0 and print PASS; counts as a claim
EXPR uses integers and n, + - * // ** ( ), postfix ! and !!, C(a, b), and sum(k, LO, HI, EXPR).
Integers only: `//` must divide exactly, or the claim is FALSE. CMD is `python3 -I path.py [args]`, run from the
repository root with a timeout. A check that passes is the record's runner, so `checked-finite` records carry it."""
import json, os, re, shlex, subprocess, sys
import asteroid.asteroid as A

SEQ = {}            # name -> list of int
TIMEOUT = 900
LIMIT = 10**6       # largest n in n!, n!!, C(n, k), and the most terms one sum may add
STEPS = 10**7       # most evaluation steps for one formula claim
RUN_STEPS = [3 * 10**7]   # most evaluation steps for all formula claims of one run together
MAXBITS = 10**6     # largest integer a formula may make (bits); a step on a big integer costs 1 + bits // 1024
WRITERS = {"boards.py", "center.py", "one-not/tools/tensor/dag.py", "compute/funsearch/targets.py"}   # they write findings or run shell commands
INT = re.compile(r"-?\d+")

def _lit(body, where):
    """The integers of a literal list. Each item must be a plain integer."""
    xs = [x for x in body.replace(",", " ").split()]
    bad = [x for x in xs if not INT.fullmatch(x)]
    if bad: raise SystemExit(f"{where}: not an integer: {bad[0]}")
    return [int(x) for x in xs]

def _passed(out):
    """A check passes only if one stdout line is exactly PASS and no line has the word FAIL."""
    ls = [l.strip() for l in out.splitlines()]
    return "PASS" in ls and not any("FAIL" in re.findall(r"\w+", l) for l in ls)

def _ints(xs, where):
    if not isinstance(xs, list) or not all(isinstance(x, int) and not isinstance(x, bool) for x in xs):
        raise SystemExit(f"{where}: not a list of integers")
    return list(xs)

def _cmd(cmd, where):
    """`python3 -I path.py [args]`, path a file inside the repository. Returns argv with this Python."""
    p = shlex.split(cmd)
    if len(p) < 3 or p[0] != "python3" or p[1] != "-I" or not p[2].endswith(".py"):
        raise SystemExit(f"{where}: CMD must be: python3 -I path.py [args]")
    f = os.path.realpath(os.path.join(A.ROOT, p[2]))
    if os.path.commonpath([os.path.realpath(A.ROOT), f]) != os.path.realpath(A.ROOT) or not os.path.isfile(f):
        raise SystemExit(f"{where}: no such file in the repository: {p[2]}")
    if os.path.relpath(f, os.path.realpath(A.ROOT)).replace(os.sep, "/") in WRITERS:
        raise SystemExit(f"{where}: {p[2]} writes records or runs commands; a check may not run it")
    return [sys.executable, "-I"] + p[2:], p[2]

def _run(cmd, where):
    argv, path = _cmd(cmd, where)
    env = A.child_env(where)
    try: r = subprocess.run(argv, cwd=A.ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=TIMEOUT, env=env)
    except subprocess.TimeoutExpired: return False, f"timed out after {TIMEOUT} s", path, ""
    return r.returncode == 0, f"exit {r.returncode}", path, r.stdout

def _from_file(f, key, where):
    d = json.load(open(f, encoding="utf-8"))
    if key is None: return _ints(d, where)
    hits = [e for e in d if isinstance(e, dict) and key in e.get("name", "")]
    if len(hits) != 1: raise SystemExit(f"{where}: {len(hits)} entries of {f} have \"{key}\" in their name (need exactly 1)")
    return _ints(hits[0]["seq"], where)

# ---- the formula language: a small exact parser, no eval ----
def _tokens(s):
    out = []
    for m in re.finditer(r"\s*(?:(\d+)|([A-Za-z_]\w*)|(\*\*|//|!!|[-+*!(),]))", s):
        out.append(m.group(1) or m.group(2) or m.group(3))
    if "".join(out) != re.sub(r"\s+", "", s): raise ValueError(f"cannot read formula: {s}")
    return out

class _P:
    def __init__(self, s): self.t = _tokens(s); self.i = 0
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def eat(self, x=None):
        t = self.peek()
        if t is None or (x is not None and t != x): raise ValueError(f"expected {x or 'more'} at token {self.i}")
        self.i += 1; return t
    def expr(self):
        a = self.term()
        while self.peek() in ("+", "-"):
            op = self.eat(); b = self.term(); a = (op, a, b)
        return a
    def term(self):
        a = self.unary()
        while self.peek() in ("*", "//"):
            op = self.eat(); b = self.unary(); a = (op, a, b)
        return a
    def unary(self):
        if self.peek() == "-": self.eat(); return ("neg", self.unary())
        return self.power()
    def power(self):
        a = self.postfix()
        if self.peek() == "**": self.eat(); return ("**", a, self.unary())
        return a
    def postfix(self):
        a = self.atom()
        while self.peek() in ("!", "!!"): a = (self.eat(), a)
        return a
    def atom(self):
        t = self.eat()
        if t.isdigit(): return ("int", int(t))
        if t == "(": a = self.expr(); self.eat(")"); return a
        if t == "C" and self.peek() == "(":
            self.eat("("); a = self.expr(); self.eat(","); b = self.expr(); self.eat(")"); return ("C", a, b)
        if t == "sum" and self.peek() == "(":
            self.eat("("); v = self.eat()
            if not re.fullmatch(r"[A-Za-z_]\w*", v): raise ValueError("sum needs a variable")
            self.eat(","); lo = self.expr(); self.eat(","); hi = self.expr(); self.eat(","); body = self.expr(); self.eat(")")
            return ("sum", v, lo, hi, body)
        if re.fullmatch(r"[A-Za-z_]\w*", t): return ("var", t)
        raise ValueError(f"unexpected {t}")

def parse(s):
    p = _P(s); a = p.expr()
    if p.peek() is not None: raise ValueError(f"unexpected {p.peek()}")
    return a

def _big(x, what):
    if x > LIMIT: raise ValueError(f"{what} with {x} > {LIMIT} is too large")

def _bits(r, budget, mul=False):
    """Charge a result by its size: big integers cost more steps (k = bits // 1024: k for a sum or a small factor,
    k * k // 8 more for a product of two big numbers or a power). Past MAXBITS the claim is FALSE."""
    b = abs(r).bit_length() if isinstance(r, int) else 0
    if b > MAXBITS: raise ValueError(f"a number with more than {MAXBITS} bits")
    budget[0] -= (b >> 10) + (((b >> 10) ** 2) >> 3 if mul else 0)
    if budget[0] < 0: raise ValueError(f"more than {STEPS} steps")
    return r

def ev(a, V, budget=None):
    if budget is None: budget = [STEPS]
    budget[0] -= 1
    if budget[0] < 0: raise ValueError(f"more than {STEPS} steps")
    _ev = lambda b, W=V: ev(b, W, budget)
    k = a[0]
    if k == "int": return a[1]
    if k == "var":
        if a[1] not in V: raise ValueError(f"unknown name {a[1]}")
        return V[a[1]]
    if k == "neg": return -_ev(a[1], V)
    if k in ("+", "-", "*", "//", "**"):
        x, y = _ev(a[1], V), _ev(a[2], V)
        if k == "+": return _bits(x + y, budget)
        if k == "-": return _bits(x - y, budget)
        if k == "*":
            if abs(x).bit_length() + abs(y).bit_length() > MAXBITS + 1: raise ValueError(f"a number with more than {MAXBITS} bits")
            return _bits(x * y, budget, min(abs(x), abs(y)).bit_length() > 64)
        if k == "//":
            if abs(y).bit_length() > 64: budget[0] -= ((abs(x).bit_length() >> 10) ** 2) >> 1   # a long division: k * k // 2
            if y == 0 or x % y: raise ValueError(f"{x} // {y} is not exact")
            return x // y
        if y < 0: raise ValueError(f"{x} ** {y}: negative exponent")
        if abs(x) > 1 and y > 100000: raise ValueError("exponent too large")
        if abs(x) > 1 and (abs(x).bit_length() - 1) * y > MAXBITS: raise ValueError(f"a number with more than {MAXBITS} bits")
        return _bits(x ** y, budget, True)
    if k == "!":
        x = _ev(a[1], V)
        if x < 0: raise ValueError(f"({x})! is undefined")
        _big(x, "n!"); budget[0] -= x
        r = 1
        for i in range(2, x + 1): r = _bits(r * i, budget)
        return r
    if k == "!!":
        x = _ev(a[1], V)
        if x < -1: raise ValueError(f"({x})!! is undefined")
        _big(x, "n!!"); budget[0] -= x // 2
        r = 1
        while x > 1: r = _bits(r * x, budget); x -= 2
        return r                                   # 0!! = (-1)!! = 1
    if k == "C":
        x, y = _ev(a[1], V), _ev(a[2], V)
        if x < 0: raise ValueError(f"C({x}, {y}): negative top")
        if y < 0 or y > x: return 0
        _big(x, "C(n, k)"); budget[0] -= y
        r = 1
        for i in range(y): r = _bits(r * (x - i), budget) // (i + 1)
        return r
    if k == "sum":
        lo, hi = _ev(a[2], V), _ev(a[3], V)
        _big(hi - lo + 1, "a sum of terms")
        t = 0
        for j in range(lo, hi + 1): t = _bits(t + _ev(a[4], {**V, a[1]: j}), budget)
        return t
    raise ValueError(k)

FORMS = {"as-is": lambda s: list(s), "diff": lambda s: [b - a for a, b in zip(s, s[1:])],
         "partial": lambda s: [sum(s[:i + 1]) for i in range(len(s))], "plus1": lambda s: [x + 1 for x in s]}

def _get(name):
    if name not in SEQ: raise SystemExit(f"no sequence named {name} (define it with `seq {name} = ...`)")
    return SEQ[name]

def _show(s, k=8): return "[" + ", ".join(map(str, s[:k])) + (", ..." if len(s) > k else "") + "]"

def claim_expr(text, lean, api, force=False):
    """The finite claim forms. Returns (ok, detail) or None. Python only: `by lean` is refused."""
    m1 = re.fullmatch(r"(\w+)\s*=\s*\[([-\d,\s]*)\]", text)
    m2 = re.fullmatch(r"(\w+) matches (\w+)(?: (as-is|diff|partial|plus1))?", text)
    m3 = re.fullmatch(r'formula (\w+)\s*=\s*"([^"]+)"(?: from (-?\d+))?', text)
    if not (m1 or m2 or m3): return None
    if lean: raise SystemExit(f"{api['script']}:{api['ln']}: finite claims are exact Python checks; `by lean` is not available for them")
    if m1:
        s, want = _get(m1.group(1)), _lit(m1.group(2), f"{api['script']}:{api['ln']}")
        if not want: return False, "an empty list tests nothing"
        if len(s) < len(want): return False, f"{m1.group(1)} has only {len(s)} terms"
        bad = [i for i, (x, y) in enumerate(zip(s, want)) if x != y]
        return (not bad), (f"first {len(want)} terms equal" if not bad else f"term {bad[0] + 1}: {s[bad[0]]} != {want[bad[0]]}")
    if m2:
        form = m2.group(3) or "as-is"
        a, b = FORMS[form](_get(m2.group(1))), _get(m2.group(2)); k = min(len(a), len(b))
        if k < 5: return False, f"common prefix has {k} terms, need at least 5"
        bad = [i for i in range(k) if a[i] != b[i]]
        return (not bad), (f"{form}({m2.group(1)}) = {m2.group(2)} on the first {k} terms" if not bad
                           else f"term {bad[0] + 1}: {form}({m2.group(1)}) gives {a[bad[0]]}, {m2.group(2)} has {b[bad[0]]}")
    s, k0 = _get(m3.group(1)), int(m3.group(3) or 1)
    try:
        f = parse(m3.group(2))
        if not s: return False, f"{m3.group(1)} has no terms, so the formula is tested on nothing"
        if RUN_STEPS[0] <= 0: return False, f"this run already spent its {3 * 10**7} formula steps"
        budget = [min(STEPS, RUN_STEPS[0])]; start = budget[0]
        try:
            for i, x in enumerate(s):
                y = ev(f, {"n": k0 + i}, budget)
                if y != x: return False, f"n={k0 + i}: formula gives {y}, sequence has {x}"
        finally: RUN_STEPS[0] -= start - max(budget[0], 0)
    except ValueError as e: return False, f"formula error: {e}"
    except RecursionError: return False, "formula error: nested too deeply"
    return True, f"formula equals all {len(s)} terms, n={k0}..{k0 + len(s) - 1}"

def handle(line, api):
    ln, where = api["ln"], f"{api['script']}:{api['ln']}"
    if m := re.fullmatch(r'seq (\w+) = from (\S+?)(?: "([^"]+)")?', line):
        f = A.in_path(m.group(2)); SEQ[m.group(1)] = _from_file(f, m.group(3), where); api["src"]["seq " + m.group(1)] = os.path.relpath(f, A.ROOT) if os.path.isabs(f) else f
        A.say(f"{ln}: seq {m.group(1)} = {_show(SEQ[m.group(1)])} ({len(SEQ[m.group(1)])} terms, from {f})"); return True
    if m := re.fullmatch(r'seq (\w+) = run "([^"]+)"(?: "([^"]+)")?', line):
        f = os.path.join(os.path.dirname(path := _cmd(m.group(2), where)[1]), "fingerprints.json")
        fa = os.path.join(A.ROOT, f)
        before = os.stat(fa).st_mtime_ns if os.path.isfile(fa) else None
        ok, why, path, _ = _run(m.group(2), where)
        if not ok: raise SystemExit(f"{where}: {m.group(2)} failed ({why})")
        fresh = os.path.isfile(fa) and os.stat(fa).st_mtime_ns != before
        if not os.path.isfile(os.path.join(A.ROOT, f)): raise SystemExit(f"{where}: no {f} beside {path}")
        SEQ[m.group(1)] = _from_file(os.path.join(A.ROOT, f), m.group(3), where); api["src"]["seq " + m.group(1)] = f
        A.RUNNERS.append(m.group(2))
        A.say(f"{ln}: seq {m.group(1)} = {_show(SEQ[m.group(1)])} ({len(SEQ[m.group(1)])} terms, {m.group(2)} passed; " + (f"it wrote {f})" if fresh else f"{f} is the committed copy, not written by this run)")); return True
    if m := re.fullmatch(r"seq (\w+) = \[([-\d,\s]*)\]", line):
        SEQ[m.group(1)] = _lit(m.group(2), where); A.say(f"{ln}: seq {m.group(1)} = {_show(SEQ[m.group(1)])}"); return True
    if m := re.fullmatch(r'check "([^"]+)"', line):
        ok, why, path, out = _run(m.group(1), where)
        ok = ok and _passed(out)
        if ok: A.RUNNERS.append(m.group(1)); api["src"]["check " + path] = path
        api["results"].append((ln, f'check "{m.group(1)}"', ok, False))
        A.say(f"{ln}: check {m.group(1)}: python {'TRUE' if ok else 'FALSE'} ({why}, {'printed PASS' if _passed(out) else 'no PASS line, or a FAIL'})"); return True
    return False
