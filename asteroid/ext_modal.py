"""asteroid extension: exact Kripke frames and propositional modal logic. Finite and exhaustive.
  kripke NAME = worlds N rel [(0,1), (1,2)] [val p {0,2} q {1}]   one frame on worlds 0..N-1 (an optional valuation)
  kripke NAME = all N PROP[+PROP...]                              every relation on N worlds with these properties
                                       PROP: reflexive | transitive | symmetric | euclidean | serial | any
  claim valid NAME "FORMULA"           true at every world, under every valuation, on every frame of NAME
  claim invalid NAME "FORMULA"         not valid: a countermodel exists (it is printed)
  claim defines NAME "FORMULA" PROP[+PROP...]   on every frame of NAME: FORMULA is valid iff the frame has PROP
  claim worlds NAME "FORMULA" = {0, 2} the worlds where FORMULA is true under NAME's valuation are exactly these
FORMULA: atoms (lowercase words, e.g. p q r), T, F, ~ (not), [] (box), <> (diamond), &, |, -> and <->.
Unary operators bind tightest, then &, then |, then -> and <-> (right associative). Parentheses as usual.
Size limits: N <= 12 for one frame, N <= 4 for `all`, at most 3 atoms in a validity claim, and at most
WORK frame-valuation pairs per claim. Past a limit the claim is FALSE, not slow. Python only; no floats."""
import re

FRAMES = {}       # name -> {"n": N, "rels": [succ masks tuple], "val": {atom: mask} or None, "desc": str}
MAX_ONE, MAX_ALL, MAX_ATOMS, WORK = 12, 4, 3, 2 * 10**6
NODES = 2 * 10**7          # most (frame-valuation pairs) x (formula size) for one claim
RUN_NODES = [6 * 10**7]    # the same, for all modal claims of one run together
PROPS = ("reflexive", "transitive", "symmetric", "euclidean", "serial", "any")

# ---- relations as successor bitmasks: succ[w] has bit v set iff w R v ----
def has(succ, prop):
    n = len(succ); R = lambda a, b: succ[a] >> b & 1
    if prop == "any": return True
    if prop == "reflexive": return all(R(w, w) for w in range(n))
    if prop == "serial": return all(succ[w] for w in range(n))
    if prop == "symmetric": return all(R(b, a) for a in range(n) for b in range(n) if R(a, b))
    if prop == "transitive": return all(succ[b] & ~succ[a] == 0 for a in range(n) for b in range(n) if R(a, b))
    if prop == "euclidean": return all(succ[a] & ~succ[b] == 0 for a in range(n) for b in range(n) if R(a, b))
    raise ValueError(prop)

def all_frames(n, props):
    out = []
    for code in range(1 << (n * n)):
        succ = tuple((code >> (w * n)) & ((1 << n) - 1) for w in range(n))
        if all(has(succ, p) for p in props): out.append(succ)
    return out

def pairs(succ): return [(a, b) for a in range(len(succ)) for b in range(len(succ)) if succ[a] >> b & 1]

# ---- formulas ----
def _tokens(s):
    t = re.findall(r"\s*(<->|->|\[\]|<>|[~&|()]|[a-z]\w*|T|F)", s)
    if "".join(t) != re.sub(r"\s+", "", s): raise ValueError(f"cannot read formula: {s}")
    return t

class _P:
    def __init__(self, s): self.t = _tokens(s); self.i = 0
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def eat(self, x=None):
        t = self.peek()
        if t is None or (x is not None and t != x): raise ValueError(f"expected {x or 'more'} at token {self.i}")
        self.i += 1; return t
    def imp(self):
        a = self.disj()
        if self.peek() in ("->", "<->"): op = self.eat(); return (op, a, self.imp())
        return a
    def disj(self):
        a = self.conj()
        while self.peek() == "|": self.eat(); a = ("|", a, self.conj())
        return a
    def conj(self):
        a = self.un()
        while self.peek() == "&": self.eat(); a = ("&", a, self.un())
        return a
    def un(self):
        t = self.eat()
        if t in ("~", "[]", "<>"): return (t, self.un())
        if t == "(": a = self.imp(); self.eat(")"); return a
        if t in ("T", "F"): return (t,)
        if re.fullmatch(r"[a-z]\w*", t): return ("atom", t)
        raise ValueError(f"unexpected {t}")

def parse(s):
    p = _P(s)
    try: a = p.imp()
    except RecursionError: raise ValueError("nested too deeply")
    if p.peek() is not None: raise ValueError(f"unexpected {p.peek()}")
    return a

def atoms(f):
    if f[0] == "atom": return {f[1]}
    return set().union(*[atoms(x) for x in f[1:]]) if len(f) > 1 else set()

def ev(f, succ, val):
    """The set of worlds (a bitmask) where f is true."""
    n = len(succ); full = (1 << n) - 1; k = f[0]
    if k == "atom": return val[f[1]]
    if k == "T": return full
    if k == "F": return 0
    if k == "~": return full & ~ev(f[1], succ, val)
    if k == "[]": s = ev(f[1], succ, val); return sum(1 << w for w in range(n) if succ[w] & ~s == 0)
    if k == "<>": s = ev(f[1], succ, val); return sum(1 << w for w in range(n) if succ[w] & s)
    a, b = ev(f[1], succ, val), ev(f[2], succ, val)
    if k == "&": return a & b
    if k == "|": return a | b
    if k == "->": return full & (~a | b)
    if k == "<->": return full & ~(a ^ b)
    raise ValueError(k)

def counter(f, succ):
    """None if f is valid on the frame, else (world, valuation) of a countermodel."""
    n, at = len(succ), sorted(atoms(f)); full = (1 << n) - 1
    for code in range(1 << (n * len(at))):
        val = {a: (code >> (i * n)) & full for i, a in enumerate(at)}
        bad = full & ~ev(f, succ, val)
        if bad: return (bad & -bad).bit_length() - 1, val
    return None

def _ws(mask, n): return "{" + ", ".join(str(w) for w in range(n) if mask >> w & 1) + "}"

def show_cm(succ, w, val):
    n = len(succ)
    return f"countermodel: {n} worlds, R = {pairs(succ)}, " + ", ".join(f"{a} = {_ws(m, n)}" for a, m in sorted(val.items())) + f", false at world {w}"

def _get(name, where):
    if name not in FRAMES: raise SystemExit(f"{where}: no kripke frame named {name}")
    return FRAMES[name]

def _props(s, where):
    ps = s.split("+")
    bad = [p for p in ps if p not in PROPS]
    if bad: raise SystemExit(f"{where}: {bad[0]} is not one of {' | '.join(PROPS)}")
    return ps

def _work(K, f, n):
    a = len(atoms(f))
    if a > MAX_ATOMS: return f"{a} atoms > {MAX_ATOMS}"
    w = len(K["rels"]) * (1 << (n * a))
    if w > WORK: return f"{w} frame-valuation pairs > {WORK}"
    x = w * size(f)
    if x > NODES: return f"{w} pairs x formula size {size(f)} = {x} > {NODES}"
    if x > RUN_NODES[0]: return f"this run already spent its {6 * 10**7} modal steps"
    RUN_NODES[0] -= x
    return None

def size(f): return 1 + sum(size(x) for x in f[1:] if isinstance(x, tuple))

def claim_expr(text, lean, api, force=False):
    m = re.fullmatch(r'(valid|invalid) (\w+) "([^"]+)"', text)
    md = re.fullmatch(r'defines (\w+) "([^"]+)" ([\w+]+)', text)
    mw = re.fullmatch(r'worlds (\w+) "([^"]+)"\s*=\s*\{([\d,\s]*)\}', text)
    if not (m or md or mw): return None
    where = f"{api.get('script')}:{api.get('ln')}"
    if lean: raise SystemExit(f"{where}: modal claims are exact Python checks; `by lean` is not available for them")
    name = (m or md or mw).group(2 if m else 1)
    K = _get(name, where); n = K["n"]
    try: f = parse((m or md or mw).group(3 if m else 2))
    except ValueError as e: return False, f"formula error: {e}"
    if mw:
        if K["val"] is None: return False, f"{name} has no valuation"
        miss = atoms(f) - set(K["val"])
        if miss: return False, f"{name} gives no value to {sorted(miss)[0]}"
        want = sum(1 << int(x) for x in mw.group(3).replace(",", " ").split())
        if want >> n: return False, f"a world in the set is not one of 0..{n - 1}"
        got = ev(f, K["rels"][0], K["val"])
        return got == want, f"true exactly at {_ws(got, n)}" + ("" if got == want else f", not {_ws(want, n)}")
    if (lim := _work(K, f, n)): return False, f"too large: {lim}"
    if m:
        for succ in K["rels"]:
            c = counter(f, succ)
            if c: return m.group(1) == "invalid", ("not valid; " if m.group(1) == "invalid" else "") + show_cm(succ, *c)
        return m.group(1) == "valid", f"valid on all {len(K['rels'])} frames of {name}, every valuation"
    ps = _props(md.group(3), where); yes = no = 0
    for succ in K["rels"]:
        hp = all(has(succ, p) for p in ps); c = counter(f, succ)
        if hp and c: return False, f"a {md.group(3)} frame where it fails: " + show_cm(succ, *c)
        if not hp and not c: return False, f"valid on a frame that is not {md.group(3)}: R = {pairs(succ)}"
        yes += hp; no += not hp
    return True, f"valid on exactly the {yes} {md.group(3)} frames of {name}; refuted on each of the other {no}"

def handle(line, api):
    import asteroid.asteroid as A
    ln, where = api["ln"], f"{api['script']}:{api['ln']}"
    if m := re.fullmatch(r"kripke (\w+) = all (\d+) ([\w+]+)", line):
        n, ps = int(m.group(2)), _props(m.group(3), where)
        if not 1 <= n <= MAX_ALL: raise SystemExit(f"{where}: `all` needs 1 <= N <= {MAX_ALL}")
        FRAMES[m.group(1)] = {"n": n, "rels": all_frames(n, ps), "val": None}
        A.say(f"{ln}: kripke {m.group(1)} = {len(FRAMES[m.group(1)]['rels'])} relations on {n} worlds that are {m.group(3)}"); return True
    if m := re.fullmatch(r"kripke (\w+) = worlds (\d+) rel \[([\d\s,()]*)\](?: val (.+))?", line):
        n = int(m.group(2))
        if not 1 <= n <= MAX_ONE: raise SystemExit(f"{where}: worlds needs 1 <= N <= {MAX_ONE}")
        body = m.group(3)
        if re.sub(r"\(\s*\d+\s*,\s*\d+\s*\)|[\s,]", "", body): raise SystemExit(f"{where}: rel must be a list of pairs (a, b)")
        succ = [0] * n
        for a, b in re.findall(r"\(\s*(\d+)\s*,\s*(\d+)\s*\)", body):
            a, b = int(a), int(b)
            if a >= n or b >= n: raise SystemExit(f"{where}: pair ({a}, {b}) names a world outside 0..{n - 1}")
            succ[a] |= 1 << b
        val = None
        if m.group(4):
            val = {}
            for at, ws in re.findall(r"([a-z]\w*)\s*\{([\d,\s]*)\}", m.group(4)):
                val[at] = sum(1 << int(x) for x in ws.replace(",", " ").split())
                if val[at] >> n: raise SystemExit(f"{where}: valuation of {at} names a world outside 0..{n - 1}")
            if re.sub(r"[a-z]\w*\s*\{[\d,\s]*\}|\s", "", m.group(4)): raise SystemExit(f"{where}: val must be: ATOM {{w, ...}} ...")
        FRAMES[m.group(1)] = {"n": n, "rels": [tuple(succ)], "val": val}
        props = [p for p in PROPS[:-1] if has(tuple(succ), p)]
        A.say(f"{ln}: kripke {m.group(1)} = {n} worlds, {sum(bin(s).count('1') for s in succ)} arrows ({', '.join(props) or 'none of the five properties'})"); return True
    return False
