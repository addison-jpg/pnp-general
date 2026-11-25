"""asteroid extension: exact finite probability. Integers and Fractions only, no floats.
  dist NAME = {OUT: P, OUT: P, ...}     a finite distribution; OUT is a word or an integer, P is an integer or a/b,
                                        each P >= 0, and the P must sum to exactly 1 (else the line is an error)
  dist NAME = NAME1 * NAME2             the product (independent pair); an outcome is written A.B
  claim prob NAME (OUT, OUT, ...) = F   the probability of the event {OUT, ...} is exactly F
  claim expect NAME = F                 the mean is exactly F; every outcome must be an integer
An outcome named in an event that NAME does not have makes the claim FALSE, not silently 0."""
import re
from fractions import Fraction

DIST = {}           # name -> dict outcome(str) -> Fraction
OUT = re.compile(r"-?\d+|[A-Za-z_]\w*(?:\.[A-Za-z_0-9]\w*)*|-?\d+(?:\.-?\d+)+")

def frac(s, where):
    s = s.strip()
    if not re.fullmatch(r"-?\d+(?:\s*/\s*\d+)?", s): raise SystemExit(f"{where}: not an integer or a/b: {s}")
    a, _, b = s.partition("/")
    try: a, b = int(a), (int(b) if b else 1)
    except ValueError as e: raise SystemExit(f"{where}: {e}")      # more digits than Python reads from text
    if b == 0: raise SystemExit(f"{where}: zero denominator: {s}")
    return Fraction(a, b)

def parse_dist(body, where):
    d = {}
    for item in [x for x in body.split(",") if x.strip()]:
        if ":" not in item: raise SystemExit(f"{where}: expected OUT: P, got {item.strip()}")
        o, p = (x.strip() for x in item.split(":", 1))
        if not OUT.fullmatch(o): raise SystemExit(f"{where}: bad outcome name {o}")
        if o in d: raise SystemExit(f"{where}: outcome {o} given twice")
        d[o] = frac(p, where)
        if d[o] < 0: raise SystemExit(f"{where}: negative probability for {o}")
    if not d: raise SystemExit(f"{where}: empty distribution")
    if sum(d.values()) != 1: raise SystemExit(f"{where}: probabilities sum to {sum(d.values())}, not 1")
    return d

MAX_OUT = 10**6     # most outcomes of one distribution (a product of two big ones would not halt in time)

def product(a, b):
    if len(a) * len(b) > MAX_OUT: raise SystemExit(f"a product with {len(a) * len(b)} outcomes > {MAX_OUT}")
    return {f"{x}.{y}": p * q for x, p in a.items() for y, q in b.items()}

def _get(name, where):
    if name not in DIST: raise SystemExit(f"{where}: no distribution named {name}")
    return DIST[name]

def _show(d): return "{" + ", ".join(f"{o}: {p}" for o, p in list(d.items())[:6]) + (", ..." if len(d) > 6 else "") + "}"

def claim_expr(text, lean, api, force=False):
    m1 = re.fullmatch(r"prob (\w+) \(([^)]*)\)\s*=\s*(\S+)", text)
    m2 = re.fullmatch(r"expect (\w+)\s*=\s*(\S+)", text)
    if not (m1 or m2): return None
    where = f"{api.get('script')}:{api.get('ln')}"
    if lean: raise SystemExit(f"{where}: probability claims are exact Python checks; `by lean` is not available for them")
    if m1:
        d, want = _get(m1.group(1), where), frac(m1.group(3), where)
        ev = [x.strip() for x in m1.group(2).split(",") if x.strip()]
        if not ev: return False, "an empty event tests nothing"
        miss = [o for o in ev if o not in d]
        if miss: return False, f"{m1.group(1)} has no outcome {miss[0]}"
        if len(set(ev)) != len(ev): return False, "an outcome is listed twice in the event"
        got = sum(d[o] for o in ev)
        return got == want, f"P = {got}" + ("" if got == want else f", not {want}")
    d, want = _get(m2.group(1), where), frac(m2.group(2), where)
    if not all(re.fullmatch(r"-?\d+", o) for o in d): return False, "expect needs integer outcomes"
    got = sum(int(o) * p for o, p in d.items())
    return got == want, f"E = {got}" + ("" if got == want else f", not {want}")

def handle(line, api):
    ln, where = api["ln"], f"{api['script']}:{api['ln']}"
    if m := re.fullmatch(r"dist (\w+) = \{(.*)\}", line):
        DIST[m.group(1)] = parse_dist(m.group(2), where)
    elif m := re.fullmatch(r"dist (\w+) = (\w+) \* (\w+)", line):
        DIST[m.group(1)] = product(_get(m.group(2), where), _get(m.group(3), where))
    else: return False
    import asteroid.asteroid as A
    A.say(f"{ln}: dist {m.group(1)} = {_show(DIST[m.group(1)])} ({len(DIST[m.group(1)])} outcomes, sum 1)"); return True
