"""asteroid extension: the edges (NOT-gate fix, hypotheses, implication, the Theorem as one claim).
  flip(NAME) flipclasses(NAME) flipslack(NAME)   first-class terms in  F(NAME) OP RHS  (Python only; no Lean form)
  claim hyps(NAME) [by lean]                     the Theorem's other hypotheses; Lean: hypsB NAME = true
  claim hyps(NAME) = false [by lean]             the same, and Lean: hypsB NAME = false (Python and kernel agree on failures)
  claim if EXPR1 then EXPR2                      implication (Python only); also inside  claim forall c in W: if ... then ...
  claim EXPR1 and EXPR2                          conjunction of claim expressions
  claim theorem(NAME) [by lean]                  if hyps and correct then gates >= base; Lean: hypsB, correctB and the gate count
A user `conjecture theorem:` shadows the builtin theorem(c).
Python definitions: flip and flipclasses are one-not/tools/search/conjectures.py (`_flip_gates`, `count_flip_classes`);
hyps mirrors `hypsB` of one-not/lean/PEqualNP/W951/AsteroidCheap.lean line by line."""
import re
import asteroid.asteroid as A
from conjectures import _flip_gates

def _fg(c): return _flip_gates(c, "flip")
def flip(c): return len(_fg(c)[0])
def flipclasses(c):
    f, w = _fg(c); n = c["n"]; M = (1 << (1 << n)) - 1
    return len({min(w[n + k], M ^ w[n + k]) for k in f})
def flipslack(c): return flipclasses(c) - A.core.base(c)

def hyps(c):
    """hypsB: setsOkB && sets <= outs && 0 < gates && every set >= 2 points && pairwise intersection <= 1 (i != j) && notCount <= 1."""
    S, n = c["sets"], c["n"]
    return (all(len(set(s)) == len(s) and all(0 <= u < n for u in s) for s in S)
            and len(S) <= len(c["outs"]) and len(c["gates"]) > 0 and all(len(s) >= 2 for s in S)
            and all(i == j or len([u for u in S[i] if u in S[j]]) <= 1 for i in range(len(S)) for j in range(len(S)))
            and A.core.nots(c) <= 1)

A.EXTRA_F.update({"flip": flip, "flipclasses": flipclasses, "flipslack": flipslack})

NOTED = set()
def _note(text, env):
    """The one-NOT assumption of slack / orwitness / forall cubes / forall p phi, made explicit (once per circuit)."""
    for m in re.finditer(r'(?<![\w])(?:slack|orwitness|phi)\((\w+)', text):
        nm = m.group(1)
        if nm in env and not nm.startswith("_") and nm not in NOTED and A.core.nots(env[nm]) > 1:
            NOTED.add(nm); k = A.core.nots(env[nm])
            print(f"note: {nm} has {k} NOT gates; slack counts OR witnesses (the one-NOT count); use flipslack for several NOT gates")

def _split(text, kw):
    """split at the keyword ` kw ` outside quotes and brackets"""
    out, cur, depth, q, i = [], "", 0, False, 0
    pat = f" {kw} "
    if pat not in text: return [text]       # the common case, in linear time (a long seq literal took minutes)
    while i < len(text):
        ch = text[i]
        if ch == '"': q = not q
        elif not q and ch in "[({": depth += 1
        elif not q and ch in "])}": depth -= 1
        if not q and depth == 0 and text.startswith(pat, i): out.append(cur); cur = ""; i += len(pat); continue
        cur += ch; i += 1
    return out + [cur]

def claim_expr(text, lean, api, force=False):
    env = api["env"]; _note(text, env)
    if text.startswith("if "):
        parts = text[3:].split(" then ", 1)
        if len(parts) == 2:
            ok1, d1 = A.do_claim(parts[0].strip(), False)
            if not ok1: return True, f"hypothesis false ({d1}); implication holds", text
            ok2, d2 = A.do_claim(parts[1].strip(), False)
            return ok2, f"hypothesis true ({d1}); conclusion: {d2}" + ("  (Python only)" if lean else ""), text
    parts = _split(text, "and")
    if len(parts) > 1:
        rs = [A.do_claim(p.strip(), lean) for p in parts]
        return all(r[0] for r in rs), " and ".join(r[1] for r in rs), text
    m = re.fullmatch(r"hyps\((\w+)\)(?:\s*=\s*(true|false))?", text)
    if m:
        name, want = m.group(1), m.group(2) or "true"; v = hyps(env[name]); ok = (v == (want == "true"))
        if lean and (ok or force):
            api["extra_lean"]["imports"].append("PEqualNP.W951.AsteroidCheap")
            api["lean_claims"].append((name, "claim", f"hypsB {name} = {want}", text))
        return ok, f"hyps = {v}", text
    m = re.fullmatch(r"theorem\((\w+)\)", text)
    if m:
        name = m.group(1); c = env[name]; h, k = hyps(c), A.core.correct(c); g = len(c["gates"]) >= A.core.base(c)
        ok = (not (h and k)) or g
        if lean and (ok or force) and h and k and g:
            api["extra_lean"]["imports"].append("PEqualNP.W951.AsteroidCheap")
            for st in (f"hypsB {name} = true", f"correctB {name} = true", f"({name}.sets.map (fun S => S.length - 1)).sum ≤ {name}.gates.length"):
                api["lean_claims"].append((name, "claim", st, text))
        return ok, f"hyps {h}, correct {k}, gates {len(c['gates'])} vs base {A.core.base(c)}" + (" (hypotheses fail: vacuous)" if not (h and k) else ""), text
    return None

def handle(line, api): return False
