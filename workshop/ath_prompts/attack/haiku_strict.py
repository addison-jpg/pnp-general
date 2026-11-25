#!/usr/bin/env python3
"""Attack (a): rescore the Haiku C3 rows with stricter scorers. Standard library only. No model calls.
Scorers for 'num' tasks:  last  = last number is the answer (the trial's strict rule)
                          any   = the answer is among the numbers (the trial's lenient rule)
                          first = the first number is the answer (the stated final answer leads)
                          exact = the reply is the answer and nothing else (after trimming quotes, spaces, a final '.')
For 'contains' tasks: last/any/first use the trial rule; exact needs the reply to be the answer only.
'py' tasks: the trial's exec test under every scorer.
Run: python3 -I workshop/ath_prompts/attack/haiku_strict.py"""
import json, math, os, re, signal
T = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "measure", "trial")
tasks = {t["id"]: t for t in json.load(open(os.path.join(T, "tasks_claude.json")))}
tasks["st07"]["answer"] = "2"  # same key fix as score_claude.py
rows = json.load(open(os.path.join(T, "claude_haiku_rows.json")))
CS = {"st02", "st06"}

def nums(s): return [float(x) for x in re.findall(r"-?\d+(?:\.\d+)?", s.replace(",", ""))]
def trim(s): return s.strip().rstrip(".").strip().strip("'\"`").strip()

def py_ok(t, out):
    m = re.findall(r"```(?:python)?\n(.*?)```", out, re.S)
    code = m[0] if m else "\n".join(l for l in out.splitlines() if l.startswith(("def ", "f =", "f=", "    ")))
    try:
        signal.alarm(2); g = {}; exec(code, g); exec(t["answer"], g); signal.alarm(0); return True
    except BaseException:
        signal.alarm(0); return False

def score(t, out, rule):
    k, a = t["kind"], str(t["answer"])
    if k == "py": return py_ok(t, out)
    if rule == "exact":
        r = trim(out)
        if k == "num":
            try: return float(r.replace(",", "").lstrip("$")) == float(a)
            except ValueError: return False
        return r == a if t["id"] in CS else r.lower() == a.lower()
    if k == "num":
        n = nums(out)
        if not n: return False
        return {"last": n[-1], "first": n[0]}.get(rule, None) == float(a) if rule != "any" else float(a) in n
    return a in out if t["id"] in CS else a.lower() in out.lower()

def sign_p(x, y):
    n, k = x + y, min(x, y)
    return min(1.0, 2 * sum(math.comb(n, j) for j in range(k + 1)) / 2 ** n) if n else 1.0

def table(ids, rule):
    p = {}
    for r in rows:
        if r["id"] in ids: p.setdefault(r["id"], {})[r["register"]] = score(tasks[r["id"]], r["response"] or "", rule)
    i = sum(v["informal"] for v in p.values()); f = sum(v["formal"] for v in p.values())
    io = sum(v["informal"] and not v["formal"] for v in p.values()); fo = sum(v["formal"] and not v["informal"] for v in p.values())
    return i, f, io, fo, sign_p(io, fo), len(p)

sets = {"all 42": list(tasks), "original 30": [i for i in tasks if not i.startswith("h")], "harder 12": [i for i in tasks if i.startswith("h")],
        "all 42 minus ar04": [i for i in tasks if i != "ar04"]}
print("set | scorer | informal | formal | informal-only | formal-only | exact sign p")
for name, ids in sets.items():
    for rule in ("any", "last", "first", "exact"):
        i, f, io, fo, p, n = table(ids, rule)
        print(f"{name} | {rule} | {i}/{n} | {f}/{n} | {io} | {fo} | {p:.4f}")
# reply length: the 'exact' rule mostly measures terseness
L = {}
for r in rows: L.setdefault(r["register"], []).append(len(r["response"] or ""))
print("mean reply chars: informal %.1f, formal %.1f" % (sum(L["informal"]) / len(L["informal"]), sum(L["formal"]) / len(L["formal"])))
print("PASS")
