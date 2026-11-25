#!/usr/bin/env python3
"""Score the Claude-Haiku C3 replication (claude_haiku_rows.json) with the trial's blind scorer.
Strict = the original rule (last number in the reply). Lenient = the answer appears among the numbers.
st07's key is corrected from 3 to 2 here ("mississippi" has two p's); the original tasks.json still says 3.
Run: python3 -I workshop/ath_prompts/measure/trial/score_claude.py"""
import json, math, os, re, signal
D = os.path.dirname(os.path.abspath(__file__))
tasks = {t["id"]: t for t in json.load(open(os.path.join(D, "tasks_claude.json")))}
tasks["st07"]["answer"] = "2"
rows = json.load(open(os.path.join(D, "claude_haiku_rows.json")))
CS = {"st02", "st06"}

def score(t, out, lenient):
    k, a = t["kind"], t["answer"]
    if k == "num":
        nums = [float(x) for x in re.findall(r"-?\d+(?:\.\d+)?", out.replace(",", ""))]
        return bool(nums) and ((float(a) in nums) if lenient else nums[-1] == float(a))
    if k == "contains": return a in out if t["id"] in CS else a.lower() in out.lower()
    m = re.findall(r"```(?:python)?\n(.*?)```", out, re.S)
    code = m[0] if m else "\n".join(l for l in out.splitlines() if l.startswith(("def ", "f =", "f=", "    ")))
    try:
        signal.alarm(2); g = {}; exec(code, g); exec(a, g); signal.alarm(0); return True
    except BaseException:
        signal.alarm(0); return False

def table(ids, lenient):
    p = {}
    for r in rows:
        if r["id"] in ids: p.setdefault(r["id"], {})[r["register"]] = score(tasks[r["id"]], r["response"] or "", lenient)
    i_only = sum(v["informal"] and not v["formal"] for v in p.values()); f_only = sum(v["formal"] and not v["informal"] for v in p.values())
    n = i_only + f_only; k = min(i_only, f_only)
    pv = min(1.0, 2 * sum(math.comb(n, j) for j in range(k + 1)) / 2 ** n) if n else 1.0
    return f"informal {sum(v['informal'] for v in p.values())}/{len(p)}  formal {sum(v['formal'] for v in p.values())}/{len(p)}  informal-only {i_only}  formal-only {f_only}  exact sign test p={pv:.3f}"

sets = {"all 42": list(tasks), "original 30": [i for i in tasks if not i.startswith("h")], "harder 12": [i for i in tasks if i.startswith("h")]}
for name, ids in sets.items():
    print(f"{name:12} strict  : {table(ids, False)}\n{'':12} lenient : {table(ids, True)}")
print("PASS")
