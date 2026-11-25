#!/usr/bin/env python3
"""Attack on the Qwen C3 trial: rescore results.json with the st07 key fixed (2, not 3), with the
'any number' rule, and without the two pairs that differ in content (ar04, ar10). Standard library only.
Run: python3 -I workshop/ath_prompts/attack/qwen_rescore.py"""
import json, math, os, re
T = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "measure", "trial")
tasks = {t["id"]: t for t in json.load(open(os.path.join(T, "tasks.json")))}
rows = json.load(open(os.path.join(T, "results.json")))["rows"]
CS = {"st02", "st06"}

def nums(s): return [float(x) for x in re.findall(r"-?\d+(?:\.\d+)?", s.replace(",", ""))]
def ok(r, key_fix, rule):
    t = tasks[r["task"]]; a = "2" if (key_fix and t["id"] == "st07") else str(t["answer"])
    if t["kind"] == "py" or (t["kind"] == "num" and rule == "last" and not (key_fix and t["id"] == "st07")):
        if t["kind"] == "py" or a == str(t["answer"]): return r["ok"]
    out = r["output"]
    if t["kind"] == "num":
        n = nums(out); return bool(n) and (float(a) in n if rule == "any" else n[-1] == float(a))
    return a in out if t["id"] in CS else a.lower() in out.lower()

def sign_p(x, y):
    n, k = x + y, min(x, y)
    return min(1.0, 2 * sum(math.comb(n, j) for j in range(k + 1)) / 2 ** n) if n else 1.0

print("variant | run | informal | formal | inf-only | frm-only | exact p")
for label, key_fix, rule, drop in (("as published", False, "last", set()), ("st07 key fixed", True, "last", set()),
                                   ("key fixed, any number", True, "any", set()), ("key fixed, drop ar04 ar10", True, "last", {"ar04", "ar10"})):
    pooled_i = pooled_f = 0
    for run in ("greedy", "s0", "s1", "s2"):
        p = {}
        for r in rows:
            if r["run"] == run and r["task"] not in drop: p.setdefault(r["task"], {})[r["register"]] = ok(r, key_fix, rule)
        i = sum(v["informal"] for v in p.values()); f = sum(v["formal"] for v in p.values())
        io = sum(v["informal"] and not v["formal"] for v in p.values()); fo = sum(v["formal"] and not v["informal"] for v in p.values())
        print(f"{label} | {run} | {i}/{len(p)} | {f}/{len(p)} | {io} | {fo} | {sign_p(io, fo):.4f}")
        if run != "greedy": pooled_i += i; pooled_f += f
    print(f"{label} | sampled pooled | {pooled_i} | {pooled_f} | | |")
print("PASS")
