"""Referee-B pre-check (discovery tool, NOT proof authority): test a candidate charging of 3rd+ merge gates.

Independent of research/tools/w951 on purpose (a second implementation to cross-check it). Definitions as in
research/tools/w951/systems.py system/merges: for set S, z = 0 exactly on S, atoms z + e_u; walking gates in order,
a gate that is 0 at z and joins two union-find blocks of {u in S : atom u makes the gate 1} is a merge gate.

Input JSON: {"circuit": {"n", "sets", "gates": [[op, a(, b)]], "outs"},
             "charge": {"<gate>": {"<set index>": weight}},          # candidate rule output
             "demand": {"<set index>": number}}                       # optional; default = #3rd+ merges, |S|>=4 only
Output JSON (stdout): circuit_ok, merges per set, loads per gate, coverage per set, violations, verdict PASS/FAIL.
Usage: python3 -I check_charge.py candidate.json [--out verdict.json]
"""
import itertools, json, sys
from fractions import Fraction as F

def evaluate(c, x):
    n, v = c["n"], list(x)
    for g in c["gates"]:
        a = v[g[1]]
        v.append(a & v[g[2]] if g[0] == "and" else a | v[g[2]] if g[0] == "or" else 1 - a)
    return v

def check(doc):
    c, n = doc["circuit"], doc["circuit"]["n"]
    ok = all(evaluate(c, x)[c["outs"][w]] == int(any(x[u] for u in S))
             for x in itertools.product([0, 1], repeat=n) for w, S in enumerate(c["sets"]))
    merges = {}
    for w, S in enumerate(c["sets"]):
        z = [0 if v in S else 1 for v in range(n)]
        wz = evaluate(c, z)
        at = {u: evaluate(c, [1 if v == u else z[v] for v in range(n)]) for u in S}
        par = {u: u for u in S}
        def find(u):
            while par[u] != u: u = par[u]
            return u
        M = []
        for i in range(n, n + len(c["gates"])):
            if wz[i]: continue
            roots = sorted({find(u) for u in S if at[u][i]})
            if len(roots) >= 2:
                if len(roots) > 2: raise ValueError(f"gate {i} merges {len(roots)} blocks for set {w}")
                M.append(i); par[roots[1]] = roots[0]
        merges[w] = M
    charge = {int(g): {int(w): F(str(x)) for w, x in d.items()} for g, d in doc.get("charge", {}).items()}
    demand = {int(w): F(str(x)) for w, x in doc["demand"].items()} if "demand" in doc else \
             {w: F(len(M[2:])) for w, M in merges.items() if len(c["sets"][w]) >= 4}
    load = {g: sum(d.values()) for g, d in charge.items()}
    cover = {w: sum(charge.get(g, {}).get(w, 0) for g in charge) for w in demand}
    viol = [f"gate {g} load {l} > 1" for g, l in load.items() if l > 1]
    viol += [f"set {w} covered {cover[w]} < demand {d}" for w, d in demand.items() if cover[w] < d]
    viol += [f"charge on non-gate wire {g}" for g in charge if not n <= g < n + len(c["gates"])]
    out = {"circuit_ok": ok, "merges": merges, "third_plus": {w: M[2:] for w, M in merges.items()},
           "load": {g: str(l) for g, l in load.items()}, "coverage": {w: str(x) for w, x in cover.items()},
           "demand": {w: str(d) for w, d in demand.items()}, "violations": viol,
           "verdict": "PASS" if ok and not viol else "FAIL"}
    return out

if __name__ == "__main__":
    res = check(json.load(open(sys.argv[1])))
    s = json.dumps(res, indent=1, sort_keys=True, default=str)
    if "--out" in sys.argv: open(sys.argv[sys.argv.index("--out") + 1], "w").write(s + "\n")
    print(s)
