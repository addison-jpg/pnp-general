"""Where can a B charge go? Discovery survey (not proof authority).
For each correct one-NOT circuit with a set |S| >= 4: demand(w) = #3rd+ merge gates of w (canonical z_S, as check_charge).
Supports tried (set w may put charge only on): A = its own 3rd+ merges; B = all its merge gates; C = gates in cone(out_w);
D = gates in cone(out_w) that are not among the first two merges of any set. Feasible iff max flow (gates cap 1) = total demand.
Usage: python3 -I support_survey.py <file.json|file.jsonl> ...  -> per-circuit lines + summary (JSON on last line)."""
import json, sys, itertools
import networkx as nx
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from check_charge import evaluate

def merges_of(c):
    n, out = c["n"], {}
    for w, S in enumerate(c["sets"]):
        z = [0 if v in S else 1 for v in range(n)]; wz = evaluate(c, z)
        at = {u: evaluate(c, [1 if v == u else z[v] for v in range(n)]) for u in S}
        par = {u: u for u in S}
        def f(u):
            while par[u] != u: u = par[u]
            return u
        M = []
        for i in range(n, n + len(c["gates"])):
            if wz[i]: continue
            r = sorted({f(u) for u in S if at[u][i]})
            if len(r) >= 2: M.append(i); par[r[-1]] = r[0]
        out[w] = M
    return out

def cone(c, o):
    n, seen, st = c["n"], set(), [o]
    while st:
        i = st.pop()
        if i < n or i in seen: continue
        seen.add(i); st.extend(c["gates"][i - n][1:])
    return seen

def correct(c):
    n = c["n"]
    if n > 18: return None  # n <= 18 checked exhaustively (was 14; Research 09:43 found 6 circuits with n = 15..18)
    return all(evaluate(c, x)[c["outs"][w]] == int(any(x[u] for u in S))
               for x in itertools.product([0, 1], repeat=n) for w, S in enumerate(c["sets"]))

def feasible(demand, support):
    G = nx.DiGraph(); tot = 0
    for w, d in demand.items():
        if d == 0: continue
        tot += d; G.add_edge("s", ("w", w), capacity=d)
        for g in support[w]: G.add_edge(("w", w), ("g", g), capacity=1); G.add_edge(("g", g), "t", capacity=1)
    if tot == 0: return True
    if "t" not in G: return False
    return nx.maximum_flow_value(G, "s", "t") >= tot

def survey(c):
    if sum(g[0] == "not" for g in c["gates"]) != 1 or not any(len(S) >= 4 for S in c["sets"]): return None
    ok = correct(c)
    if ok is False: return {"skip": "incorrect"}
    M = merges_of(c); big = [w for w, S in enumerate(c["sets"]) if len(S) >= 4]
    demand = {w: len(M[w][2:]) for w in big}
    first2 = set().union(*[set(M[w][:2]) for w in M])
    cones = {w: cone(c, c["outs"][w]) for w in big}
    sup = {"A": {w: set(M[w][2:]) for w in big}, "B": {w: set(M[w]) for w in big},
           "C": cones, "D": {w: cones[w] - first2 for w in big}}
    return {"demand": sum(demand.values()), **{k: feasible(demand, s) for k, s in sup.items()}}

def load(path):
    if path.endswith(".jsonl"):
        for line in open(path):
            line = line.strip()
            if line:
                try: d = json.loads(line)
                except Exception: continue
                if isinstance(d, dict): yield d.get("circuit", d)
    else:
        try: d = json.load(open(path))
        except Exception: return
        items = d if isinstance(d, list) else [d]
        for it in items:
            if isinstance(it, dict): yield it.get("circuit", it)

if __name__ == "__main__":
    tot = {"circuits": 0, "with_demand": 0, "A": 0, "B": 0, "C": 0, "D": 0, "fail_examples": {"A": [], "B": [], "C": [], "D": []}}
    for p in sys.argv[1:]:
        for k, c in enumerate(load(p)):
            if not isinstance(c, dict) or "gates" not in c: continue
            try: r = survey(c)
            except Exception as e: r = {"skip": repr(e)[:60]}
            if not r or "skip" in r: continue
            tot["circuits"] += 1
            if r["demand"]: tot["with_demand"] += 1
            for key in "ABCD":
                if r[key]: tot[key] += 1
                elif len(tot["fail_examples"][key]) < 5: tot["fail_examples"][key].append(f"{p}#{k}")
            print(p, k, r)
    print(json.dumps(tot))
