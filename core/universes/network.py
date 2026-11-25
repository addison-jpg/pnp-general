#!/usr/bin/env python3
"""Universes as neurons: the network level of biology/brain/ applied to the repository's own map.

Each program (field) in the centre is a node, a "universe". There is a directed edge A -> B when a record of A
cites evidence that lives in B: A's results lean on B's, like a synapse from B onto A's work.
On that directed graph this computes the same quantities biology/brain/network computes for neurons: connectivity,
critical edges (a connection whose loss splits the map), directed cliques (directed simplices) and the Betti
numbers of the directed flag complex over GF(2). Exact; recomputed from center/shards each run.
Run: python3 -I center.py && python3 -I core/universes/network.py
"""
import glob, itertools, json, os, sys
sys.path.insert(0, os.getcwd())
import center

recs = [json.loads(l) for f in sorted(glob.glob("center/shards/*.jsonl")) for l in open(f, encoding="utf-8")]
def prog_of(path): p = center.program(path); return p if p != "other" else None
nodes = sorted({r["program"] for r in recs if r.get("program") and r["program"] != "other"})
E = set()
for r in recs:
    a = r.get("program")
    if a not in nodes: continue
    for ev in r.get("evidence", []) or []:
        b = prog_of(ev.split("::")[0])
        if b in nodes and b != a: E.add((a, b))
idx = {v: i for i, v in enumerate(nodes)}; n = len(nodes); Ei = {(idx[a], idx[b]) for a, b in E}

def weakly_connected(nodeset, edges):
    if not nodeset: return True
    adj = {v: set() for v in nodeset}
    for a, b in edges: adj[a].add(b); adj[b].add(a)
    start = next(iter(nodeset)); seen = {start}; todo = [start]
    while todo:
        v = todo.pop()
        for w in adj[v] - seen: seen.add(w); todo.append(w)
    return seen == set(nodeset)

active = {v for e in Ei for v in e}
conn = weakly_connected(active, Ei)
critical = [e for e in Ei if not weakly_connected(active, Ei - {e})]

def simplices(nn, edges):
    S = [[(v,) for v in range(nn)]]
    while True:
        nxt = [s + (v,) for s in S[-1] for v in range(nn) if v not in s and all((u, v) in edges for u in s)]
        if not nxt: return S
        S.append(nxt)
def rank2(rows):
    piv = {}; r = 0
    for x in rows:
        while x:
            h = x.bit_length() - 1
            if h in piv: x ^= piv[h]
            else: piv[h] = x; r += 1; break
    return r
S = simplices(n, Ei)
ranks = [0]
for k in range(1, len(S)):
    pos = {s: i for i, s in enumerate(S[k - 1])}
    ranks.append(rank2([sum(1 << pos[s[:i] + s[i + 1:]] for i in range(len(s))) for s in S[k]]))
ranks.append(0)
betti = [len(S[k]) - ranks[k] - ranks[k + 1] for k in range(len(S))]
euler = sum((-1) ** k * len(S[k]) for k in range(len(S)))
assert euler == sum((-1) ** k * b for k, b in enumerate(betti)), "Euler-Poincare fails"

indeg = {v: 0 for v in nodes}; outdeg = {v: 0 for v in nodes}
for a, b in E: outdeg[a] += 1; indeg[b] += 1
print(f"universes (programs): {n}; connections: {len(E)}; connected (among the {len(active)} with any link): {conn}")
print("isolated universes (no link in or out):", sorted(set(nodes) - {nodes[v] for v in active}))
print("critical connections (each one's loss splits the map):", sorted(f"{nodes[a]}->{nodes[b]}" for a, b in critical))
print("directed simplices by dimension:", [len(s) for s in S])
print("Betti numbers (GF(2)):", betti, "; Euler characteristic", euler, "= alternating sum of Betti numbers")
print("most relied on (in-degree):", sorted(indeg.items(), key=lambda x: -x[1])[:5])
print("relies on the most (out-degree):", sorted(outdeg.items(), key=lambda x: -x[1])[:5])
print("PASS")
print(json.dumps({"states": n + len(E), "nodes": n, "edges": len(E), "betti": betti}))
