#!/usr/bin/env python3
"""The logical structure of cryptographic assumptions, as a finite implication graph. Standard library only.

Nodes are assumptions; an edge A -> B means "A implies B" (a published reduction, cited from memory).
Checked exactly:
  1. the equivalence classes are the strongly connected components (mutual implication);
  2. the closure: everything each assumption implies, by reachability.
No attack is computed or suggested: this is the shape of the implications, nothing more.
Edges (from memory): OWF <-> PRG (Haastad, Impagliazzo, Levin, Luby 1999);
PRG -> PRF (Goldreich, Goldwasser, Micali 1986); PRF -> MAC; OWF -> secure signatures (Naor, Yung 1989);
OWF -> commitments; OWF -> P != NP (if P = NP, inverting a one-way function would be efficient).
Run: python3 -I math/crypto/structure.py   (last line is JSON)
"""
import json, time

EDGES = [
    ("OWF", "PRG"), ("PRG", "OWF"),
    ("PRG", "PRF"),
    ("PRF", "MAC"),
    ("OWF", "Signatures"),
    ("OWF", "Commitments"),
    ("OWF", "PvsNP_separation"),
]

def scc(nodes, edges):
    """Kosaraju: strongly connected components. Iterative, so no recursion limit."""
    adj = {v: [] for v in nodes}; radj = {v: [] for v in nodes}
    for a, b in edges: adj[a].append(b); radj[b].append(a)
    order, seen = [], set()
    for s in nodes:
        if s in seen: continue
        stack = [(s, iter(adj[s]))]; seen.add(s)
        while stack:
            v, it = stack[-1]
            for w in it:
                if w not in seen: seen.add(w); stack.append((w, iter(adj[w]))); break
            else:
                order.append(v); stack.pop()
    comp, out = {}, []
    for s in reversed(order):
        if s in comp: continue
        c = []; stack = [s]; comp[s] = len(out)
        while stack:
            v = stack.pop(); c.append(v)
            for w in radj[v]:
                if w not in comp: comp[w] = len(out); stack.append(w)
        out.append(sorted(c))
    return out

def closure(nodes, edges):
    adj = {v: set() for v in nodes}
    for a, b in edges: adj[a].add(b)
    out = {}
    for s in nodes:
        seen, todo = set(), [s]
        while todo:
            v = todo.pop()
            for w in adj[v]:
                if w not in seen: seen.add(w); todo.append(w)
        out[s] = sorted(seen)
    return out

def main():
    t0 = time.time()
    nodes = sorted({a for a, _ in EDGES} | {b for _, b in EDGES})
    classes = scc(nodes, EDGES)
    equiv = sorted(c for c in classes if len(c) > 1)
    assert equiv == [["OWF", "PRG"]], f"the only mutual pair is OWF <-> PRG, got {equiv}"
    cl = closure(nodes, EDGES)
    assert "PvsNP_separation" in cl["OWF"], "OWF implies P != NP"
    assert "PvsNP_separation" not in cl["PRF"], "PRF is not recorded as implying P != NP"
    print("equivalence classes (mutual implication):", equiv)
    print("PRF implies:", cl["PRF"])
    print("OWF implies:", cl["OWF"])
    print("PASS")
    print(json.dumps({"states": len(nodes), "seconds": round(time.time() - t0, 4), "classes": len(classes), "equiv": equiv}))

if __name__ == "__main__":
    main()
