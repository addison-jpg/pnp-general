#!/usr/bin/env python3
"""Route from programs down to memory: a minimum spanning forest of a three-layer (tripartite) graph.
Layers: programs (.ath files), evidence (files a program or record cites), memory (centre shards).
Edges: program -> evidence it names; evidence -> the shard that holds a record citing it. All weights 1.
Minimum spanning forest by Kruskal (exact). Standard library only.
Run: python3 -I workshop/route/route.py [--core]   (--core drops the culture/ superstructure; last line is JSON)
"""
import glob, json, os, re, sys, time
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

def find(p, x):
    while p[x] != x:
        p[x] = p[p[x]]; x = p[x]
    return x

def main():
    t0 = time.time()
    core = "--core" in sys.argv   # detach the culture superstructure: no culture/ programs or evidence
    edges = []
    for f in sorted(glob.glob(os.path.join(ROOT, "*.ath"))):
        pr = os.path.basename(f)
        text = open(f, encoding="utf-8", errors="replace").read()
        for ref in set(re.findall(r"([\w./-]+\.(?:py|ath|bench|json|lean|md))", text)):
            if core and ref.startswith("culture/"): continue
            if os.path.exists(os.path.join(ROOT, ref)):
                edges.append((("P", pr), ("E", ref)))
    for shard in sorted(glob.glob(os.path.join(ROOT, "center", "shards", "*.jsonl"))):
        sname = os.path.relpath(shard, ROOT)
        for line in open(shard, encoding="utf-8"):
            if not line.strip():
                continue
            for ev in json.loads(line).get("evidence") or []:
                ref = str(ev).split("::")[0]
                if core and ref.startswith("culture/"): continue
                if os.path.exists(os.path.join(ROOT, ref)):
                    edges.append((("E", ref), ("M", sname)))
    nodes = {n for e in edges for n in e}
    parent = {n: n for n in nodes}
    tree = []
    for a, b in edges:
        ra, rb = find(parent, a), find(parent, b)
        if ra != rb:
            parent[ra] = rb; tree.append((a, b))
    comps = len({find(parent, n) for n in nodes})
    count = {"P": 0, "E": 0, "M": 0}
    for n in nodes:
        count[n[0]] += 1
    routes = sorted((a, b) for a, b in tree if "P" in (a[0], b[0]))
    print(f"nodes: {count['P']} programs, {count['E']} evidence files, {count['M']} memory shards")
    print(f"minimum spanning forest: {len(tree)} edges, {comps} components, from {len(edges)} edges")
    print(f"program routes in the tree: {len(routes)}")
    for a, b in routes[:12]:
        print(f"  {a[1]} -> {b[1]}")
    ok = len(tree) == len(nodes) - comps
    print("PASS" if ok else "FAIL")
    print(json.dumps({"states": len(nodes), "seconds": round(time.time() - t0, 3), "programs": count["P"],
                      "evidence": count["E"], "shards": count["M"], "tree_edges": len(tree), "components": comps}))

if __name__ == "__main__":
    main()
