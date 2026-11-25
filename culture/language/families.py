#!/usr/bin/env python3
"""A language family as a rooted tree, checked exactly. Data FROM MEMORY (not pulled: Glottolog and Wiktionary
are not reachable from this container); the checks are about shape, not about the truth of the branches.

  1. The tree is rooted, connected, and every node except the root has exactly one parent (a tree, not a DAG).
  2. The number of nodes is one more than the number of edges (n - 1 edges for n nodes).
  3. Every language is reachable from the root.
  4. The languages (leaves) are the attested ones listed below; the branch count is exact.
Run: python3 -I culture/language/families.py   (last line is JSON)
"""
import json, time

# parent -> children, Indo-European, a coarse tree from memory (cited from memory; subject to a data pull)
TREE = {
    "Proto-Indo-European": ["Germanic", "Romance", "Slavic", "Indo-Iranian", "Hellenic", "Celtic", "Baltic", "Albanian", "Armenian"],
    "Germanic": ["English", "German", "Swedish"],
    "Romance": ["French", "Spanish", "Italian"],
    "Slavic": ["Russian", "Polish"],
    "Indo-Iranian": ["Hindi", "Persian"],
    "Hellenic": ["Greek"],
    "Celtic": ["Irish"],
    "Baltic": ["Lithuanian"],
}

def main():
    t0 = time.time(); nodes = set(TREE); children = set()
    for p, cs in TREE.items():
        for c in cs: nodes.add(c); children.add(c)
    root = [n for n in TREE if n not in children]
    assert root == ["Proto-Indo-European"], "exactly one root"
    parent = {}
    for p, cs in TREE.items():
        for c in cs:
            assert c not in parent, f"{c} has two parents"
            parent[c] = p
    edges = sum(len(cs) for cs in TREE.values())
    assert len(nodes) == edges + 1, "n nodes, n - 1 edges"
    seen = set(); todo = list(root)
    while todo:
        v = todo.pop()
        if v in seen: continue
        seen.add(v); todo.extend(TREE.get(v, []))
    assert seen == nodes, "every language reachable from the root"
    leaves = sorted(n for n in nodes if n not in TREE)
    branches = sorted(TREE[root[0]])
    assert len(branches) == 9
    print(f"{len(nodes)} nodes, {edges} edges, one root, a tree: PASS")
    print("branches of the root:", len(branches), "|", leaves and f"{len(leaves)} leaves")
    print("PASS")
    print(json.dumps({"states": len(nodes), "seconds": round(time.time() - t0, 3), "nodes": len(nodes), "edges": edges, "root_branches": len(branches), "leaves": len(leaves)}))

if __name__ == "__main__":
    main()
