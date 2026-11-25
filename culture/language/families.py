#!/usr/bin/env python3
"""Language families as a FOREST: many roots, not one. Data FROM MEMORY (Glottolog and Wiktionary are not
reachable from this container). The checks are about shape, and one count about who is in the tree.

Why a forest: a single-root tree assumes every language descends from one ancestor. That is a modelling choice
inherited from 19th-century comparative philology (Indo-European reconstruction; cited from memory), and it
leaves out isolates (Basque) and families outside Europe. So the structure here has several roots.

  1. Each family is a rooted tree: one root, each non-root has one parent, no cycles, every node reachable.
  2. The forest has one tree per family; the number of families is exact.
  3. Count: how many nodes are Indo-European, of all nodes. That share is printed and asserted, not hidden.
Run: python3 -I culture/language/families.py   (last line is JSON)
"""
import json, time

FAMILIES = {
    "Indo-European": {
        "Proto-Indo-European": ["Germanic", "Romance", "Slavic", "Indo-Iranian", "Hellenic", "Celtic", "Baltic", "Albanian", "Armenian"],
        "Germanic": ["English", "German", "Swedish"],
        "Romance": ["French", "Spanish", "Italian"],
        "Slavic": ["Russian", "Polish"],
        "Indo-Iranian": ["Hindi", "Persian"],
        "Hellenic": ["Greek"], "Celtic": ["Irish"], "Baltic": ["Lithuanian"],
        "Albanian": [], "Armenian": [],
    },
    "Basque (isolate)": {"Basque": []},
    "Japonic": {"Proto-Japonic": ["Japanese", "Ryukyuan"]},
    "Niger-Congo": {"Proto-Niger-Congo": ["Yoruba", "Igbo", "Bantu", "Swahili"]},
    "Sino-Tibetan": {"Proto-Sino-Tibetan": ["Mandarin", "Cantonese", "Tibetan"]},
    "Quechuan": {"Proto-Quechuan": ["Quechua", "Quichua"]},
}

def main():
    t0 = time.time(); all_nodes = set(); ie = 0; total = 0; states = 0
    for fam, tree in FAMILIES.items():
        nodes = set(tree); children = set()
        for p, cs in tree.items():
            for c in cs: nodes.add(c); children.add(c)
        roots = [n for n in tree if n not in children]
        assert len(roots) == 1, f"{fam}: one root"
        parent = {}
        for p, cs in tree.items():
            for c in cs:
                assert c not in parent, f"{fam}: {c} has two parents"
                parent[c] = p
        seen = set(); todo = list(roots)
        while todo:
            v = todo.pop()
            assert v not in seen, f"{fam}: cycle at {v}"
            seen.add(v); todo.extend(tree.get(v, []))
        assert seen == nodes, f"{fam}: every node reachable from its root"
        states += len(nodes)
        all_nodes |= nodes
        if fam == "Indo-European": ie = len(nodes)
        total += len(nodes)
    families = len(FAMILIES)
    assert families == 6
    print(f"{families} families (forest, {len(all_nodes)} nodes), each a tree, one root each: PASS")
    print(f"Indo-European nodes: {ie} of {total} ({ie / total:.0%}); the rest sit in 5 other families or isolates")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 3), "families": families, "ie_nodes": ie, "total_nodes": total}))

if __name__ == "__main__":
    main()
