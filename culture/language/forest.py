#!/usr/bin/env python3
"""Check a language forest from a CSV of any size. Standard library only.

Input: culture/language/data/languages.csv (or a path given as the first argument), columns:
    id,name,parent,region
  id: a unique code (for example an ISO 639-3 code); parent: the id of the parent node, empty for a root.
Checks (exact):
  1. every id is unique, and every parent id is an id in the file;
  2. no cycles: each node reaches a root by following parents;
  3. one family per root (each root starts one tree); the families are counted exactly;
  4. counts printed per region, so a sample's bias is visible rather than hidden.
With no file present it says so and exits 0 (nothing to check yet).
Run: python3 -I culture/language/forest.py [path]   (last line is JSON)
"""
import csv, json, os, sys, time, collections

ROOT = os.path.dirname(os.path.abspath(__file__))
DEFAULT = os.path.join(ROOT, "data", "languages.csv")

def check(rows):
    ids = [r["id"] for r in rows]
    assert len(ids) == len(set(ids)), "ids must be unique"
    parent = {r["id"]: (r["parent"] or None) for r in rows}
    for i, p in parent.items():
        assert p is None or p in parent, f"{i}: parent {p} is not in the file"
    roots = [i for i, p in parent.items() if p is None]
    for i in parent:
        seen = set(); v = i
        while parent[v] is not None:
            assert v not in seen, f"cycle through {v}"
            seen.add(v); v = parent[v]
    return roots, parent

def main(path):
    t0 = time.time()
    if not os.path.exists(path):
        print(f"NOT CHECKED: no file at {os.path.relpath(path, ROOT)}. Add the data and rerun; no PASS without data.")
        print(json.dumps({"states": 0, "seconds": 0, "rows": 0, "checked": False})); return 0
    rows = list(csv.DictReader(open(path, encoding="utf-8")))
    roots, parent = check(rows)
    by_region = collections.Counter(r["region"] or "unknown" for r in rows)
    print(f"{len(rows)} languages, {len(roots)} families (roots), every node reaches its root: PASS")
    for reg, n in by_region.most_common():
        print(f"  {reg}: {n}")
    print("PASS")
    print(json.dumps({"states": len(rows), "seconds": round(time.time() - t0, 3), "rows": len(rows), "families": len(roots)}))
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else DEFAULT))
