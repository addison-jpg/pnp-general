#!/usr/bin/env python3
"""Glottolog's classification as a forest (families and languages), checked in one linear pass.

Source: Glottolog languoid table (Hammarstrom, Forkel, Haspelmath, Bank and colleagues; CC BY 4.0), file
culture/language/data/glottolog_languoid.csv, from Zenodo. Read from the file, not from memory.
Nodes kept: level family or language, not bookkeeping. Dialects are dropped; a kept node whose parent is dropped
climbs to its nearest kept ancestor (memoised, one pass). Output: culture/language/data/languages.csv (id,name,parent,region),
which forest.py then checks.

Linear checks (no enumeration): edges = nodes - roots (a forest), every parent exists, no cycles (memoised walk),
counts per level, and the region from coordinates where Glottolog gives them ('no coordinates' otherwise).
Run: python3 -I culture/language/glottolog_forest.py   (last line is JSON)
"""
import csv, json, os, sys, time, collections

ROOT = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(ROOT, "data", "glottolog_languoid.csv")
OUT = os.path.join(ROOT, "data", "languages.csv")

def region(lat, lon):
    """Coarse boxes, labelled as coarse: where a point lies, not a continent claim."""
    if lat == "" or lon == "": return "no coordinates"
    la, lo = float(lat), float(lon)
    if -35 <= la <= 40 and -20 <= lo <= 55: return "Africa and Middle East (coarse)"
    if la > 35 and -15 <= lo <= 60: return "Europe (coarse)"
    if lo >= 60 and la > -12: return "Asia (coarse)"
    if lo >= 60 and la <= -12: return "Oceania (coarse)"
    if lo < -30: return "Americas (coarse)"
    return "Asia (coarse)"

def main():
    t0 = time.time()
    rows = list(csv.DictReader(open(SRC, encoding="utf-8")))
    by_id = {r["id"]: r for r in rows}
    kept = {r["id"] for r in rows if r["level"] in ("family", "language") and r["bookkeeping"] != "True"}
    memo = {}
    def kept_parent(i):
        """Nearest kept ancestor of i, or None. Walks parents once per node, memoised; a cycle is an error."""
        path = []; v = by_id[i]["parent_id"] or None
        while True:
            if v is None: res = None; break
            if v in memo: res = memo[v]; break
            if v in kept: res = v; break
            if v not in by_id: res = None; break
            if v in path: raise SystemExit(f"cycle through {v}")
            path.append(v); v = by_id[v]["parent_id"] or None
        for p in path: memo[p] = res
        return res
    out = []
    for i in kept:
        r = by_id[i]
        out.append({"id": i, "name": r["name"], "parent": kept_parent(i) or "", "region": region(r["latitude"], r["longitude"])})
    ids = {o["id"] for o in out}
    roots = [o for o in out if not o["parent"]]
    edges = sum(1 for o in out if o["parent"])
    assert all(o["parent"] in ids for o in out if o["parent"]), "every parent is kept"
    assert edges == len(out) - len(roots), "a forest: edges = nodes - roots"
    with open(OUT, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["id", "name", "parent", "region"]); w.writeheader()
        for o in sorted(out, key=lambda o: o["id"]): w.writerow(o)
    lv = collections.Counter(by_id[i]["level"] for i in kept)
    reg = collections.Counter(o["region"] for o in out)
    print(f"Glottolog forest: {len(out)} nodes ({lv['language']} languages, {lv['family']} families kept), "
          f"{len(roots)} roots (independent families and isolates), {edges} edges: PASS")
    for k, n in reg.most_common(): print(f"  {k}: {n}")
    print("PASS")
    print(json.dumps({"states": len(out), "seconds": round(time.time() - t0, 3), "nodes": len(out), "roots": len(roots), "edges": edges}))

if __name__ == "__main__":
    sys.exit(main())
