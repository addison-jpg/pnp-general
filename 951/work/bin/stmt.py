#!/usr/bin/env python3
"""Read exact step statements from the public data host (no desk lease needed).
  stmt.py L-meta-951            print the lemma record (json)
  stmt.py L-meta-951 --lean     print only formal_statement (what the theorem must prove)
  stmt.py --catalog OUT.json    write id/title/status of every lemma of every program
Static files only (data.pequalnp.com); be gentle, results are cached in work/statements/."""
import json, re, sys, os, urllib.request, concurrent.futures as cf
BASE = "https://data.pequalnp.com/"
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CACHE = os.path.join(HERE, "statements")
def get(rel):
    with urllib.request.urlopen(urllib.request.Request(BASE + rel, headers={"User-Agent": "pnp-workspace"}), timeout=60) as r:
        return json.load(r)
def overview():
    return get(get("head.json")["files"]["map"])
def program_nodes(m, key):
    p = next(p for p in m["programs"] if p["key"] == key)
    return p, get(p["file"])["nodes"]
def lemma(lid, m=None):
    k, n = re.fullmatch(r"L-([a-z]+)-(\d+)", lid).groups()
    m = m or overview()
    _, nodes = program_nodes(m, k)
    node = next(x for x in nodes if x[0] == int(n))
    d = get(f"data/lemma/{lid}.{node[3]}.json")
    os.makedirs(CACHE, exist_ok=True)
    json.dump(d, open(os.path.join(CACHE, lid + ".json"), "w"), indent=1, ensure_ascii=False)
    return d
def catalog(out):
    m = overview(); rows = []
    for p in m["programs"]:
        nodes = get(p["file"])["nodes"]
        def one(x):
            lid = f"L-{p['key']}-{x[0]}"
            try:
                d = get(f"data/lemma/{lid}.{x[3]}.json")
                return {"id": lid, "status": d.get("status"), "kind": d.get("kind"), "title": d.get("title"),
                        "depends_on": d.get("depends_on"), "len": len(d.get("formal_statement") or "")}
            except Exception as e:
                return {"id": lid, "error": str(e)}
        with cf.ThreadPoolExecutor(4) as ex:
            rows += list(ex.map(one, nodes))
    json.dump(rows, open(out, "w"), indent=0, ensure_ascii=False)
    print(len(rows), "rows ->", out)
if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "--catalog": catalog(a[1])
    elif a:
        d = lemma(a[0])
        print(d["formal_statement"] if "--lean" in a else json.dumps(d, indent=1, ensure_ascii=False))
    else: print(__doc__)
