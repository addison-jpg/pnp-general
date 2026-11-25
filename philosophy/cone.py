#!/usr/bin/env python3
"""Cone against disk: when does a hub stop being critical? Exhaustive over every labelled base graph on up to 6 vertices.

The cone over a base graph G adds one apex joined to every vertex of G, and one triangle {apex, u, v} for each edge uv of G.
Facts checked on every G (nothing sampled):
  1. The apex is a cut vertex of the cone exactly when G is disconnected (G with 2 or more vertices).
  2. A spoke (apex, v) is a bridge exactly when v is isolated in G.
  3. The cone is a disk (every vertex of G in a triangle, every edge in 1 or 2 triangles, every vertex link one path
     or one cycle, Euler characteristic 1, one boundary circle) exactly when G is one path or one cycle.
     The apex is INSIDE the disk exactly when G is a cycle (its link is the whole cycle G); for a path it is on the edge.
  4. The fewest edges to add to G so that the apex is no longer a cut vertex is (number of components of G) - 1.
Then the repository itself is measured: the base is the universe map of core/universes/network.py (a universe is a
field in the centre store; an edge means a record of one cites evidence in the other), and the apex is big.ath.
Readings (Lacan, Deleuze and Guattari, Fisher) are in philosophy/PSYCHOSIS.md section 5 and are analogy.
Run: python3 -I philosophy/cone.py        (last line is JSON for the board runner)
"""
import glob, itertools, json, os, sys, time

def components(n, edges):
    parent = list(range(n))
    def find(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for a, b in edges: parent[find(a)] = find(b)
    return len({find(v) for v in range(n)})

def connected_without(n, edges, drop_vertex=None, drop_edge=None):
    keep = [v for v in range(n) if v != drop_vertex]
    if not keep: return True
    idx = {v: i for i, v in enumerate(keep)}
    es = [(idx[a], idx[b]) for a, b in edges if a != drop_vertex and b != drop_vertex and (a, b) != drop_edge]
    return components(len(keep), es) == 1

def is_cycle(n, edges):
    deg = [0] * n
    for a, b in edges: deg[a] += 1; deg[b] += 1
    return n >= 3 and all(d == 2 for d in deg) and components(n, edges) == 1

def is_disk(n, edges):
    """The cone's 2-complex: vertices 0..n-1 plus apex n; triangles {n, u, v} for uv in edges."""
    A = n; tris = [(A, a, b) for a, b in edges]
    if not tris or any(all(v not in e for e in edges) for v in range(n)): return False   # a dangling spoke is not a disk
    count = {}
    for t in tris:
        for e in itertools.combinations(sorted(t), 2): count[e] = count.get(e, 0) + 1
    if any(c > 2 for c in count.values()): return False
    for v in range(n + 1):  # link of v: edges opposite v in triangles containing v
        link = [tuple(sorted(x for x in t if x != v)) for t in tris if v in t]
        if not link: continue
        verts = sorted({x for e in link for x in e}); ix = {x: i for i, x in enumerate(verts)}
        deg = [0] * len(verts)
        for a, b in link: deg[ix[a]] += 1; deg[ix[b]] += 1
        if components(len(verts), [(ix[a], ix[b]) for a, b in link]) != 1 or any(d > 2 for d in deg): return False
    V = len({x for t in tris for x in t}); E = len(count); F = len(tris)
    boundary = [e for e, c in count.items() if c == 1]
    bverts = sorted({x for e in boundary for x in e}); bx = {x: i for i, x in enumerate(bverts)}
    one_circle = bool(boundary) and is_cycle(len(bverts), [(bx[a], bx[b]) for a, b in boundary])
    return V - E + F == 1 and one_circle

def main():
    t0 = time.time(); states = 0; counts = {}
    for n in range(1, 7):
        pairs = list(itertools.combinations(range(n), 2)); c = {"bases": 0, "apex_critical": 0, "disks": 0}
        for mask in range(1 << len(pairs)):
            G = [p for k, p in enumerate(pairs) if mask >> k & 1]; states += 1; c["bases"] += 1
            cone = G + [(v, n) for v in range(n)]
            comp = components(n, G)
            apex_cut = n >= 2 and not connected_without(n + 1, cone, drop_vertex=n)
            assert apex_cut == (n >= 2 and comp > 1), "fact 1"
            deg = [0] * n
            for a, b in G: deg[a] += 1; deg[b] += 1
            for v in range(n):
                bridge = not connected_without(n + 1, cone, drop_edge=(v, n))
                assert bridge == (deg[v] == 0), "fact 2"
            disk = is_disk(n, G)
            path = n >= 2 and len(G) == n - 1 and comp == 1 and max(deg) <= 2
            assert disk == (path or is_cycle(n, G)), "fact 3"
            if disk: c["apex_inside"] = c.get("apex_inside", 0) + is_cycle(n, G)
            # fact 4: (comp - 1) added edges suffice (join components in a chain) and fewer do not (each edge joins at most two)
            best = None
            for k in range(0, comp):
                for add in itertools.combinations([p for p in pairs if p not in G], k):
                    if components(n, G + list(add)) == 1: best = k; break
                if best is not None: break
            assert best == comp - 1, "fact 4"
            c["apex_critical"] += apex_cut; c["disks"] += disk
        counts[n] = c
        print(f"n={n}: {c['bases']} base graphs; apex critical in {c['apex_critical']}; cone is a disk in {c['disks']}, apex inside in {c.get('apex_inside', 0)}")
    # the repository: apex big.ath over the universe map
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, root); os.chdir(root)
    import center
    recs = [json.loads(l) for f in sorted(glob.glob("center/shards/*.jsonl")) for l in open(f, encoding="utf-8") if l.strip()]
    nodes = sorted({r["program"] for r in recs if r.get("program") and r["program"] != "other"})
    ix = {v: i for i, v in enumerate(nodes)}; E = set()
    for r in recs:
        a = r.get("program")
        if a not in ix: continue
        for ev in r.get("evidence") or []:
            b = center.program(str(ev).split("::")[0])
            if b in ix and b != a: E.add(tuple(sorted((ix[a], ix[b]))))
    n, comp = len(nodes), components(len(nodes), list(E))
    deg = [0] * n
    for a, b in E: deg[a] += 1; deg[b] += 1
    iso = [nodes[v] for v in range(n) if deg[v] == 0]
    print(f"repository: big.ath over {n} universes, {len(E)} lateral links, {comp} components, {len(iso)} isolated")
    print(f"  apex critical: {comp > 1}; spokes that are bridges: {len(iso)}; fewest lateral links to make the apex not critical: {comp - 1}")
    print(f"  a disk with big.ath inside needs the base to be one ring through all {n} universes: {n} links; {len(E)} exist now")
    print("facts 1-4 hold on every base graph with up to 6 vertices")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2), "disks": [counts[k]["disks"] for k in counts],
                      "repo": {"universes": n, "lateral": len(E), "components": comp, "isolated": len(iso), "links_to_free_apex": comp - 1}}))

if __name__ == "__main__":
    main()
