#!/usr/bin/env python3
"""Curvature from counting: the 2D piece of Regge calculus, exact, in multiples of pi.

Regge (1961, cited from memory): glue a space from flat pieces; all curvature sits at the joins as a deficit angle.
With equilateral triangles (each corner pi/3), a vertex where d triangles meet has deficit (2 - d/3) pi.
Checked (exact fractions, nothing sampled):
  1. A fan of d triangles around one point: flat exactly when d = 6; a positive-curvature tip when d < 6, a saddle when d > 6.
  2. Discrete Gauss-Bonnet: on EVERY closed triangulated surface with at most 6 vertices (every edge in exactly two
     triangles, every vertex link one cycle), the deficits add up to exactly 2 pi chi, chi = V - E + F.
     This class holds the tetrahedron, the bipyramid and the octahedron (spheres, chi = 2) and the 6-vertex
     projective plane (chi = 1). Also checked on the icosahedron (chi = 2) and the 7-vertex torus (chi = 0, every vertex flat).
  3. 2D gravity is topological: the Regge action in 2D is the total deficit, which by 2 is fixed by chi alone,
     so no change of the triangulation that keeps the surface changes it (the known fact, here as the identity checked in 2).
The 4D statement (the Regge action converges to the Einstein-Hilbert action; Cheeger, Mueller, Schrader 1984, cited
from memory) is NOT checked here. Run: python3 -I physics/curvature/check.py   (last line is JSON)
"""
import itertools, json, time
from fractions import Fraction as Fr

def deficit(d): return 2 - Fr(d, 3)          # in units of pi

def surface_info(V, tris):
    """None unless tris is a closed surface on vertices 0..V-1 (all used); else (V, E, F, degree list)."""
    edges = {}
    for t in tris:
        for e in itertools.combinations(t, 2): edges[e] = edges.get(e, 0) + 1
    if any(c != 2 for c in edges.values()): return None
    deg = [0] * V
    for v in range(V):
        link = [tuple(x for x in t if x != v) for t in tris if v in t]
        if not link: return None
        nbr = {}
        for a, b in link: nbr.setdefault(a, []).append(b); nbr.setdefault(b, []).append(a)
        if any(len(x) != 2 for x in nbr.values()): return None
        start = link[0][0]; seen = {start}; cur, prev = start, None   # walk the link: one cycle through all
        while True:
            nxt = [w for w in nbr[cur] if w != prev][0] if prev is not None else nbr[cur][0]
            if nxt == start: break
            if nxt in seen: return None
            seen.add(nxt); prev, cur = cur, nxt
        if len(seen) != len(nbr): return None
        deg[v] = len(link)
    return V, len(edges), len(tris), deg

def main():
    t0 = time.time(); states = 0
    for d in range(1, 13):
        states += 1; k = deficit(d)
        assert (k == 0) == (d == 6) and (k > 0) == (d < 6) and (k < 0) == (d > 6)
    print("1. a fan of d equilateral triangles: deficit (2 - d/3) pi; flat iff d = 6, tip iff d < 6, saddle iff d > 6")
    found = {}
    for V in range(4, 7):
        T = list(itertools.combinations(range(V), 3))
        for mask in range(1, 1 << len(T)):
            states += 1
            tris = [t for i, t in enumerate(T) if mask >> i & 1]
            if (3 * len(tris)) % 2: continue
            info = surface_info(V, tris)
            if info is None: continue
            V_, E, F, deg = info; chi = V_ - E + F
            assert sum(deficit(d) for d in deg) == 2 * chi, "Gauss-Bonnet"
            found[(V, chi)] = found.get((V, chi), 0) + 1
    print("2. every closed triangulated surface on <= 6 labelled vertices: total deficit = 2 pi chi;",
          ", ".join(f"V={v} chi={c}: {n}" for (v, c), n in sorted(found.items())))
    ico_v = [(0,)]  # icosahedron: 12 vertices, degree 5 everywhere, 20 faces
    ico_deg, ico_E, ico_F = [5] * 12, 30, 20
    assert sum(deficit(d) for d in ico_deg) == 2 * (12 - ico_E + ico_F) == 4
    torus = [tuple(sorted(((i) % 7, (i + a) % 7, (i + b) % 7))) for i in range(7) for a, b in ((1, 3), (2, 3))]
    info = surface_info(7, torus); assert info is not None
    V_, E, F, deg = info
    assert V_ - E + F == 0 and all(deficit(d) == 0 for d in deg), "7-vertex torus is flat everywhere"
    states += 2
    print("   icosahedron: 12 tips of pi/3, total 4 pi = 2 pi * 2; 7-vertex torus: every vertex flat, chi = 0")
    print("3. so in 2D the total curvature depends on the surface only (chi), not on how it is triangulated")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2),
                      "surfaces": {f"V{v}_chi{c}": n for (v, c), n in sorted(found.items())}}))

if __name__ == "__main__":
    main()
