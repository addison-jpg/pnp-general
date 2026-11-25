"""Discrete geometry simulation of a stated model. Not physics.

Model: start from the octahedron and split each triangle into four,
with new vertices at edge midpoints. Treat every face as equilateral.
A vertex of degree d then has deficit (2 - d/3) pi, as checked in
physics/curvature/check.py. A closed surface has total deficit 2 pi chi.

Horizon proxy (a stated definition only): the number of vertices with
positive deficit, called "tip" vertices. This count is not claimed to
match any physical horizon. It is a label for a combinatorial count.
"""
import json
from fractions import Fraction


def octahedron():
    faces = [(0, 2, 4), (2, 1, 4), (1, 3, 4), (3, 0, 4),
             (2, 0, 5), (1, 2, 5), (3, 1, 5), (0, 3, 5)]
    return 6, faces


def subdivide(n, faces):
    mid = {}

    def m(a, b):
        nonlocal n
        key = (min(a, b), max(a, b))
        if key not in mid:
            mid[key] = n
            n += 1
        return mid[key]

    out = []
    for a, b, c in faces:
        ab, bc, ca = m(a, b), m(b, c), m(c, a)
        out += [(a, ab, ca), (b, bc, ab), (c, ca, bc), (ab, bc, ca)]
    return n, out


def measure(n, faces):
    deg = [0] * n
    edges = set()
    for f in faces:
        for i in range(3):
            a, b = f[i], f[(i + 1) % 3]
            edges.add((min(a, b), max(a, b)))
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    deficits = [2 - Fraction(d, 3) for d in deg]  # in units of pi
    chi = n - len(edges) + len(faces)
    total = sum(deficits, Fraction(0))
    tips = sum(1 for x in deficits if x > 0)
    return chi, total, tips


def main(levels=5):
    n, faces = octahedron()
    rows = []
    for level in range(levels):
        chi, total, tips = measure(n, faces)
        assert chi == 2, chi
        assert total == 2 * chi, total  # total deficit = 2 pi chi
        rows.append({"level": level, "vertices": n, "faces": len(faces),
                     "chi": chi, "total_deficit_pi": str(total),
                     "tips": tips})
        print(f"level {level}: V={n} F={len(faces)} chi={chi} "
              f"total={total} pi tips={tips}")
        n, faces = subdivide(n, faces)
    print("Simulation of a stated model. Tip count is a proxy only.")
    print(json.dumps({"model": "octahedron midpoint subdivision",
                      "all_total_equal_2pi_chi": True, "rows": rows}))


if __name__ == "__main__":
    main()
