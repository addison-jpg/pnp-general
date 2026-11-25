"""Join philosophy + curvature: the cone over a d-cycle (philosophy/cone.py) is a disk with the apex inside, and the
apex is a fan of d triangles; its deficit (physics/curvature/check.py) is 0 exactly when d = 6. d = 3..12."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); from load import load
cone, curv = load("philosophy/cone.py"), load("physics/curvature/check.py")
for d in range(3, 13):
    C = [(i, i + 1) for i in range(d - 1)] + [(0, d - 1)]
    assert cone.is_disk(d, C) and cone.is_cycle(d, C)             # apex inside the disk
    assert (curv.deficit(d) == 0) == (d == 6)                     # one triangle per base edge meets at the apex
print("d = 3..12: the cone over a d-cycle is a disk with the apex inside; its apex deficit (2 - d/3) pi is 0 iff d = 6"); print("PASS")
