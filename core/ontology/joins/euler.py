"""Join curvature + brain: on the icospheres of biology/brain/hairy.py (subdivision 0..3) chi = 2 three ways, exact:
V - E + F and the deficit sum / 2 pi (physics/curvature/check.py), and the Banchoff index sum with integer heights
(hairy.py's link rule) for 3 fixed vertex orders. Exhaustive over that stated set only."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); from load import load
hairy, curv = load("biology/brain/hairy.py"), load("physics/curvature/check.py")
for s in range(4):
    V, F = hairy.icosphere(s); n = len(V)
    info = curv.surface_info(n, [tuple(sorted(t)) for t in F]); assert info
    _, E, Fn, deg = info; chi = n - E + Fn
    assert chi == 2 and sum(curv.deficit(d) for d in deg) == 2 * chi
    z = {v: r for r, v in enumerate(sorted(range(n), key=lambda v: (V[v][2], v)))}    # rank by height z, ties by index
    for h in (list(range(n)), [-v for v in range(n)], [z[v] for v in range(n)]):
        tot = 0
        for v in range(n):
            sg = [h[u] > h[v] for u in hairy.link_cycle(v, F)]
            tot += 1 - sum(sg[i] != sg[i - 1] for i in range(len(sg))) // 2
        assert tot == chi
    print(f"subdivision {s}: V={n} E={E} F={Fn}, chi = 2 = deficit sum / 2 pi = index sum (3 height orders)")
print("PASS")
