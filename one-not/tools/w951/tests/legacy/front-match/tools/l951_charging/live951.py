# build_live: ov951.build plus "the NOT (gate p) lies in the cone of some output" (helper tooling, not a proof).
# ov951.build only asks that some later gate reads the NOT; most circuits it returns then have the NOT feeding junk
# only (= a monotone circuit plus dead gates). c[k] <-> wire n+k is an output or read by a gate whose c is true.
import types
def _load():
    src = open('tools/l951_charging/ov951.py').read().split('random.seed(')[0]
    m = types.ModuleType('ov951_defs'); exec(src, m.__dict__); return m
ov = _load()
def build_live(n, sets, s, p, blocks):
    cl, SEL, O = ov.build(n, sets, s, p, blocks)
    top = [max(abs(l) for c in cl for l in c)]
    def nv(): top[0] += 1; return top[0]
    c = [nv() for _ in range(s)]
    for k in range(s):
        w = n + k; reasons = [O[i][w] for i in range(len(sets))]
        for j in range(k + 1, s):
            A, B, _ = SEL[j]
            u = nv(); reasons.append(u)          # u -> c[j] and (A_j or B_j selects w)
            cl.append([-u, c[j]]); cl.append([-u, A[w], B[w]] if j != p else [-u, A[w]])
        cl.append([-c[k]] + reasons)
    cl.append([c[p]])
    return cl, SEL, O
build, decode, wires = build_live, ov.decode, ov.wires
