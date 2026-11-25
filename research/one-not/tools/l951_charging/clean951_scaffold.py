# build_clean (helper tooling, not a proof): ov951.build + NOT (gate p) in an output cone + CLEAN:
# every gate wire is non-constant and differs (as a function on all 2^n rows) from every other wire, inputs included.
# Same return values as ov951.build: (cl, SEL, O).
import types, itertools
def _load():
    src = open('research/tools/l951_charging/ov951.py').read().split('random.seed(')[0].replace('return cl,SEL,O', 'return cl,SEL,O,W')
    m = types.ModuleType('ov951_w'); exec(src, m.__dict__); return m
ov = _load()
decode, wires = ov.decode, ov.wires
def build_clean(n, sets, s, p, blocks):
    cl, SEL, O, W = ov.build(n, sets, s, p, blocks)
    top = [max(abs(l) for c in cl for l in c)]
    def nv(): top[0] += 1; return top[0]
    R = 1 << n
    # live NOT (as live951)
    c = [nv() for _ in range(s)]
    for k in range(s):
        w = n + k; reasons = [O[i][w] for i in range(len(sets))]
        for j in range(k + 1, s):
            A, B, _ = SEL[j]; u = nv(); reasons.append(u)
            cl.append([-u, c[j]]); cl.append([-u, A[w], B[w]] if j != p else [-u, A[w]])
        cl.append([-c[k]] + reasons)
    cl.append([c[p]])
    # non-constant gates
    for k in range(s):
        cl.append([W[(n + k, r)] for r in range(R)]); cl.append([-W[(n + k, r)] for r in range(R)])
    # gate differs from every input wire: some row where W != x_i
    for k in range(s):
        for i in range(n):
            cl.append([(-W[(n + k, r)] if (r >> i) & 1 else W[(n + k, r)]) for r in range(R)])
    # gates pairwise different: some row r with W_k xor W_l
    for k, l in itertools.combinations(range(s), 2):
        ds = []
        for r in range(R):
            d = nv(); ds.append(d); a, b = W[(n + k, r)], W[(n + l, r)]
            cl += [[-d, a, b], [-d, -a, -b]]
        cl.append(ds)
    return cl, SEL, O
