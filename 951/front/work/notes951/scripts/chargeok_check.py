import sys, json, itertools
from collections import Counter
PASCH = {"n": 6, "sets": [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]],
 "gates": [["or", 2, 5], ["not", 6], ["or", 0, 4], ["or", 3, 5], ["or", 1, 9], ["or", 0, 1], ["or", 3, 8], ["and", 4, 7], ["or", 2, 11], ["or", 6, 13]],
 "outs": [14, 12, 10, 15]}
def evaluate(n, gates, x):
    w = list(x)
    for g in gates:
        op = g[0]
        if op == "not": w.append(1 - w[g[1]])
        elif op == "and": w.append(w[g[1]] & w[g[2]])
        elif op == "or": w.append(w[g[1]] | w[g[2]])
        else: raise ValueError("bad gate " + str(g))
    return w
def cone(n, gates, out):
    seen, stack = set(), [out]
    while stack:
        i = stack.pop()
        if i in seen: continue
        seen.add(i)
        if i >= n:
            for j in gates[i - n][1:]: stack.append(j)
    return {i for i in seen if i >= n}
def check(c):
    n, S, gates, outs = c["n"], [set(s) for s in c["sets"]], c["gates"], c["outs"]
    s = len(gates)
    nots = [k for k, g in enumerate(gates) if g[0] == "not"]
    if len(nots) != 1: return None, "needs exactly one NOT gate (found %d)" % len(nots)
    nw = n + nots[0]
    for x in itertools.product([0, 1], repeat=n):
        w = evaluate(n, gates, x)
        for o, st in zip(outs, S):
            if w[o] != int(any(x[v] for v in st)): return None, "circuit incorrect"
    unit = [evaluate(n, gates, tuple(1 if c_ == u else 0 for c_ in range(n))) for u in range(n)]
    cones = [cone(n, gates, o) for o in outs]
    res = {}
    for variant in ("full", "cone"):
        total, detail = 0, []
        for wi, R in enumerate(S):
            best = None
            rest = [v for v in range(n) if v not in R]
            for r in range(len(rest) + 1):
                for extra in itertools.combinations(rest, r):
                    Q = R | set(extra)
                    z = evaluate(n, gates, tuple(0 if v in Q else 1 for v in range(n)))
                    if z[nw] != 1: continue
                    wires = range(n, n + s) if variant == "full" else sorted(cones[wi])
                    d = [i for i in wires if z[i] == 0 and sum(unit[u][i] for u in R) >= 2]
                    if best is None or len(d) < best[0]: best = (len(d), sorted(Q), d)
            if best is None:
                total = float("inf"); detail.append((sorted(R), None))
            else:
                total += best[0]; detail.append((sorted(R), best))
        res[variant] = (total, detail)
    base = sum(len(R) - 1 for R in S)
    return {"s": s, "base": base, "res": res}, None
def main():
    circuits = [PASCH] if sys.argv[1] == "--pasch" else [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
    nviol = 0; hist = Counter()
    for idx, c in enumerate(circuits):
        r, err = check(c)
        if err: hist['skip:' + err] += 1; continue
        cnt = Counter(i for _, b in r["res"]["full"][1] if b for i in b[2])
        dbl = sum(1 for v in cnt.values() if v >= 2)
        tf, tc = r["res"]["full"][0], r["res"]["cone"][0]
        hist['ok'] += 1; hist['dbl>0'] += dbl > 0
        hist['slack_full=%s' % (r["s"] - tf if tf != float('inf') else 'inf')] += 1
        if tf > r["s"] or tc > r["s"]:
            nviol += 1
            if nviol <= 3: print('VIOLATION', idx, r["s"], r["base"], tf, tc, json.dumps(c))
        if "-v" in sys.argv: print(idx, r["s"], r["base"], 'dbl', dbl, 'full', tf, 'cone', tc)
    print(dict(hist)); print("violations:", nviol)
if __name__ == "__main__": main()
