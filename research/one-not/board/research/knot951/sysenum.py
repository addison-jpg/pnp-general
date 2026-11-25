"""Enumerate (1,1)-disjoint systems (linear hypergraphs, |S|>=2, no isolated point) on exactly n points up to iso."""
import itertools, sys, json
def systems(n, minsize=2, need3=True, connected=True, maxbase=None):
    cand = [frozenset(c) for z in range(minsize, n + 1) for c in itertools.combinations(range(n), z)]
    perms = list(itertools.permutations(range(n)))
    seen, out = set(), []
    def canon(sys_):
        best = None
        inv = {v: tuple(sorted(len(S) for S in sys_ if v in S)) for v in range(n)}
        order = sorted(range(n), key=lambda v: inv[v])        # position -> old point, sorted by invariant
        cls = [inv[v] for v in order]
        for q in perms:
            if any(cls[q[i]] != cls[i] for i in range(n)): continue   # q permutes positions inside classes
            p = [0] * n
            for i, v in enumerate(order): p[v] = q[i]
            t = tuple(sorted(tuple(sorted(p[v] for v in S)) for S in sys_))
            if best is None or t < best: best = t
        return best
    def rec(i, cur, b):
        if cur:
            yield list(cur)
        for j in range(i, len(cand)):
            S = cand[j]
            if maxbase is not None and b + len(S) - 1 > maxbase: continue
            if all(len(S & T) <= 1 for T in cur):
                cur.append(S); yield from rec(j + 1, cur, b + len(S) - 1); cur.pop()
    for sys_ in rec(0, [], 0):
        if set().union(*sys_) != set(range(n)): continue
        if need3 and all(len(S) == 2 for S in sys_): continue
        if connected:
            comp = set(sys_[0]); ch = True
            while ch:
                ch = False
                for S in sys_:
                    if S & comp and not S <= comp: comp |= S; ch = True
            if len(comp) < n: continue
        c = canon(sys_)
        if c not in seen:
            seen.add(c); out.append([list(S) for S in c])
    return out
if __name__ == '__main__':
    n = int(sys.argv[1]); mb = int(sys.argv[2]) if len(sys.argv) > 2 else None
    ms = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    L = systems(n, maxbase=mb, minsize=ms)
    json.dump(L, open('/home/user/ku951/sys_n%d_ms%d.json' % (n, ms), 'w'))
    from collections import Counter
    print(n, len(L), sorted(Counter(sum(len(S) - 1 for S in s) for s in L).items()))
