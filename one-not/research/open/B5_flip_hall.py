"""B5: S3(b) in Hall form on stored circuits.
C(w) = flip classes of set S_w: wire functions up to complement with |D| >= 2 at (S_w, Z) for some zero point Z of S_w,
D(g) = {u in S_w : g(Z + e_u) != g(Z)} (same definition as conjectures.py count_flip_classes, inputs included; they never qualify).
Hall: for every nonempty subfamily W, |U_{w in W} C(w)| >= sum_{w in W} (|S_w| - 1).
Usage: python3 -I B5_flip_hall.py FILE.json ...   (prints the least Hall margin per circuit)."""
import json, sys, itertools

def tables(n, G):
    N = 1 << n; M = (1 << N) - 1; w = []
    for i in range(n):
        w.append(sum(1 << x for x in range(N) if x >> i & 1))
    for g in G:
        op = g[0]
        if op == 'not': w.append(M ^ w[g[1]])
        elif op == 'and': w.append(w[g[1]] & w[g[2]])
        elif op == 'or': w.append(w[g[1]] | w[g[2]])
        else: raise ValueError(op)
    return w, M

def zeros(n, S):
    rest = [v for v in range(n) if v not in S]
    for r in range(len(rest) + 1):
        for Zs in itertools.combinations(rest, r):
            yield sum(1 << v for v in Zs)

def classes_of_set(n, S, w, M):
    """bit-parallel: diff_u has bit Z set iff Z has bit u = 0 and t(Z + e_u) != t(Z); a class qualifies iff two diff_u meet on
    the zero points of S."""
    N = 1 << n
    zero = [M ^ sum(1 << x for x in range(N) if x >> u & 1) for u in range(n)]
    zS = M
    for u in S: zS &= zero[u]
    out = set()
    for t in set(w):
        cl = min(t, M ^ t)
        if cl in out: continue
        d = [(t ^ (t >> (1 << u))) & zS for u in S]
        acc = 0; hit = False
        for x in d:
            if acc & x: hit = True; break
            acc |= x
        if hit: out.add(cl)
    return out

def correct(c, w):
    return all(w[o] == (0 if not R else __import__('functools').reduce(lambda a, b: a | b, (w[u] for u in R)))
               for R, o in zip(c['sets'], c['outs']))

def hall(c):
    n, sets = c['n'], [list(R) for R in c['sets']]
    w, M = tables(n, c['gates'])
    assert correct(c, w), "circuit not correct"
    C = [classes_of_set(n, R, w, M) for R in sets]
    worst = None
    m = len(sets)
    for mask in range(1, 1 << m):
        W = [i for i in range(m) if mask >> i & 1]
        U = set().union(*(C[i] for i in W)); need = sum(len(sets[i]) - 1 for i in W)
        mg = len(U) - need
        if worst is None or mg < worst[0]: worst = (mg, W)
    allc = set().union(*C)
    shared = sum(1 for cl in allc if sum(cl in Ci for Ci in C) >= 2)
    nn = sum(g[0] == 'not' for g in c['gates'])
    return dict(n=n, m=m, gates=len(c['gates']), nots=nn, base=sum(len(R) - 1 for R in sets),
                per_set=[len(Ci) for Ci in C], classes=len(allc), shared=shared, hall_min=worst[0], at=worst[1])

if __name__ == '__main__':
    for f in sys.argv[1:]:
        try:
            c = json.load(open(f))
            if c['n'] > 24: print(f, 'skip n =', c['n']); continue
            print(f, hall(c))
        except Exception as e:
            print(f, 'ERROR', e)
