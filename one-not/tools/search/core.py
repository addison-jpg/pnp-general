"""One simple data structure for the outward search: a circuit is a dict
{"n": int, "sets": [[int]], "gates": [[op, a, b?]], "outs": [int]}; wire i < n is input i, wire n + k is gate k.
Truth tables are Python ints with one bit per input vector. Serves README items D5, D8, D9."""
import itertools, functools

def tables(n, G):
    N = 1 << n; M = (1 << N) - 1; w = []
    for i in range(n):
        t = 0
        for x in range(N):
            if x >> i & 1: t |= 1 << x
        w.append(t)
    for g in G:
        w.append(M ^ w[g[1]] if g[0] == 'not' else (w[g[1]] & w[g[2]] if g[0] == 'and' else w[g[1]] | w[g[2]]))
    return w

def correct(c, w=None):
    w = w or tables(c['n'], c['gates'])
    for R, o in zip(c['sets'], c['outs']):
        t = 0
        for u in R: t |= w[u]
        if w[o] != t: return False
    return True

def nots(c): return sum(g[0] == 'not' for g in c['gates'])
def base(c, Q=0): return sum(len(R) - 1 for R in c['sets'] if not any(Q >> u & 1 for u in R))

@functools.lru_cache(maxsize=None)
def _zeros(n, R, Q):
    rest = [v for v in range(n) if v not in R and not Q >> v & 1]
    return tuple(Q | sum(1 << v for v in Zs) for r in range(len(rest) + 1) for Zs in itertools.combinations(rest, r))

def witness(c, Q=0, w=None, any_gate=True):
    """Gates g with g(Z) = 0 and g = 1 at two atoms of a set avoiding Q, Z a zero point of it containing Q."""
    n = c['n']; w = w or tables(n, c['gates']); out = set()
    alive = [tuple(R) for R in c['sets'] if not any(Q >> u & 1 for u in R)]
    for k, g in enumerate(c['gates']):
        if not any_gate and g[0] != 'or': continue
        t = w[n + k]
        for R in alive:
            if any((not t >> Z & 1) and sum(t >> (Z | 1 << u) & 1 for u in R) >= 2 for Z in _zeros(n, R, Q)):
                out.add(k); break
    return out

def slack(c, Q=0, w=None, any_gate=True): return len(witness(c, Q, w, any_gate)) - base(c, Q)

def alive_points(c, Q): return sorted({u for R in c['sets'] if not any(Q >> v & 1 for v in R) for u in R})

def prune(c):
    """Drop gates no output reads; returns a new circuit."""
    n, G = c['n'], c['gates']; keep = set(); st = [o for o in c['outs'] if o >= n]
    while st:
        x = st.pop()
        if x in keep: continue
        keep.add(x); st += [a for a in G[x - n][1:] if a >= n]
    order = sorted(keep); pos = {x: n + i for i, x in enumerate(order)}
    f = lambda a: a if a < n else pos[a]
    return {"n": n, "sets": c['sets'], "gates": [[G[x - n][0]] + [f(a) for a in G[x - n][1:]] for x in order], "outs": [f(o) for o in c['outs']]}
