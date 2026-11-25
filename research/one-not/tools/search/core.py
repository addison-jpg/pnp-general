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

# ---- no-rewire filter (README L2 MinCE.no_rewire; scripts in research/one-not/tools/kill_tests/rewire_r6.py, norewire_step.py) ----
def live_gates(c):
    """Set of wires (>= n) read on some path to an output."""
    n, G = c['n'], c['gates']; L = set(); st = list(c['outs'])
    while st:
        x = st.pop()
        if x < n or x in L: continue
        L.add(x); st += G[x - n][1:]
    return L

def all_read(c):
    """Every gate is on a path to an output."""
    return len(live_gates(c)) == len(c['gates'])

def topo_sort(c):
    """Re-sort gates topologically (inputs first); the circuit must be acyclic. Returns a new circuit."""
    import sys as _s; _s.setrecursionlimit(max(_s.getrecursionlimit(), 10000))
    n, G = c['n'], c['gates']; order = []; seen = set()
    def visit(x):
        if x < n or x in seen: return
        seen.add(x)
        for a in G[x - n][1:]: visit(a)
        order.append(x)
    for x in range(n, n + len(G)): visit(x)
    pos = {x: n + i for i, x in enumerate(order)}; f = lambda a: a if a < n else pos[a]
    return dict(c, gates=[[G[x - n][0]] + [f(a) for a in G[x - n][1:]] for x in order], outs=[f(o) for o in c['outs']])

def gate_saving_rewirings(c, rng=None, first=False, w=None):
    """All (gate index k, input position j, new wire f): move input j of gate k to wire f, f not a descendant of the gate
    (no cycle; f may be a later wire), keeping every output correct and leaving some gate unread. Shuffled if rng is given."""
    n, G = c['n'], c['gates']; w = w or tables(n, G); res = []; tgt = []
    for R in c['sets']:
        t = 0
        for u in R: t |= w[u]
        tgt.append(t)
    N = n + len(G); M = (1 << (1 << n)) - 1; desc = []
    for k in range(len(G)):
        d = {n + k}
        for kk in range(k + 1, len(G)):
            if any(j in d for j in G[kk][1:]): d.add(n + kk)
        desc.append(d)
    ks = list(range(len(G)))
    if rng: rng.shuffle(ks)
    for k in ks:
        g = G[k]; D = desc[k]; ds = sorted(D)
        for j in range(1, len(g)):
            fs = [f for f in range(N) if f not in D and f != g[j]]
            if rng: rng.shuffle(fs)
            for f in fs:
                G2 = [list(x) for x in G]; G2[k][j] = f
                if len(live_gates(dict(c, gates=G2))) == len(G): continue
                v = {}
                val = lambda a: v[a] if a in D else w[a]
                for x in ds:
                    h = G2[x - n]
                    v[x] = M ^ val(h[1]) if h[0] == 'not' else (val(h[1]) & val(h[2]) if h[0] == 'and' else val(h[1]) | val(h[2]))
                if all(val(o) == t for o, t in zip(c['outs'], tgt)):
                    res.append((k, j, f))
                    if first: return res
    if rng: rng.shuffle(res)
    return res

def gate_saving_rewire(c):
    """One gate-saving rewiring (k, j, f) or None. None (with all_read) = MinCE.no_rewire holds."""
    r = gate_saving_rewirings(c, first=True)
    return r[0] if r else None

def apply_rewire(c, rw):
    k, j, f = rw; G2 = [list(x) for x in c['gates']]; G2[k][j] = f
    return prune(topo_sort(dict(c, gates=G2)))

def reduce(c, rng=None, keep_not=False):
    """Prune and apply gate-saving rewirings until none is left. rng: random order; keep_not: skip rewirings after which a
    NOT gate would be unread (the result may then still admit a NOT-killing rewiring: test it with gate_saving_rewire)."""
    c = prune(c); had = nots(c)
    while True:
        rws = gate_saving_rewirings(c, rng)
        if keep_not: rws = [r for r in rws if nots(apply_rewire(c, r)) >= had]
        if not rws: return c
        c = apply_rewire(c, rws[0])

def faces_incorrect(c):
    """For a one-NOT circuit: both faces (NOT gate -> constant 0, -> constant 1) are incorrect."""
    n, G = c['n'], c['gates']; M = (1 << (1 << n)) - 1; res = []
    for const in (0, M):
        w = []
        for i in range(n):
            t = 0
            for x in range(1 << n):
                if x >> i & 1: t |= 1 << x
            w.append(t)
        for g in G: w.append(const if g[0] == 'not' else (w[g[1]] & w[g[2]] if g[0] == 'and' else w[g[1]] | w[g[2]]))
        res.append(not correct(c, w))
    return all(res)
