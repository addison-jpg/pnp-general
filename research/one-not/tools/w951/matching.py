"""Shared capacitated bipartite matching (pure Python, no dependencies).

One max-flow (Dinic) behind every "sets -> gates" matching check, replacing the hand-copied
augmenting-path `bmatch` helpers and the scipy LP load checks of the notes951 scripts.

Data shape (same as the scripts): vertex i (a set / world / test system) may use the items
T[i] (gate ids, any hashable), needs d[i] of them (usually |S_i| - 1), item a has c[a] copies.

    bmatch(T, d, c=None)         vertex i may take several copies of one item
    simple_bmatch(T, d, c=None)  vertex i takes each item at most once
    frac_feasible_half(T, d)     the 1/2-1/2 two-system load check (was an LP)
    hall_check(T, d, c, simple)  brute force over all vertex subsets (tests only)

Capacities `c`: None (all 1), an int (same for all items), or a dict item -> int
(items missing from the dict get 1).
"""
from collections import deque
from itertools import combinations

__all__ = ['bmatch', 'simple_bmatch', 'frac_feasible_half', 'hall_check', 'max_matched']

_INF = float('inf')


def _cap(c):
    if c is None:
        return lambda a: 1
    if isinstance(c, int):
        return lambda a: c
    return lambda a: c.get(a, 1)


def _norm(T, d, c):
    # Sets are deduplicated; items are kept in a deterministic first-seen order.
    Ts = [list(dict.fromkeys(t)) for t in T]
    d = list(d)
    if len(Ts) != len(d):
        raise ValueError('T and d must have the same length')
    cap = _cap(c)
    items = list(dict.fromkeys(a for t in Ts for a in t))
    cs = {a: cap(a) for a in items}
    if any(x < 0 for x in d) or any(x < 0 for x in cs.values()):
        raise ValueError('demands and capacities must be >= 0')
    return Ts, d, items, cs


class _Flow:
    """Dinic max-flow on an adjacency-list residual graph (iterative, no recursion limit)."""

    def __init__(self, n):
        self.n = n
        self.adj = [[] for _ in range(n)]
        self.to = []
        self.cap = []

    def add(self, u, v, cap):
        """Add edge u -> v; returns its edge id (the reverse edge is id ^ 1)."""
        self.adj[u].append(len(self.to)); self.to.append(v); self.cap.append(cap)
        self.adj[v].append(len(self.to)); self.to.append(u); self.cap.append(0)
        return len(self.to) - 2

    def _levels(self, s):
        lvl = [-1] * self.n
        lvl[s] = 0
        q = deque([s])
        while q:
            u = q.popleft()
            for e in self.adj[u]:
                v = self.to[e]
                if self.cap[e] > 0 and lvl[v] < 0:
                    lvl[v] = lvl[u] + 1
                    q.append(v)
        return lvl

    def max_flow(self, s, t):
        total = 0
        to, cap, adj = self.to, self.cap, self.adj
        while True:
            lvl = self._levels(s)
            if lvl[t] < 0:
                return total
            it = [0] * self.n
            path = []          # edge ids from s to the current node
            u = s
            while True:
                if u == t:
                    f = min(cap[e] for e in path)
                    for e in path:
                        cap[e] -= f
                        cap[e ^ 1] += f
                    total += f
                    path = []
                    u = s
                    continue
                advanced = False
                while it[u] < len(adj[u]):
                    e = adj[u][it[u]]
                    v = to[e]
                    if cap[e] > 0 and lvl[v] == lvl[u] + 1:
                        path.append(e)
                        u = v
                        advanced = True
                        break
                    it[u] += 1
                if advanced:
                    continue
                if u == s:
                    break
                lvl[u] = -1    # dead end: prune and step back
                e = path.pop()
                u = to[e ^ 1]

    def reachable(self, s):
        """Nodes reachable from s in the residual graph (source side of a min cut)."""
        return [x >= 0 for x in self._levels(s)]


def _solve(T, d, c, edge_cap):
    """Core. edge_cap = _INF (non-simple) or 1 (simple).
    Returns (value, total demand, assignment, source-side vertex set of a min cut)."""
    Ts, d, items, cs = _norm(T, d, c)
    n, m = len(Ts), len(items)
    idx = {a: n + k for k, a in enumerate(items)}
    S, Tk = n + m, n + m + 1
    g = _Flow(n + m + 2)
    for i in range(n):
        g.add(S, i, d[i])
    for a in items:
        g.add(idx[a], Tk, cs[a])
    edges = [[(a, g.add(i, idx[a], edge_cap)) for a in Ts[i]] for i in range(n)]
    val = g.max_flow(S, Tk)
    assign = [[a for a, e in row for _ in range(g.cap[e ^ 1])] for row in edges]
    reach = g.reachable(S)
    return val, sum(d), assign, {i for i in range(n) if reach[i]}


def max_matched(T, d, c=None, simple=True):
    """Number of matched slots (the integer the old `bmatch(Ds, demand)` copies returned;
    with c=None the simple and non-simple values coincide)."""
    return _solve(T, d, c, 1 if simple else _INF)[0]


def bmatch(T, d, c=None):
    """Capacitated (non-simple) b-matching.

    Vertex i gets d[i] slots, item a has c[a] copies, every slot of i goes to a copy of an
    item of T[i], no copy is used twice. One vertex MAY use several copies of the same item.
    This is exactly `HasBMatching t d c` of proofs/main/PEqualNP/Base/Matching/Hall.lean.

    Returns (assignment, None) on success: assignment[i] is a list of d[i] items of T[i]
    (with repetition; item a occurs at most c[a] times overall).
    Returns (None, s) on failure: s is a set of vertex indices with
        sum_{i in s} d[i]  >  sum_{a in N(s)} c[a],      N(s) = union of T[i], i in s,
    a violated instance of `hasBMatching_iff` (s = vertices reachable from the source in the
    residual graph of a maximum flow).
    """
    val, D, assign, s = _solve(T, d, c, _INF)
    return (assign, None) if val == D else (None, s)


def simple_bmatch(T, d, c=None):
    """Simple capacitated b-matching: as `bmatch`, but vertex i uses each item at most once
    (unit edge capacities), so assignment[i] is a list of d[i] DISTINCT items of T[i].

    Returns (assignment, None), or (None, s) where s is a set of vertex indices with
        sum_{i in s} d[i]  >  sum_a min(c[a], #{i in s : a in T[i]}).
    That inequality failing for no s is the exact condition (max-flow/min-cut). The plain
    Hall condition `sum_s d <= sum_{N(s)} c` of `bmatch` is necessary but NOT sufficient:
    T=[{a,b},{a,b},{a,c}], d=[2,2,2], c=2 passes it for every s, yet s={0,1,2} gives
    6 > min(2,3)+min(2,2)+min(2,1) = 5. With all c[a] = 1 the two notions coincide.
    """
    val, D, assign, s = _solve(T, d, c, 1)
    return (assign, None) if val == D else (None, s)


def frac_feasible_half(T, d):
    """Fixed-1/2-weight two-system load check, without an LP.

    T[w] = (D0, D1): the two counted gate sets of set w (e.g. canonical and R*), d[w] its
    demand |S_w| - 1. Returns (ok, violator).

    What the scripts computed. work/notes951/w9/mixrule.py `fixedlp` (weights a = 1/2):
    variables y[w,j,g] in [0, 1/2] for g in D_j(w), with sum_g y[w,j,g] = d[w]/2, minimising
    the maximum gate load L = max_g sum_{w,j} y[w,j,g]; the rule "works" iff L <= 1.
    Doubling y gives x[w,j,g] in [0,1], sum_g x = d[w] per system (w,j), gate load <= 2:
    a fractional simple b-matching of the 2n systems into gates of capacity 2. That
    polytope is integral (bipartite network matrix), so
        L <= 1   <=>   simple_bmatch(all 2n systems, each with demand d[w], c=2) succeeds.
    This replaces mixrule.py at a = 1/2 exactly, with no float tolerance; the returned
    assignment halves to an LP solution with every y in {0, 1/2}.

    When it does not apply. (1) Other fixed weights p/q need edge capacity p and gate
    capacity q, not provided here. (2) w9/fraclp.py optimises the weights lam over a menu
    of systems; that is a genuine LP. This check is only a sufficient test for it (uniform
    1/2 on two chosen systems), and a single system per set is just `bmatch`.
    (3) It decides L <= 1 only; it does not return the optimum L.

    On failure the violator is a set of pairs (w, j), j in {0, 1}, with
        sum_{(w,j) in s} d[w]  >  sum_g min(2, #{(w,j) in s : g in D_j(w)}),
    i.e. the two-world Hall inequality fails for F_c = {w : (w,0) in s}, F_r = {w : (w,1) in s}.
    On success the violator is None.
    """
    Ts, ds, keys = [], [], []
    for w, pair in enumerate(T):
        pair = list(pair)
        if len(pair) != 2:
            raise ValueError('T[%d] must be a pair of item collections' % w)
        for j, D in enumerate(pair):
            Ts.append(D); ds.append(d[w]); keys.append((w, j))
    assign, s = simple_bmatch(Ts, ds, 2)
    if assign is not None:
        return True, None
    return False, {keys[k] for k in s}


def hall_check(T, d, c=None, simple=False):
    """Brute force over ALL vertex subsets (exponential; tests and tiny instances only).

    simple=False: checks sum_{i in s} d[i] <= sum_{a in N(s)} c[a]            (bmatch)
    simple=True:  checks sum_{i in s} d[i] <= sum_a min(c[a], #{i in s: a in T[i]})
    Returns None if every subset passes, else a violating subset (smallest first) as a set.
    """
    Ts, d, items, cs = _norm(T, d, c)
    n = len(Ts)
    for r in range(1, n + 1):
        for s in combinations(range(n), r):
            cnt = {}
            for i in s:
                for a in Ts[i]:
                    cnt[a] = cnt.get(a, 0) + 1
            if simple:
                rhs = sum(min(cs[a], k) for a, k in cnt.items())
            else:
                rhs = sum(cs[a] for a in cnt)
            if sum(d[i] for i in s) > rhs:
                return set(s)
    return None
