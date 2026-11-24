"""Faster exact synthesis for the edge function f_G(x) = OR_{uv in E} x_u x_v.
Basis: fan-in-2 AND/OR plus NOT, every gate counted, inputs free.

synth_exact(n, edges, k): is there a circuit with EXACTLY k gates, every non-output gate read
by a later gate, computing f_G?  min_size() runs k upward from a counting lower bound, so the
first SAT k is the least size and every smaller k was UNSAT.

Speedups over exact_edge_fn.py (all sound, see comments):
  * CEGAR on truth-table rows (seeded with the informative rows), as in cegar_synth.py;
  * order of independent consecutive gates is fixed (sorted by input pair);
  * gates are not repeated; no NOT of NOT; every gate is used;
  * lower bound k >= (#non-isolated vertices) - 1 (each of them must be read, 2 inputs per gate).
"""
import itertools, random, sys, time
from pysat.solvers import Solver


def f_row(r, edges):
    return int(any((r >> u) & 1 and (r >> v) & 1 for u, v in edges))


class Synth:
    def __init__(self, n, edges, k, sym=2, solver='cadical153'):
        self.n, self.k, self.edges = n, k, edges
        self.m = m = n + k
        self.S = Solver(name=solver)
        self.cnt = 0
        nv, add = self.nv, self.add
        self.s1, self.s2 = {}, {}
        self.tA, self.tO, self.tN = {}, {}, {}
        for g in range(n, m):
            A, O, N = nv(), nv(), nv()
            self.tA[g], self.tO[g], self.tN[g] = A, O, N
            add([A, O, N]); add([-A, -O]); add([-A, -N]); add([-O, -N])
            for i in range(g):
                self.s1[g, i], self.s2[g, i] = nv(), nv()
            self.exactly_one([self.s1[g, i] for i in range(g)])
            self.exactly_one([self.s2[g, i] for i in range(g)])
            for i in range(g):
                add([-N, -self.s1[g, i], self.s2[g, i]])          # NOT: s2 = s1
                for j in range(i + 1):                             # binary: s1 < s2
                    add([N, -self.s1[g, i], -self.s2[g, j]])
                if i >= n:
                    add([-N, -self.s1[g, i], -self.tN[i]])         # no NOT of NOT
        # every non-output gate is read
        for i in range(n, m - 1):
            add([self.s1[g, i] for g in range(i + 1, m)] + [self.s2[g, i] for g in range(i + 1, m)])
        # every non-isolated input is read (f_G depends on it)
        deg = set(u for e in edges for u in e)
        for i in deg:
            add([self.s1[g, i] for g in range(n, m)] + [self.s2[g, i] for g in range(n, m)])
        if sym:
            self.symmetry(sym)
        self.rows = set()

    def nv(self):
        self.cnt += 1
        return self.cnt

    def add(self, c):
        self.S.add_clause(c)

    def exactly_one(self, lits):
        self.add(lits)
        if len(lits) <= 6:
            for a, b in itertools.combinations(lits, 2):
                self.add([-a, -b])
        else:
            prev = None
            for idx, l in enumerate(lits):
                if idx == len(lits) - 1:
                    if prev is not None:
                        self.add([-prev, -l])
                    break
                s = self.nv()
                self.add([-l, s])
                if prev is not None:
                    self.add([-prev, s]); self.add([-prev, -l])
                prev = s

    def symmetry(self, level=2):
        n, m, add = self.n, self.m, self.add
        for g in range(n, m - 1):
            h = g + 1
            reads = [self.s1[h, g], self.s2[h, g]]
            # h does not read g  =>  (s1[g], s2[g]) <=_lex (s1[h], s2[h])
            for i in range(g):
                for i2 in range(i):                                # s1[h] < s1[g]: forbidden
                    add(reads + [-self.s1[g, i], -self.s1[h, i2]])
                for j in range(g):
                    for j2 in range(j):                            # equal s1, s2[h] < s2[g]
                        add(reads + [-self.s1[g, i], -self.s1[h, i], -self.s2[g, j], -self.s2[h, j2]])
            if level < 2:
                continue
            # equal inputs: break the tie by type order NOT < AND < OR
            for i in range(g):
                for j in range(g):
                    pre = reads + [-self.s1[g, i], -self.s1[h, i], -self.s2[g, j], -self.s2[h, j]]
                    add(pre + [-self.tA[g], -self.tN[h]])
                    add(pre + [-self.tO[g], -self.tN[h]])
                    add(pre + [-self.tO[g], -self.tA[h]])
                    # no two gates of the same type on the same pair: merge them
                    add(pre + [-self.tA[g], -self.tA[h]])
                    add(pre + [-self.tO[g], -self.tO[h]])
                    add(pre + [-self.tN[g], -self.tN[h]])

    def add_row(self, r):
        if r in self.rows:
            return
        self.rows.add(r)
        n, m, add = self.n, self.m, self.add
        t = f_row(r, self.edges)
        v = {g: self.nv() for g in range(n, m)}
        def lit(i):
            return bool((r >> i) & 1) if i < n else v[i]
        for g in range(n, m):
            a, b = self.nv(), self.nv()
            for sel, x in ((self.s1, a), (self.s2, b)):
                for i in range(g):
                    s = sel[g, i]; L = lit(i)
                    if L is True: add([-s, x])
                    elif L is False: add([-s, -x])
                    else: add([-s, -L, x]); add([-s, L, -x])
            o = v[g]; A, O, N = self.tA[g], self.tO[g], self.tN[g]
            add([-A, -a, -b, o]); add([-A, a, -o]); add([-A, b, -o])
            add([-O, a, b, -o]); add([-O, -a, o]); add([-O, -b, o])
            add([-N, a, o]); add([-N, -a, -o])
        add([v[m - 1] if t else -v[m - 1]])

    def extract(self, model):
        ms = set(l for l in model if l > 0)
        gates = []
        for g in range(self.n, self.m):
            i = next(i for i in range(g) if self.s1[g, i] in ms)
            j = next(j for j in range(g) if self.s2[g, j] in ms)
            op = 'AND' if self.tA[g] in ms else 'OR' if self.tO[g] in ms else 'NOT'
            gates.append((op, i, j))
        return gates

    def evaluate(self, gates):
        n = self.n
        out = {}
        for r in range(1 << n):
            w = [(r >> i) & 1 for i in range(n)]
            for op, i, j in gates:
                w.append((w[i] & w[j]) if op == 'AND' else (w[i] | w[j]) if op == 'OR' else 1 - w[i])
            out[r] = w[-1]
        return out


def seed_rows(n, edges):
    rows = {0, (1 << n) - 1}
    for u in range(n):
        rows.add(1 << u)
    for u, v in edges:
        rows.add((1 << u) | (1 << v))
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v; adj[v] |= 1 << u
    for u in range(n):                    # a vertex with its whole neighbourhood, and independent sets
        rows.add((1 << u) | adj[u])
    full = (1 << n) - 1
    for u in range(n):
        rows.add(full & ~(1 << u))
    return rows


def synth_exact(n, edges, k, sym=True, per_round=6, verbose=False):
    """Return a gate list (op, i, j) with exactly k gates computing f_G, or None."""
    S = Synth(n, edges, k, sym=sym)
    for r in seed_rows(n, edges):
        S.add_row(r)
    rounds = 0
    while True:
        if not S.S.solve():
            S.S.delete()
            return None, rounds, len(S.rows)
        gates = S.extract(S.S.get_model())
        vals = S.evaluate(gates)
        bad = [r for r in range(1 << n) if vals[r] != f_row(r, edges)]
        rounds += 1
        if not bad:
            S.S.delete()
            return gates, rounds, len(S.rows)
        random.Random(rounds).shuffle(bad)
        for r in bad[:per_round]:
            S.add_row(r)


def min_size(n, edges, hi, lo=None, verbose=True, sym=True):
    nonisol = len(set(u for e in edges for u in e))
    if lo is None:
        lo = max(1, nonisol - 1)
    for k in range(lo, hi + 1):
        t = time.time()
        gates, rounds, nrows = synth_exact(n, edges, k, sym=sym)
        if verbose:
            print(f"   k={k}: {'SAT' if gates else 'UNSAT'} ({time.time()-t:.1f}s, {rounds} rounds, {nrows} rows)", flush=True)
        if gates:
            return k, gates
    return None, None


def tau(n, edges):
    for k in range(n + 1):
        for S in itertools.combinations(range(n), k):
            s = set(S)
            if all(u in s or v in s for u, v in edges):
                return k
