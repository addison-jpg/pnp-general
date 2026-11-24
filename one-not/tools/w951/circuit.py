"""One-NOT circuits for Boolean sums (L-meta-951): the single shared data structure.

A circuit has `n` inputs (wires 0..n-1) and `s` gates (gate k is wire n+k), each
('and', a, b), ('or', a, b) or ('not', a) on EARLIER wires, target sets S_w (lists of inputs)
and one output wire per set (`outs[w]` should compute OR(S_w)).

JSON format (front/scaffold scripts): {"n":…, "sets":[[…]], "gates":[["or",a,b],["and",a,b],["not",a]], "outs":[…]}.
The SAT tools write NOT as ("not", a, a); `Circuit` accepts both and stores the 2-field form.

Points are ints: bit i of a point is x_i (so e_u = 1<<u, z_Q = all-ones minus Q).
Truth tables are ints over the 2^n points: bit r of table(i) is wire i at point r.
(The legacy scripts index rows by itertools.product, i.e. x_0 is the MOST significant bit;
`product_index` / `table_in_product_order` convert.)

Every transformation returns a `Reduced` record with the new circuit, the old->new wire map
and the gate-count accounting; nothing is mutated in place.
"""
import json
from collections import namedtuple
from itertools import combinations

__all__ = ['Circuit', 'Reduced', 'as_circuit', 'load', 'save', 'point', 'bits', 'z_of',
           'product_index', 'CONST0', 'CONST1']

CONST0, CONST1 = ('const', 0), ('const', 1)
_OPS = ('and', 'or', 'not')

Reduced = namedtuple('Reduced', 'circuit wire_map removed detail')
Reduced.__doc__ = """Result of a circuit transformation.
circuit   the new Circuit
wire_map  dict old wire -> new wire, or CONST0/CONST1 if the old wire became constant,
          or None if it was removed as dead
removed   number of gates removed (old s - new s)
detail    dict with the accounting: disjoint lists of old gate wires 'const', 'merged', 'dead'
          (len sums to `removed`), plus transformation-specific entries"""


def point(x):
    """Point (int) from a 0/1 sequence x[0..n-1]; ints pass through."""
    if isinstance(x, int):
        return x
    r = 0
    for i, b in enumerate(x):
        if b:
            r |= 1 << i
    return r


def bits(m):
    """Sorted list of the set bit positions of the int m."""
    out, i = [], 0
    while m:
        if m & 1:
            out.append(i)
        m >>= 1
        i += 1
    return out


def z_of(n, Q):
    """z_Q: the point that is 0 exactly on Q (legacy `zQ`, `zof`, `zS`, `[0 if v in Q else 1 ...]`)."""
    return ((1 << n) - 1) & ~sum(1 << v for v in set(Q))


def product_index(n, pt):
    """Index of point `pt` in itertools.product([0,1], repeat=n) (x_0 most significant)."""
    r = 0
    for i in range(n):
        if pt >> i & 1:
            r |= 1 << (n - 1 - i)
    return r


_INPUT_TABLES = {}


def _input_tables(n):
    if n not in _INPUT_TABLES:
        R = 1 << n
        tabs = []
        for i in range(n):
            t, width = ((1 << (1 << i)) - 1) << (1 << i), 1 << (i + 1)   # 0..01..1, period 2^(i+1)
            while width < R:                                             # repeat by doubling
                t |= t << width
                width *= 2
            tabs.append(t)
        _INPUT_TABLES[n] = tabs
    return _INPUT_TABLES[n]


class Circuit:
    """Immutable one-NOT (or any-NOT) circuit with cached truth tables. See module docstring."""
    __slots__ = ('n', 'gates', 'sets', 'outs', '_cache')

    def __init__(self, n, gates, sets=(), outs=()):
        self.n = int(n)
        gs = []
        for g in gates:
            op = g[0]
            if op == 'not':
                gs.append(('not', int(g[1])))
            elif op in ('and', 'or'):
                gs.append((op, int(g[1]), int(g[2])))
            else:
                raise ValueError('bad gate %r' % (g,))
        self.gates = tuple(gs)
        self.sets = tuple(tuple(s) for s in sets)
        self.outs = tuple(int(o) for o in outs)
        self._cache = {}

    # ---------------------------------------------------------------- I/O
    @classmethod
    def from_dict(cls, d):
        """From the JSON dict. Accepts the wrapper {'c': {...}} of the climb logs, key 'out' for
        'outs', and 3-field NOT gates (legacy `norm`: conedbl.py:5, w9/fa/lib.py:2, w9/tw/tw.py:20)."""
        if isinstance(d, Circuit):
            return d
        if 'gates' not in d and 'c' in d:
            d = d['c']
        outs = d['outs'] if 'outs' in d else d.get('out', ())
        if isinstance(outs, int):
            outs = [outs]
        return cls(d['n'], d['gates'], d.get('sets', ()), outs)

    def to_dict(self, not_arity=2):
        """JSON dict (lists). not_arity=3 writes NOT as ['not', a, a] (SAT-tool format)."""
        gs = [[g[0], g[1]] + ([g[1]] if not_arity == 3 else []) if g[0] == 'not' else list(g) for g in self.gates]
        return {'n': self.n, 'sets': [list(s) for s in self.sets], 'gates': gs, 'outs': list(self.outs)}

    def triples(self):
        """Gates as (op, a, b) triples, NOT as ('not', a, a) (ov951.decode / payment format)."""
        return [(g[0], g[1], g[1]) if g[0] == 'not' else g for g in self.gates]

    def __eq__(self, o):
        return isinstance(o, Circuit) and (self.n, self.gates, self.sets, self.outs) == (o.n, o.gates, o.sets, o.outs)

    def __hash__(self):
        return hash((self.n, self.gates, self.sets, self.outs))

    def __repr__(self):
        return 'Circuit(n=%d, s=%d, sets=%s, outs=%s)' % (self.n, self.s, list(map(list, self.sets)), list(self.outs))

    # dict-style read access, so code written for the JSON dict keeps working
    def __getitem__(self, k):
        if k == 'n':
            return self.n
        if k == 'gates':
            return [list(g) for g in self.gates]
        if k == 'sets':
            return [list(s) for s in self.sets]
        if k == 'outs':
            return list(self.outs)
        raise KeyError(k)

    # ---------------------------------------------------------------- basic data
    @property
    def s(self):
        """Number of gates."""
        return len(self.gates)

    @property
    def W(self):
        """Number of wires n + s."""
        return self.n + len(self.gates)

    @property
    def demands(self):
        """d_w = |S_w| - 1."""
        return [len(S) - 1 for S in self.sets]

    @property
    def base(self):
        """sum_w (|S_w| - 1): the lower bound of L-meta-951."""
        return sum(len(S) - 1 for S in self.sets)

    @property
    def gate_wires(self):
        return range(self.n, self.W)

    @property
    def nots(self):
        """Wires of the NOT gates, in order."""
        return [self.n + k for k, g in enumerate(self.gates) if g[0] == 'not']

    @property
    def not_wire(self):
        """Wire of the (first) NOT gate (legacy `nw`, `Nw`, `N`); None if there is none."""
        ns = self.nots
        return ns[0] if ns else None

    @property
    def h_wire(self):
        """Input wire of the (first) NOT gate (legacy `hw`, `h`, `H`); None if there is none."""
        nw = self.not_wire
        return None if nw is None else self.gates[nw - self.n][1]

    def inputs_of(self, w):
        """Input wires of gate wire w (empty for an input)."""
        return () if w < self.n else self.gates[w - self.n][1:]

    def validate(self, sums=True, one_not=None):
        """Raise ValueError unless the circuit is well formed (gate inputs earlier wires, outs are wires)
        and, if sums, the sets are a Boolean-sum system (|S| >= 2, pairwise |S∩S'| <= 1) with one output each.
        one_not=True demands exactly one NOT, one_not=False at most one. (w9/fc/lib.py:21-26)"""
        n = self.n
        for k, g in enumerate(self.gates):
            if not all(0 <= j < n + k for j in g[1:]):
                raise ValueError('gate %d reads a non-earlier wire: %r' % (k, g))
        if not all(0 <= o < self.W for o in self.outs):
            raise ValueError('output wire out of range')
        if sums:
            if len(self.sets) != len(self.outs):
                raise ValueError('need one output per set')
            if not all(len(set(S)) == len(S) >= 2 and all(0 <= v < n for v in S) for S in self.sets):
                raise ValueError('sets must have >= 2 distinct inputs')
            for a, b in combinations(self.sets, 2):
                if len(set(a) & set(b)) > 1:
                    raise ValueError('sets %r and %r share two points' % (a, b))
        k = len(self.nots)
        if one_not is True and k != 1 or one_not is False and k > 1:
            raise ValueError('%d NOT gates' % k)
        return self

    # ---------------------------------------------------------------- evaluation
    def eval(self, x, force=None):
        """All wire values at one point (list of n+s bits). x: point int or 0/1 sequence.
        force=0/1 replaces every NOT gate by that constant (the circuits C0 / C1).
        Legacy: evalN (w8/verify.py:2), evaluate (chargeok_check.py:6), ev (rstar.py:4, w9/fa/lib.py:7,
        w9/fc/lib.py:5, w9/tw/tw.py:5, fb/top2.py:6, gen_clean.py:10, climb*.py:12), wires (ov951.py:58)."""
        if isinstance(x, int):
            w = [(x >> i) & 1 for i in range(self.n)]
        else:
            w = [int(b) for b in x]
        for g in self.gates:
            if g[0] == 'not':
                w.append(1 - w[g[1]] if force is None else force)
            elif g[0] == 'and':
                w.append(w[g[1]] & w[g[2]])
            else:
                w.append(w[g[1]] | w[g[2]])
        return w

    def point_mask(self, pt, force=None):
        """Int whose bit i is the value of wire i at point pt (cached)."""
        key = ('pm', force)
        cache = self._cache.get(key)
        if cache is None:
            cache = self._cache[key] = {}
        m = cache.get(pt)
        if m is None:
            m = 0
            for i, b in enumerate(self.eval(pt, force)):
                if b:
                    m |= 1 << i
            cache[pt] = m
        return m

    @property
    def full(self):
        """All-ones truth table (2^n bits)."""
        return (1 << (1 << self.n)) - 1

    def tables(self, force=None):
        """Truth tables of all wires as ints over the 2^n points (cached).
        Legacy: tts (w9/fa/sand.py:6), the `w`/`X` arrays of duals/relrule.py:10-13 and climbr.py:8-16,
        tabs (w9/fc/lib.py:28), tables (resid.py:7, fc/relrule.py:6, tw/clean.py:4), table (payment/ana.py:5),
        tt (w9/fe/rel.py:5) — those are per-point lists; see `value` / `table_in_product_order`."""
        key = ('tt', force)
        t = self._cache.get(key)
        if t is None:
            full = self.full
            t = list(_input_tables(self.n))
            for g in self.gates:
                if g[0] == 'not':
                    t.append(full ^ t[g[1]] if force is None else (full if force else 0))
                elif g[0] == 'and':
                    t.append(t[g[1]] & t[g[2]])
                else:
                    t.append(t[g[1]] | t[g[2]])
            self._cache[key] = t
        return t

    def table(self, w, force=None):
        return self.tables(force)[w]

    def value(self, w, pt, force=None):
        """Value of wire w at point pt."""
        return self.tables(force)[w] >> pt & 1

    def table_in_product_order(self, w, force=None):
        """Truth table of wire w as a tuple indexed like itertools.product([0,1], repeat=n)."""
        t, n = self.tables(force)[w], self.n
        out = [0] * (1 << n)
        for pt in range(1 << n):
            out[product_index(n, pt)] = t >> pt & 1
        return tuple(out)

    def or_table(self, S):
        """Truth table of OR(x_v : v in S)."""
        X, t = _input_tables(self.n), 0
        for v in S:
            t |= X[v]
        return t

    def cube_table(self, z):
        """Truth table of the upper cube {x >= z}."""
        X, t = _input_tables(self.n), self.full
        for v in bits(z):
            t &= X[v]
        return t

    # ---------------------------------------------------------------- structure
    def cone(self, o):
        """Gate wires in the cone of wire o (o included if it is a gate).
        Legacy: cone (chargeok_check.py:15, allsys.py:10, w9/fc/lib.py:12, w9/tw/tw.py:12, fb/irr.py:3,
        dualp.py:109, payment/ana.py:14, scaffold_opus/gen.py:12, an.py:9), cone_o (payer.py:13)."""
        key = ('cone', o)
        c = self._cache.get(key)
        if c is None:
            n, seen, st = self.n, set(), [o]
            while st:
                i = st.pop()
                if i < n or i in seen:
                    continue
                seen.add(i)
                st.extend(self.gates[i - n][1:])
            c = self._cache[key] = frozenset(seen)
        return c

    def cones(self):
        """Cones of the outputs, one per set."""
        return [self.cone(o) for o in self.outs]

    def downstream(self, w=None):
        """Gate wires that depend (syntactically) on wire w, w included; default w = the NOT gate.
        Legacy: `down` (allsys.py:7-9, dualp.py:106-108, w9/fa/sig.py:6, fc/pool.py:8-10)."""
        if w is None:
            w = self.not_wire
        key = ('down', w)
        d = self._cache.get(key)
        if d is None:
            d = set() if w is None else {w}
            for k, g in enumerate(self.gates):
                if any(j in d for j in g[1:]):
                    d.add(self.n + k)
            d = self._cache[key] = frozenset(d)
        return d

    def readers(self):
        """readers()[w] = gate wires that read wire w (each once, in order). Legacy: `rd` (payer.py:44-47)."""
        r = self._cache.get('readers')
        if r is None:
            r = [[] for _ in range(self.W)]
            for k, g in enumerate(self.gates):
                for j in dict.fromkeys(g[1:]):
                    r[j].append(self.n + k)
            self._cache['readers'] = r
        return r

    def read_wires(self):
        """Wires read by some gate or used as an output."""
        return {j for g in self.gates for j in g[1:]} | set(self.outs)

    def unread(self):
        """Gate wires that no gate reads and that are not outputs."""
        rd = self.read_wires()
        return [w for w in self.gate_wires if w not in rd]

    def live(self, outs=None):
        """Gate wires in the cone of some output (default: all outputs)."""
        res = set()
        for o in (self.outs if outs is None else outs):
            res |= self.cone(o)
        return res

    # ---------------------------------------------------------------- checks
    def is_correct(self, force=None):
        """Every output equals OR(S_w) on all 2^n points (with NOT forced to a constant if force is given)."""
        t = self.tables(force)
        return all(t[o] == self.or_table(S) for S, o in zip(self.sets, self.outs))

    def is_essential(self):
        """Both C0 and C1 (NOT replaced by constant 0 / 1) are wrong.
        Legacy: essential (scaffold_opus/gen.py:19), okN (gen_clean.py:42), `wrong` (climb*.py:25)."""
        return not self.is_correct(0) and not self.is_correct(1)

    def is_clean(self, constants=True):
        """All wires (inputs included) have pairwise different truth tables; with constants=True
        (verify.py, w9/fc/lib.py, climbr.tt_ok) also no wire is constant. payment/ana.py:33 is constants=False."""
        t = self.tables()
        if len(set(t)) != len(t):
            return False
        return not constants or all(0 < x < self.full for x in t)

    def all_read(self):
        """Every gate is read by a gate or is an output (legacy key 'read' / 'allread')."""
        return not self.unread()

    def not_is_live(self):
        """The NOT gate lies in the cone of some output."""
        nw = self.not_wire
        return nw is not None and nw in self.live()

    def verify(self):
        """dict(correct, C0, C1, clean, read, s, base) — exactly w8/verify.py:9-18 `verify`
        (C0/C1 = the circuit with NOT := 0 / 1 is still correct)."""
        return dict(correct=self.is_correct(), C0=self.is_correct(0), C1=self.is_correct(1),
                    clean=self.is_clean(), read=self.all_read(), s=self.s, base=self.base)

    def verify_full(self):
        """The independent verifier of w9/fc/lib.py:19-43: adds h0 = h(0), hard[w] = h(z_{S_w}) = 1,
        nset[w] = NOT in cone(o_w), hardN = #(hard and nset), DD[w]. Requires exactly one NOT."""
        self.validate(one_not=True)
        n, hw, nw = self.n, self.h_wire, self.not_wire
        hard = [self.value(hw, z_of(n, S)) == 1 for S in self.sets]
        nset = [nw in c for c in self.cones()]
        dd = [self.value(o, z_of(n, S), 1) == 1 and any(self.value(o, 1 << u, 0) == 0 for u in S)
              for S, o in zip(self.sets, self.outs)]
        return dict(correct=self.is_correct(), C0wrong=not self.is_correct(0), C1wrong=not self.is_correct(1),
                    clean=self.is_clean(), read=self.all_read(), h0=self.value(hw, 0),
                    hardN=sum(a and b for a, b in zip(hard, nset)), hard=hard, nset=nset, DD=dd,
                    s=self.s, base=self.base, n=n)

    # ---------------------------------------------------------------- transformations
    def _rebuild(self, keep, alias, sets, out_alias, detail):
        """New circuit on the gates `keep` (old gate wires, any iterable), reading inputs through `alias`
        (old wire -> old wire or CONST). Returns Reduced."""
        n = self.n
        keep = sorted(keep)
        new = {i: i for i in range(n)}
        gates = []
        for i in keep:
            g = self.gates[i - n]
            args = []
            for j in g[1:]:
                a = alias(j)
                if isinstance(a, tuple) or a not in new:
                    raise ValueError('kept gate %d reads removed wire %r' % (i, j))
                args.append(new[a])
            new[i] = n + len(gates)
            gates.append((g[0],) + tuple(args))
        wire_map = {}
        for i in range(self.W):
            a = alias(i)
            wire_map[i] = a if isinstance(a, tuple) else new.get(a)
        kept_sets, outs, const_outs = [], [], []
        for S, a in zip(sets, out_alias):
            if isinstance(a, tuple):
                const_outs.append((tuple(S), a[1]))
            else:
                kept_sets.append(S)
                outs.append(new[a])
        if const_outs:
            detail['const_outs'] = const_outs
        c = Circuit(n, gates, kept_sets, outs)
        return Reduced(c, wire_map, self.s - c.s, detail)

    def drop_gate(self, k, j):
        """Delete gate k and redirect its readers (and outputs) to the earlier wire j; later wires shift
        down by one. This is `dropGate gates k j n` / `redir (n+k) j` of lean/PEqualNP/W951/Cleanup.lean:11,69."""
        p = self.n + k
        if not (0 <= k < self.s and 0 <= j < p):
            raise ValueError('drop_gate needs k < s and j < n + k')
        rd = lambda i: i if i < p else (j if i == p else i - 1)
        gates = list(self.gates[:k]) + [(g[0],) + tuple(rd(i) for i in g[1:]) for g in self.gates[k + 1:]]
        c = Circuit(self.n, gates, self.sets, [rd(o) for o in self.outs])
        return Reduced(c, {i: rd(i) for i in range(self.W)}, 1, {'const': [], 'merged': [p], 'dead': []})

    def remove_dead(self, outs=None):
        """Remove every gate outside the cones of the outputs (default: all). Same result as iterating
        'delete an unread gate' (prune, w9/fb/cfgI.py:14-21)."""
        live = self.live(outs)
        dead = [w for w in self.gate_wires if w not in live]
        ident = lambda i: i
        return self._rebuild(live, ident, self.sets, self.outs, {'const': [], 'merged': [], 'dead': dead})

    def delete_outputs(self, F):
        """Delete the outputs (and sets) with indices in F and keep only the cones of the remaining
        outputs. removed = number of gates private to F = |gates \\ union of the other cones|
        (the quantity P(F) of maxviol, w9/fb/irr.py:10-18). detail['deleted'] lists the set indices."""
        F = set(F)
        keep = [w for w in range(len(self.outs)) if w not in F]
        live = self.live([self.outs[w] for w in keep])
        dead = [w for w in self.gate_wires if w not in live]
        return self._rebuild(live, lambda i: i, [self.sets[w] for w in keep], [self.outs[w] for w in keep],
                             {'const': [], 'merged': [], 'dead': dead, 'deleted': sorted(F)})

    def cleanup(self):
        """Merge every gate whose truth table equals an earlier wire into that wire, then remove dead
        gates (cleanup, w9/tw/clean.py:7-29; constants are not merged, as there)."""
        t = self.tables()
        first, rep = {}, {}
        for i, x in enumerate(t):
            if x in first and i >= self.n:
                rep[i] = first[x]
            else:
                first.setdefault(x, i)
        alias = lambda i: rep.get(i, i)
        return self._finish(alias, self.sets, [alias(o) for o in self.outs], {'const': []})

    def _finish(self, alias, sets, out_alias, detail):
        n, need, st = self.n, set(), [a for a in out_alias if not isinstance(a, tuple)]
        while st:
            i = st.pop()
            if isinstance(i, tuple) or i < n or i in need:
                continue
            need.add(i)
            st.extend(alias(j) for j in self.gates[i - n][1:])
        merged = [i for i in self.gate_wires if not isinstance(alias(i), tuple) and alias(i) != i]
        consts = [i for i in self.gate_wires if isinstance(alias(i), tuple)]
        dead = [i for i in self.gate_wires if alias(i) == i and i not in need]
        detail.update(const=consts, merged=merged, dead=dead)
        return self._rebuild(need, alias, sets, out_alias, detail)

    def _restricted_sets(self, v, b):
        """Sets/outputs surviving x_v := b: for b = 0 every set loses v; for b = 1 the sets through v
        become constant 1 and are dropped."""
        if b == 0:
            idx = list(range(len(self.sets)))
            sets = [tuple(u for u in S if u != v) for S in self.sets]
        else:
            idx = [w for w, S in enumerate(self.sets) if v not in S]
            sets = [self.sets[w] for w in idx]
        return idx, sets

    def restrict(self, v, b, semantic=True):
        """The restriction x_v := b with dead-gate removal and gate-count accounting.

        Input v stays as an (unused) input so wire numbers of the other inputs do not move.
        Sets: b = 0 removes v from every set (a set may shrink to one point; its output is then an
        input wire); b = 1 drops the sets through v. detail['sets'] gives the surviving set indices.

        semantic=True  merge by truth table on the subcube x_v = b: a gate equal there to a constant,
                       to an input or to an earlier gate is removed; then dead gates are removed.
                       circuit.s equals restr(c, v, b) of w9/fe/kill.py:5-22.
        semantic=False syntactic constant propagation only (and(1,x)=x, or(0,x)=x, and(0,x)=0, ...),
                       then dead gates: `propagate({v: b})`.
        detail: 'const' gates that became constant, 'merged' gates identified with another wire,
        'dead' gates no remaining output needs, 'through' = number of sets containing v.
        """
        idx, sets = self._restricted_sets(v, b)
        through = sum(1 for S in self.sets if v in S)
        if not semantic:
            r = self.propagate({v: b}, keep=idx, sets=sets)
            r.detail.update(sets=idx, through=through)
            return r
        X = _input_tables(self.n)
        M = X[v] if b else self.full ^ X[v]
        t = [x & M for x in self.tables()]
        canon = {0: CONST0, M: CONST1}
        for i in range(self.n):
            if i != v:
                canon.setdefault(t[i], i)
        al = {}
        for i in range(self.W):
            if i < self.n:
                al[i] = canon[t[i]]
            elif t[i] in canon:
                al[i] = canon[t[i]]
            else:
                canon[t[i]] = i
                al[i] = i
        return self._finish(al.__getitem__, sets, [al[self.outs[w]] for w in idx], {'sets': idx, 'through': through})

    def propagate(self, assign, keep=None, sets=None):
        """Syntactic constant propagation: `assign` maps wires (inputs or gates, e.g. the NOT) to 0/1.
        A gate with a constant input becomes a constant or an alias of its other input; a NOT of a
        constant becomes a constant. Then only the cones of the outputs with set indices `keep`
        (default: all) are kept. With assign = {v: 1 for v in M} ∪ {NOT: 0} the new gate count is
        restrict_count(n, gates, outs, p, M, keep) of tools/l951_charging/agents/restr951.py:5-32."""
        n = self.n
        val = {w: (CONST1 if b else CONST0) for w, b in assign.items()}
        alias = {}

        def res(w):
            while w in alias:
                w = alias[w]
            return val.get(w, w)
        for k, g in enumerate(self.gates):
            w = n + k
            if w in val:
                continue
            if g[0] == 'not':
                a = res(g[1])
                if isinstance(a, tuple):
                    val[w] = CONST0 if a[1] else CONST1
                continue
            ra, rb = res(g[1]), res(g[2])
            ca, cb = isinstance(ra, tuple), isinstance(rb, tuple)
            if ca and cb:
                x = ra[1] & rb[1] if g[0] == 'and' else ra[1] | rb[1]
                val[w] = CONST1 if x else CONST0
            elif ca or cb:
                c, o = (ra, rb) if ca else (rb, ra)
                if g[0] == 'and':
                    if c[1] == 0:
                        val[w] = CONST0
                    else:
                        alias[w] = o
                else:
                    if c[1] == 1:
                        val[w] = CONST1
                    else:
                        alias[w] = o
        idx = list(range(len(self.outs))) if keep is None else list(keep)
        if sets is None:
            sets = [self.sets[w] for w in idx] if self.sets else [()] * len(idx)
        return self._finish(res, sets, [res(self.outs[w]) for w in idx], {})


def as_circuit(c):
    """Circuit from a Circuit or a JSON dict."""
    return c if isinstance(c, Circuit) else Circuit.from_dict(c)


def load(path):
    """List of circuits from a .json file (one circuit) or a .jsonl file (one per non-empty line;
    lines without a circuit are skipped). Legacy: load (w9/fa/lib.py:4, w9/tw/tw.py:68) and the
    `cs=[json.loads(l) ...] if f.endswith('.jsonl') else [json.load(open(f))]` idiom."""
    with open(path) as f:
        if str(path).endswith('.jsonl'):
            ds = [json.loads(l) for l in f if l.strip()]
        else:
            ds = [json.load(f)]
    out = []
    for d in ds:
        if isinstance(d, dict) and ('gates' in d or isinstance(d.get('c'), dict)):
            out.append(Circuit.from_dict(d))
    return out


def save(c, path, not_arity=2):
    """Write one circuit as .json, or append it as a line to a .jsonl file."""
    d = as_circuit(c).to_dict(not_arity)
    if str(path).endswith('.jsonl'):
        with open(path, 'a') as f:
            f.write(json.dumps(d) + '\n')
    else:
        with open(path, 'w') as f:
            json.dump(d, f)
