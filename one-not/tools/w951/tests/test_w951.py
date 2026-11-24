"""Tests for tools/w951: every function against the ORIGINAL implementation (tests/legacy/, verbatim
copies from branches front-match, scaffold-951, tractability) on all instance JSONs (tests/instances/)
and on random circuits, plus property tests.

    python3 tools/w951/tests/test_w951.py          (or: pytest tools/w951/tests)
"""
import contextlib
import copy
import glob
import io
import itertools
import json
import os
import random
import sys
import tempfile
import unittest
import warnings

warnings.simplefilter('ignore', ResourceWarning)

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(os.path.dirname(HERE)))     # .../tools
sys.path.insert(0, HERE)

import w951                                                     # noqa: E402
from w951 import Circuit, systems, matching, z_of, bits, CONST0, CONST1   # noqa: E402
from w951 import lp, rules                                      # noqa: E402
from legacy_loader import L                                     # noqa: E402

TOL = 1e-9
BIG_N = 11            # legacy functions that enumerate 2^n or 3^(n-|S|) points are skipped above this


def quiet(f, *a, **k):
    with contextlib.redirect_stdout(io.StringIO()):
        return f(*a, **k)


def instances():
    out = []
    for f in sorted(glob.glob(os.path.join(HERE, 'instances', '*.json'))):
        out.append((os.path.basename(f)[:-5], Circuit.from_dict(json.load(open(f)))))
    return out


INST = instances()
SMALL = [(nm, c) for nm, c in INST if c.n <= BIG_N]


def D(c):
    """Fresh normalised JSON dict (the legacy scripts get what their own `norm` would give them)."""
    return copy.deepcopy(c.to_dict())


def close(a, b, tol=TOL):
    """Structural equality with a float tolerance."""
    if isinstance(a, float) or isinstance(b, float):
        if a is None or b is None:
            return a is b
        return a == b or abs(a - b) <= tol
    if isinstance(a, dict) and isinstance(b, dict):
        return a.keys() == b.keys() and all(close(a[k], b[k], tol) for k in a)
    if isinstance(a, (list, tuple)) and isinstance(b, (list, tuple)):
        return len(a) == len(b) and all(close(x, y, tol) for x, y in zip(a, b))
    return a == b


# ------------------------------------------------------------------ random circuits
def rand_sets(rng, n):
    sets, tries = [], 0
    while tries < 30 and len(sets) < rng.randint(1, 4):
        tries += 1
        S = sorted(rng.sample(range(n), rng.randint(2, min(4, n))))
        if all(len(set(S) & set(T)) <= 1 for T in sets):
            sets.append(S)
    return sets


def rand_circuit(rng, n=None, s=None):
    """Arbitrary one-NOT circuit (not correct): for the syntactic definitions."""
    n = n or rng.randint(3, 6)
    s = s or rng.randint(4, 14)
    p = rng.randrange(s)
    gates = []
    for k in range(s):
        if k == p:
            gates.append(['not', rng.randrange(n + k)])
        else:
            gates.append([rng.choice(['and', 'or']), rng.randrange(n + k), rng.randrange(n + k)])
    sets = rand_sets(rng, n)
    outs = [rng.randrange(n, n + s) for _ in sets]
    return Circuit(n, gates, sets, outs)


def rand_correct(rng, n=None):
    """Correct one-NOT circuit: OR trees, then identities f = (f | (h & g)) & (f | N) and
    f = (f & h) | (f & N) with N = not h spliced in at random wires."""
    n = n or rng.randint(4, 7)
    sets = rand_sets(rng, n)
    G = []
    add = lambda op, *a: (G.append([op, *a]), n + len(G) - 1)[1]
    hs = rng.sample(range(n), rng.randint(1, 2))
    h = hs[0]
    for v in hs[1:]:
        h = add('or', h, v)
    N = add('not', h)

    def gadget(f):
        r = rng.random()
        if r < 0.35:
            g = rng.randrange(n + len(G))
            return add('and', add('or', f, add('and', h, g)), add('or', f, N))
        if r < 0.7:
            return add('or', add('and', f, h), add('and', f, N))
        return f
    outs = []
    for S in sets:
        vs = list(S)
        rng.shuffle(vs)
        f = vs[0]
        for v in vs[1:]:
            f = add('or', f, v)
            if rng.random() < 0.5:
                f = gadget(f)
        if f < n or rng.random() < 0.5:
            f = add('or', add('and', f, h), add('and', f, N))
        outs.append(f)
    return Circuit(n, G, sets, outs)


def mutate(rng, c, maxs):
    """The climb scripts' moves (insert a gate and reroute a reader / retarget an input)."""
    n, G, O = c.n, [list(g) for g in c.gates], list(c.outs)
    s = len(G)
    if rng.random() < 0.5 and s < maxs:
        k = rng.randint(0, s)
        Wk = n + k
        a, b = rng.randrange(Wk), rng.randrange(Wk)
        if a == b:
            return None
        G2 = [[g[0]] + [x + 1 if x >= Wk else x for x in g[1:]] for g in G]
        G2.insert(k, [rng.choice(['and', 'or']), a, b])
        O2 = [o + 1 if o >= Wk else o for o in O]
        readers = [(i, j) for i in range(k + 1, len(G2)) for j in range(1, len(G2[i]))]
        if not readers:
            return None
        i, j = rng.choice(readers)
        G2[i][j] = Wk
        return Circuit(n, G2, c.sets, O2)
    i = rng.randrange(s)
    j = rng.randint(1, len(G[i]) - 1)
    G[i][j] = rng.randrange(n + i)
    if G[i][0] != 'not' and rng.random() < 0.3:
        G[i][0] = 'and' if G[i][0] == 'or' else 'or'
    return Circuit(n, G, c.sets, O)


def walk(rng, c, steps, maxs):
    """Mutants of c that stay correct, essential, clean and fully read (the climbs' invariant)."""
    out, cur = [], c
    for _ in range(steps):
        m = mutate(rng, cur, maxs)
        if m is None or not (m.is_correct() and m.is_essential() and m.is_clean() and m.all_read()):
            continue
        cur = m
        out.append(m)
    return out


_rng = random.Random(951)
RAND_ANY = [rand_circuit(_rng) for _ in range(150)]
RAND_OK = [c for c in (rand_correct(_rng) for _ in range(120)) if c.sets]
_seeds = {nm: c for nm, c in INST}
WALK = (walk(random.Random(1), _seeds['front-match__w8__cx2'], 6000, 22)[::4][:25]
        + walk(random.Random(2), _seeds['front-match__w8__cx1'], 6000, 26)[::4][:15])
# circuits on which the LP / menu comparisons run (correct, exactly one NOT)
LPSET = [(nm, c) for nm, c in SMALL] + [('rand%d' % i, c) for i, c in enumerate(RAND_OK[:40])] \
    + [('walk%d' % i, c) for i, c in enumerate(WALK)]


class TestCircuit(unittest.TestCase):
    def check_eval(self, c, pts):
        n, dn, tr = c.n, D(c), c.triples()
        t0, t1, t = c.tables(0), c.tables(1), c.tables()
        for pt in pts:
            x = [pt >> i & 1 for i in range(n)]
            w = c.eval(pt)
            self.assertEqual(w, c.eval(x))
            self.assertEqual(w, L.verify.evalN(n, dn['gates'], x))
            self.assertEqual(w, L.chargeok_check.evaluate(n, dn['gates'], x))
            self.assertEqual(w, L.rstar.ev(n, dn['gates'], x))
            self.assertEqual(w, L.fa_lib.ev(n, dn['gates'], x))
            self.assertEqual(w, L.fc_lib.ev(n, dn['gates'], x))
            self.assertEqual(w, L.tw.ev(n, dn['gates'], x))
            self.assertEqual(w, L.top2.ev(n, dn['gates'], x))
            self.assertEqual(w, L.gen_clean.ev(n, tr, x))
            self.assertEqual(w, L.climbrel.ev(n, dn['gates'], pt))
            self.assertEqual(w, [t[i] >> pt & 1 for i in range(c.W)])
            self.assertEqual(w, bits_to_list(c.point_mask(pt), c.W))
            for f, tf in ((0, t0), (1, t1)):
                wf = c.eval(pt, f)
                self.assertEqual(wf, L.verify.evalN(n, dn['gates'], x, f))
                self.assertEqual(wf, L.fa_lib.ev(n, dn['gates'], x, f))
                self.assertEqual(wf, L.climbrel.ev(n, dn['gates'], pt, f))
                self.assertEqual(wf, [tf[i] >> pt & 1 for i in range(c.W)])
            if L.have_sat:
                self.assertEqual(w, L.ov951.wires(n, tr, pt))

    def test_eval_instances(self):
        rng = random.Random(0)
        for nm, c in INST:
            with self.subTest(nm):
                pts = range(1 << c.n) if c.n <= 8 else [rng.randrange(1 << c.n) for _ in range(150)]
                self.check_eval(c, pts)

    def test_eval_random(self):
        for c in RAND_ANY[:60] + RAND_OK[:30]:
            self.check_eval(c, range(1 << c.n))

    def check_tables(self, c):
        dn = D(c)
        self.assertEqual((c.tables(), c.full), L.sand.tts(dn))
        if c.n <= BIG_N:
            T = L.resid.tables(dn)                              # per wire, product order
            for i in range(c.W):
                self.assertEqual(list(c.table_in_product_order(i)), T[i])
            self.assertEqual([c.table_in_product_order(i) for i in range(c.W)], L.clean.tables(dn))
            X, Wt = L.fc_relrule.tables(dn)
            self.assertEqual([tuple(w[i] for w in Wt) for i in range(c.W)],
                             [c.table_in_product_order(i) for i in range(c.W)])
            self.assertEqual(L.ana.table(c.n, c.triples()), [c.eval(x) for x in range(1 << c.n)])
            self.assertEqual(L.rel.tt(dn), [c.eval(x) for x in range(1 << c.n)])

    def test_tables(self):
        for nm, c in INST:
            with self.subTest(nm):
                self.check_tables(c)
        for c in RAND_ANY[:40]:
            self.check_tables(c)

    def check_structure(self, c):
        n, dn, tr = c.n, D(c), c.triples()
        for o in range(c.W):
            co = set(c.cone(o))
            self.assertEqual(co, L.chargeok_check.cone(n, dn['gates'], o))
            self.assertEqual(co, L.tw.cone(n, dn['gates'], o))
            self.assertEqual(co, L.fc_lib.cone(n, dn['gates'], o))
            self.assertEqual(co, L.irr.cone(n, dn['gates'], o))
            self.assertEqual(co, L.gen.cone(n, tr, o))
            self.assertEqual(co, L.ana.cone(n, tr, o))
        if c.nots:
            self.assertEqual(set(c.downstream()), L.sig.down(dn))
            self.assertEqual(c.not_wire, L.fa_lib.nw(dn))
            self.assertEqual(c.h_wire, L.fa_lib.hw(dn))
        rd = c.readers()
        for w in range(c.W):
            self.assertEqual(rd[w], [n + k for k, g in enumerate(c.gates) if w in g[1:]])

    def test_cones_down_readers(self):
        for nm, c in INST:
            with self.subTest(nm):
                self.check_structure(c)
        for c in RAND_ANY:
            self.check_structure(c)

    def check_verify(self, c, full=True):
        dn = D(c)
        v = c.verify()
        self.assertEqual(v, L.verify.verify(dn))
        self.assertEqual(L.fa_lib.verify(dn), (v['correct'], not v['C0'], not v['C1']))
        if c.sets:
            self.assertEqual(L.gen.essential(c.n, c.sets, c.triples(), c.outs), c.is_essential())
            self.assertEqual(L.climbr.tt_ok(dn), v['correct'] and v['clean'] and c.is_essential() and v['read'])
            self.assertEqual(L.climbrel.ok(dn), v['correct'] and c.is_essential() and c.not_is_live())
        if full:
            self.assertEqual(c.verify_full(), L.fc_lib.verify(dn))

    def test_verify_instances(self):
        for nm, c in INST:
            with self.subTest(nm):
                self.check_verify(c)

    def test_verify_random(self):
        for c in RAND_ANY[:80]:
            self.check_verify(c, full=False)
        for c in RAND_OK + WALK:
            self.check_verify(c)

    def test_io_roundtrip(self):
        with tempfile.TemporaryDirectory() as d:
            for nm, c in INST[:6]:
                p = os.path.join(d, nm + '.json')
                w951.save(c, p)
                self.assertEqual(w951.load(p), [c])
                self.assertEqual(Circuit.from_dict(c.to_dict(not_arity=3)), c)
                self.assertEqual(Circuit.from_dict({'score': 1, 'c': c.to_dict()}), c)
                self.assertEqual(L.fa_lib.load(p)[0], c.to_dict())
            pl = os.path.join(d, 'all.jsonl')
            for nm, c in INST:
                w951.save(c, pl)
            self.assertEqual(w951.load(pl), [c for _, c in INST])
            self.assertEqual(L.tw.load(pl), [c.to_dict() for _, c in INST])
        raw = json.load(open(os.path.join(HERE, 'instances', 'scaffold-951__payment__ce1.json')))
        self.assertEqual(Circuit.from_dict(raw).to_dict(), L.conedbl.norm(copy.deepcopy(raw)))


def bits_to_list(m, W):
    return [m >> i & 1 for i in range(W)]


class TestTransform(unittest.TestCase):
    def check_reduced(self, c, r):
        d = r.detail
        self.assertEqual(r.removed, c.s - r.circuit.s)
        self.assertEqual(r.removed, len(d['const']) + len(d['merged']) + len(d['dead']))
        self.assertEqual(len(set(d['const']) | set(d['merged']) | set(d['dead'])), r.removed)
        r.circuit.validate(sums=False)

    def check_restrict(self, c, legacy=True):
        dn = D(c)
        t = c.tables()
        for v in range(c.n):
            for b in (0, 1):
                r = c.restrict(v, b)
                self.check_reduced(c, r)
                if legacy:
                    self.assertEqual(r.circuit.s, L.kill.restr(dn, v, b))
                # semantics: on the subcube x_v = b every surviving old wire equals its image
                M = t[v] if b else c.full ^ t[v]
                tn = r.circuit.tables()
                for i in range(c.W):
                    a = r.wire_map[i]
                    if a is None:
                        continue
                    want = t[i] & M
                    got = (M if a[1] else 0) if isinstance(a, tuple) else tn[a] & M
                    self.assertEqual(want, got)
                # no two kept wires agree on the subcube, none is constant there (nothing more to merge)
                kept = [tn[i] & M for i in range(r.circuit.W) if i != v]
                self.assertEqual(len(set(kept)), len(kept))
                self.assertTrue(all(0 < x < M for x in kept))
                if c.is_correct():
                    for S, o in zip(r.circuit.sets, r.circuit.outs):
                        self.assertEqual(tn[o] & M, r.circuit.or_table(S) & M)
                    self.assertEqual(len(r.circuit.sets), len(c.sets) - (r.detail['through'] if b else 0))
                # syntactic restriction (constant propagation only): same semantics
                r2 = c.restrict(v, b, semantic=False)
                self.check_reduced(c, r2)
                tn2 = r2.circuit.tables()
                for i in range(c.W):
                    a = r2.wire_map[i]
                    if a is not None:
                        self.assertEqual(t[i] & M, (M if a[1] else 0) if isinstance(a, tuple) else tn2[a] & M)

    def test_restrict_instances(self):
        for nm, c in SMALL:
            with self.subTest(nm):
                self.check_restrict(c)

    def test_restrict_random(self):
        for c in RAND_ANY[:60] + RAND_OK[:40] + WALK[:20]:
            self.check_restrict(c)

    def check_propagate(self, c, rng):
        n, tr, nw, hw = c.n, c.triples(), c.not_wire, c.h_wire
        p = nw - n
        t = c.tables()
        msets = []
        if n <= 9:                                              # the minterms of h, as restr951.py:49-52
            msets += [bits(x) for x in range(1 << n) if t[hw] >> x & 1
                      and all(not t[hw] >> (x & ~(1 << i)) & 1 for i in bits(x))][:12]
        msets += [rng.sample(range(n), rng.randint(0, 3)) for _ in range(6)]
        for Mset in msets:
            keep = [i for i, S in enumerate(c.sets) if not set(S) & set(Mset)]
            r = c.propagate({**{v: 1 for v in Mset}, nw: 0}, keep=keep)
            self.assertEqual(r.circuit.s, L.restr951.restrict_count(n, tr, list(c.outs), p, Mset, keep))
            self.assertEqual(r.removed, len(r.detail['const']) + len(r.detail['merged']) + len(r.detail['dead']))
            # semantics on the subcube, with the NOT forced to 0
            M = c.full
            for v in Mset:
                M &= t[v]
            t0, tn = c.tables(0), r.circuit.tables()
            for i in range(c.W):
                a = r.wire_map[i]
                if a is not None:
                    self.assertEqual(t0[i] & M, (M if a[1] else 0) if isinstance(a, tuple) else tn[a] & M)

    def test_propagate(self):
        rng = random.Random(5)
        for nm, c in INST:
            with self.subTest(nm):
                self.check_propagate(c, rng)
        for c in RAND_ANY + RAND_OK[:40]:
            self.check_propagate(c, rng)

    def check_dead_cleanup(self, c):
        dn = D(c)
        r = c.remove_dead()
        self.assertEqual(r.circuit.to_dict(), L.cfgI.prune(D(c)))
        self.assertEqual(r.removed, len(r.detail['dead']))
        try:
            want = L.clean.cleanup(dn)
        except KeyError:                                        # the script crashes when a duplicate's
            want = None                                         # original is itself unread
        cl = c.cleanup()
        if want is not None:
            self.assertEqual(cl.circuit.to_dict(), {k: want[k] for k in ('n', 'sets', 'gates', 'outs')})
        t, tn = c.tables(), cl.circuit.tables()
        self.assertEqual([t[o] for o in c.outs], [tn[o] for o in cl.circuit.outs])
        self.assertEqual(len(set(tn[c.n:])), cl.circuit.s)
        self.assertTrue(cl.circuit.all_read())
        self.assertEqual(cl.removed, len(cl.detail['merged']) + len(cl.detail['dead']))

    def test_remove_dead_cleanup(self):
        n_legacy = 0
        for nm, c in SMALL:
            with self.subTest(nm):
                self.check_dead_cleanup(c)
        for c in RAND_ANY + RAND_OK:
            self.check_dead_cleanup(c)

    def check_delete_outputs(self, c):
        m, t = len(c.sets), c.tables()
        if m >= 2:
            self.assertEqual(systems.maxviol(c), L.irr.maxviol(D(c)))
        for r_ in range(0, m + 1):
            for F in itertools.combinations(range(m), r_):
                r = c.delete_outputs(F)
                rest = set().union(*[c.cone(c.outs[w]) for w in range(m) if w not in F]) if len(F) < m else set()
                self.assertEqual(r.removed, c.s - len(rest))
                self.assertEqual(sorted(r.detail['dead']), sorted(set(c.gate_wires) - rest))
                self.assertEqual(r.circuit.sets, tuple(c.sets[w] for w in range(m) if w not in F))
                tn = r.circuit.tables()
                self.assertEqual([tn[o] for o in r.circuit.outs], [t[c.outs[w]] for w in range(m) if w not in F])
                self.assertTrue(r.circuit.all_read())
                for i in rest:
                    self.assertEqual(tn[r.wire_map[i]], t[i])

    def test_delete_outputs(self):
        for nm, c in INST:
            with self.subTest(nm):
                self.check_delete_outputs(c)
        for c in RAND_ANY[:80] + RAND_OK[:40]:
            self.check_delete_outputs(c)

    def test_drop_gate(self):
        """drop_gate(k, j) on a gate that copies wire j keeps every wire's function (Cleanup.lean val_dropGate)."""
        k_tested = 0
        for c in RAND_ANY + RAND_OK:
            t = c.tables()
            for k in range(c.s):
                js = [j for j in range(c.n + k) if t[j] == t[c.n + k]]
                if not js:
                    continue
                r = c.drop_gate(k, js[0])
                tn = r.circuit.tables()
                self.assertEqual([tn[r.wire_map[i]] for i in range(c.W)], t)
                self.assertEqual(r.circuit.s, c.s - 1)
                k_tested += 1
        self.assertGreater(k_tested, 50)


class TestSystems(unittest.TestCase):
    def check_counted(self, c, rng, has_canon=True):
        n, dn = c.n, D(c)
        self.assertEqual(systems.rstar(c), L.rstar.rstar(dn))
        for wi, S in enumerate(c.sets):
            rest = [v for v in range(n) if v not in S]
            for _ in range(6):
                z = sum(1 << v for v in rest if rng.random() < 0.5)
                zl = [z >> i & 1 for i in range(n)]
                got = systems.cnt_z(c, wi, z)
                self.assertEqual(got, L.rstar.cnt_z(dn, wi, zl))
                self.assertEqual(set(got), L.top2.cntz(n, dn['gates'], S, zl))
                self.assertEqual(got, L.tw.cnt(n, dn['gates'], S, zl))
                K = c.cone(c.outs[wi])
                self.assertEqual(systems.cnt_unit(c, S, z, K), L.tw.cnt(n, dn['gates'], S, zl, K, unit=True))
        try:
            want = L.hallcheck.canon(dn)
        except Exception:
            return
        self.assertEqual(systems.canon(c), want)
        if None not in want:
            Q = L.tw.canonQ(dn)
            self.assertEqual([(q[0], z_of(n, q[0]), set(q[2])) for q in systems.canon_Q(c)],
                             [(q[0], sum(b << i for i, b in enumerate(q[1])), q[2]) for q in Q])
            self.assertEqual(systems.worlds(c), L.tw.worlds(dn))

    def test_counted_instances(self):
        rng = random.Random(3)
        for nm, c in INST:
            with self.subTest(nm):
                self.check_counted(c, rng)

    def test_counted_random(self):
        rng = random.Random(4)
        for c in RAND_ANY + RAND_OK + WALK:
            self.check_counted(c, rng)

    def check_min_good(self, c):
        dn = D(c)
        self.assertEqual(systems.chargeok(c), L.chargeok_check.check(dn))
        try:
            want = L.conedbl.analyse(dn)
        except TypeError:                                       # no Good Q for some set: the script crashes
            want = None
        if want is not None:
            self.assertEqual(systems.conedbl(c), want)
        try:
            want = L.gen_clean.slack(c.n, c.sets, c.triples())
        except TypeError:
            want = None
        if want is not None:
            self.assertEqual(systems.lean_slack(c), want)

    def test_min_good_instances(self):
        for nm, c in SMALL:
            with self.subTest(nm):
                self.check_min_good(c)
        self.assertEqual(systems.chargeok(L.chargeok_check.PASCH), L.chargeok_check.check(L.chargeok_check.PASCH))

    def test_min_good_random(self):
        for c in RAND_ANY + RAND_OK + WALK:
            self.check_min_good(c)

    def check_menus(self, c):
        dn = D(c)
        for cone in (False, True):
            M, M0 = systems.menus(c, cone), L.allsys.menus(dn, cone)
            self.assertEqual(M, M0)
            self.assertEqual([list(m.items()) for m in M], [list(m.items()) for m in M0])   # order + witnesses
            self.assertEqual(systems.menu_witnesses(c, cone), L.resid.full(dn, cone))
        self.assertEqual(systems.menu_sets(c), [sorted(sorted(x) for x in m) for m in M0 and L.allsys.menus(dn)])
        self.assertEqual(systems.priv(c), L.priv.priv(dn))

    def test_menus_instances(self):
        for nm, c in SMALL:
            with self.subTest(nm):
                self.check_menus(c)

    def test_menus_random(self):
        for c in RAND_ANY[:100] + RAND_OK[:60] + WALK:
            self.check_menus(c)

    def check_nsets_gapg(self, c):
        dn = D(c)
        self.assertEqual(systems.nsets(c), L.nsets.analyse(dn))
        for wi in range(len(c.sets)):
            got = systems.gapg_systems(c, wi)
            want = L.gapg_check.systems(dn, wi)
            self.assertEqual(got, want)
        self.assertEqual(systems.gapg(c), L.gapg_check.gapg(dn))
        self.assertEqual(systems.gapg(c, allow_B=False), L.needsB.choice(dn, False))
        self.assertEqual(systems.gapg(c, allow_B=True), L.needsB.choice(dn, True))
        for perm in (False, True):
            self.assertEqual(systems.good_Qs(c, perm), L.fc_lib.goodQs(dn, perm))
            self.assertEqual(systems.family(c, perm), L.fc_lib.family(dn, perm))

    def test_nsets_gapg_instances(self):
        for nm, c in SMALL:
            with self.subTest(nm):
                self.check_nsets_gapg(c)

    def test_nsets_gapg_random(self):
        for c in RAND_ANY + RAND_OK + WALK:
            self.check_nsets_gapg(c)

    def test_system_merges(self):
        """fa/lib `system` + `merges` on the canonical frame (z_Q, unit atoms)."""
        k = 0
        for nm, c in SMALL + [('r', x) for x in RAND_OK + WALK]:
            dn = D(c)
            for wi, (S, q) in enumerate(zip(c.sets, systems.canon_Q(c))):
                if q is None:
                    continue
                z = [0 if v in q[0] else 1 for v in range(c.n)]
                atoms = {u: L.fa_lib.unit(c.n, u) for u in S}
                want = L.fa_lib.system(dn, S, z, atoms)
                got = systems.system(c, S, z, atoms)
                self.assertEqual(got, want)
                self.assertEqual(systems.system(c, S, q[1], {u: 1 << u for u in S}), want)
                try:
                    wm = L.fa_lib.merges(dn, S, want[2])
                except AssertionError:
                    with self.assertRaises(AssertionError):
                        systems.merges(c, S, got[2])
                    continue
                self.assertEqual(systems.merges(c, S, got[2]), wm)
                k += 1
        self.assertGreater(k, 100)


class TestMatching(unittest.TestCase):
    def test_tractability_suite(self):
        """tools/matching/test_matching.py (tractability) run against the copied module."""
        path = os.path.join(HERE, 'legacy', 'tractability', 'tools', 'matching', 'test_matching.py')
        saved = sys.modules.get('matching')
        sys.modules['matching'] = matching
        try:
            ns = {'__name__': 'legacy_test_matching', '__file__': path}
            exec(compile(open(path).read(), path, 'exec'), ns)
            for k, f in sorted(ns.items()):
                if k.startswith('test_') and callable(f):
                    quiet(f)
        finally:
            if saved is None:
                sys.modules.pop('matching', None)
            else:
                sys.modules['matching'] = saved

    def test_hall_vs_bmatch_copies(self):
        k = 0
        for nm, c in SMALL + [('r', x) for x in RAND_OK + WALK]:
            dem = c.demands
            fams = [systems.rstar(c)]
            Dc = systems.canon(c)
            if None not in Dc:
                fams.append(Dc)
            M = systems.menus(c)
            for combo in itertools.islice(itertools.product(*[list(m) for m in M]), 20):
                fams.append([sorted(x) for x in combo])
            for Ds in fams:
                got = rules.hall(Ds, dem)
                self.assertEqual(got, L.hallcheck.bmatch(Ds, dem))
                self.assertEqual(got, L.allsys.bmatch(Ds, dem))
                self.assertEqual(got, L.rstar.bmatch(Ds, dem))
                self.assertEqual(got, L.tw.bmatch(Ds, dem, 1))
                a, s = matching.bmatch(Ds, dem)
                self.assertEqual(a is not None, got == sum(dem))
                k += 1
        self.assertGreater(k, 500)

    def test_two_world(self):
        """rules.two_world (max-flow) against tw.twoworld (augmenting search with the one-unit-per-(system, gate)
        rule), and against brute-force Hall and frac_feasible_half."""
        diff = n = 0
        for nm, c in SMALL + [('r', x) for x in RAND_OK + WALK]:
            dn = D(c)
            Dc, Dr = systems.worlds(c)
            if None in Dc:
                continue
            ok, got, tot = rules.two_world(c)
            ok0, got0, tot0 = L.tw.twoworld(dn)
            self.assertEqual(tot, tot0)
            self.assertEqual((ok, got), (ok0, got0))
            dem = c.demands
            # exactness of ours: brute-force Hall (simple, capacity 2) agrees
            if len(dem) <= 5:
                self.assertEqual(ok, matching.hall_check(Dc + Dr, dem + dem, 2, simple=True) is None)
            self.assertEqual(ok, matching.frac_feasible_half(list(zip(Dc, Dr)), dem)[0])
            self.assertEqual(rules.union_hall(c, Dc, Dr), L.tw.unionhall(dn, Dc, Dr))
            n += 1
            diff += got != got0
        TestMatching.two_world_stats = (n, diff)
        self.assertGreater(n, 100)


class TestLP(unittest.TestCase):
    def test_fraclp(self):
        worst = 0.0
        for nm, c in LPSET:
            with self.subTest(nm):
                dn = D(c)
                for cone in (False, True):
                    L0, lam0, M0 = L.fraclp.fraclp(dn, cone)
                    L1, lam1, M1 = lp.fraclp(c, cone)
                    self.assertEqual(M0, M1)
                    self.assertTrue(close(L0, L1) and close(lam0, lam1), (L0, L1))
                    worst = max(worst, abs(L0 - L1))
                    M = [list(m) for m in M1]
                    r = lp.min_max_load(M, c.demands)
                    self.assertTrue(close((r.L, r.pi, r.mu, r.lam, r.load), L.dual.lp(M, c.demands)))
                    self.assertAlmostEqual(sum(r.pi.values()), 1.0, places=7)
        TestLP.fraclp_maxdiff = worst

    def test_lp_caps_fixed(self):
        rng = random.Random(8)
        for nm, c in LPSET[:40]:
            M = [list(m) for m in systems.menus(c)]
            gates = sorted({g for m in M for C in m for g in C})
            cap = {g: rng.choice([1, 2, 3]) for g in gates if rng.random() < 0.5}
            fixed = {g: rng.choice([0.5, 1.0]) for g in rng.sample(gates, min(2, len(gates)))}
            for kw in (dict(cap=cap), dict(fixed=fixed), dict(cap=cap, fixed=fixed)):
                want = L.dual.lp(M, c.demands, **kw)
                r = lp.min_max_load(M, c.demands, **kw)
                if want is None:
                    self.assertNotEqual(r.status, 0)
                else:
                    self.assertTrue(close((r.L, r.pi, r.mu, r.lam, r.load), want), nm)

    def test_mix(self):
        for nm, c in LPSET:
            if None in systems.canon(c):
                continue
            with self.subTest(nm):
                dn = D(c)
                for a in (0.5, 0.3, 0.7):
                    self.assertTrue(close(rules.mix(c, a), L.mixrule.mix(dn, a)))
                Dc, Dr = systems.worlds(c)
                half = rules.mix(c, 0.5)
                self.assertEqual(half <= 1 + 1e-7, matching.frac_feasible_half(list(zip(Dc, Dr)), c.demands)[0])

    def test_dual(self):
        for nm, c in LPSET:
            with self.subTest(nm):
                M = systems.menu_sets(c)
                dem = c.demands
                D0, D1 = L.dualp.Dual(M, dem), lp.Dual(M, dem)
                s0, s1 = D0.solve(), D1.solve()
                self.assertTrue(close(s0, s1))
                self.assertTrue(close(L.dualp.ratio(s0[1], M, dem), lp.ratio(s1[1], M, dem)))
                self.assertAlmostEqual(lp.ratio(s1[1], M, dem), s1[0], places=6)        # strong duality
                self.assertAlmostEqual(lp.min_max_load(M, dem).L, s1[0], places=6)
                self.assertTrue(close(D0.flat(s0[0]), D1.flat(s1[0])))
                self.assertTrue(close(D0.sparse(s0[0], random.Random(1), 5), D1.sparse(s1[0], random.Random(1), 5)))
                want = L.resid.lpdual(M, dem)
                got = lp.lpdual(M, dem)
                self.assertTrue(close(want[:3], got[:3]))
                for g in D1.gates[:5]:
                    C = M[0][0]
                    self.assertEqual(lp.cheap(s1[1], C, dem[0]), L.dualp.cheap(s0[1], C, dem[0]))

    def test_residual(self):
        for nm, c in LPSET:
            with self.subTest(nm):
                want = quiet(L.resid.run, D(c), nm, False)
                want.pop('name')
                self.assertTrue(close(rules.residual(c), want))


class TestRules(unittest.TestCase):
    def check_classes(self, c, correct):
        dn = D(c)
        self.assertEqual(rules.private(c), tuple(L.resid.private(dn)))
        self.assertEqual(rules.roles(c), L.dualp.roles(dn))
        if correct:
            self.assertEqual(rules.sandwich_classes(c), L.sand.classes(dn))
            cls, T, H = L.rel.analyse(dn)
            self.assertEqual(rules.rel_classes(c), cls)

    def test_classes(self):
        for nm, c in SMALL:
            with self.subTest(nm):
                self.check_classes(c, True)
        for c in RAND_ANY:
            if c.sets:
                self.check_classes(c, False)
        for c in RAND_OK + WALK:
            self.check_classes(c, True)

    def check_relmenu(self, c):
        dn = D(c)
        for WT in (0, 1, 2):
            for above in (False, True):
                self.assertEqual(rules.relmenu(c, WT, above), L.relrule.relmenu(dn, WT, above))
        M, info = rules.relmenus_minimal(c)
        M0, info0 = L.fc_relrule.relmenus(dn)
        self.assertEqual((M, info), (M0, info0))
        self.assertEqual([list(m.items()) for m in M], [list(m.items()) for m in M0])

    def test_relmenu(self):
        for nm, c in SMALL:
            with self.subTest(nm):
                self.check_relmenu(c)
        for c in RAND_ANY[:80]:
            if c.sets:
                self.check_relmenu(c)
        for c in RAND_OK + WALK:
            self.check_relmenu(c)

    def test_rel_rule(self):
        vals = {}
        for nm, c in LPSET:
            with self.subTest(nm):
                dn = D(c)
                for WT in (1, 2):
                    want = L.relrule.run(dn, nm, WT, False, False)
                    got = rules.rel_rule(c, WT)
                    self.assertTrue(close(got, want), (nm, got[0], want[0]))
                vals[nm] = got[0]
        TestRules.rel_vals = vals

    def test_xrule(self):
        for nm, c in LPSET:
            with self.subTest(nm):
                self.assertEqual(rules.xrule(c), L.xrule.xrule(D(c)))


@unittest.skipUnless(L.have_sat, 'python-sat not installed')
class TestSat(unittest.TestCase):
    CASES = [(3, [(0, 1), (0, 2), (1, 2)], 4), (3, [(0, 1), (0, 2), (1, 2)], 5), (4, [(0, 1, 2), (2, 3)], 5),
             (4, [(0, 1), (0, 2), (0, 3)], 5)]

    def test_clauses_identical(self):
        from w951 import sat
        for n, sets, s in self.CASES:
            for p in range(s - 1):
                blocks = [[1, -2], [3]]
                self.assertEqual(sat.build(n, sets, s, p, blocks), L.ov951.build(n, sets, s, p, blocks))
                with contextlib.ExitStack() as st:
                    cwd = os.getcwd()
                    self.assertEqual(sat.build(n, sets, s, p, blocks, live=True),
                                     L.live951.build_live(n, sets, s, p, blocks))
                    self.assertEqual(sat.build(n, sets, s, p, blocks, live=True, clean=True),
                                     L.clean951.build_clean(n, sets, s, p, blocks))

    def test_enumerate(self):
        from w951 import sat
        from pysat.solvers import Cadical153
        n, sets, s = 3, [(0, 1), (0, 2), (1, 2)], 6
        found = 0
        for p in range(s - 1):
            cl, SEL, O = sat.build(n, sets, s, p, live=True, clean=True)
            sol = Cadical153(bootstrap_with=cl)
            for _ in range(5):
                if not sol.solve():
                    break
                model = sol.get_model()
                gates, outs = sat.decode(model, n, s, p, SEL, O)
                self.assertEqual((gates, outs), L.ov951.decode(model, n, s, p, SEL, O))
                c = sat.decode_circuit(model, n, sets, s, p, SEL, O)
                self.assertTrue(c.is_correct() and c.is_clean() and c.not_is_live() and c.not_wire == n + p)
                sol.add_clause(sat.block(model, gates, outs, s, p, SEL, O))
                found += 1
            sol.delete()
        self.assertGreater(found, 5)
        cs = list(sat.enumerate_circuits(n, sets, s, 2, limit=4, clean=True))
        self.assertEqual(len(set(cs)), len(cs))
        self.assertTrue(all(c.is_correct() and c.not_is_live() for c in cs))


@unittest.skipUnless(L.have_sat, 'python-sat not installed')
class TestSatChannel(unittest.TestCase):
    SYS = [(3, [(0, 1), (0, 2), (1, 2)]), (3, [(0, 1, 2), (0, 1)]), (4, [(0, 1, 2), (2, 3)]),
           (4, [(0, 1), (0, 2), (0, 3)])]

    @staticmethod
    def solve(cl):
        from pysat.solvers import Cadical153
        with Cadical153(bootstrap_with=cl) as sol:
            return sol.get_model() if sol.solve() else None

    def base(self, n, sets):
        """smallest s (over all NOT positions) for which the channel encoding is satisfiable"""
        from w951 import sat
        for s in range(2, 12):
            if any(self.solve(sat.build_channel(n, sets, s, p)[0]) for p in range(s - 1)):
                return s

    def test_legacy_equivalence(self):
        from w951 import sat
        for n, sets in self.SYS:
            leg = L.chan_sat(n, sets)
            base = self.base(n, sets)
            self.assertIsNotNone(base)
            for s in (base - 1, base):
                if s < 2:
                    continue
                for p in range(s - 1):
                    cl, SEL, O = sat.build_channel(n, sets, s, p)
                    lcl, A, B, OP, LO = leg(s, p)
                    with self.subTest(n=n, sets=sets, s=s, p=p):
                        self.assertEqual(cl[:len(lcl)], lcl)                     # same clauses, same numbering
                        self.assertEqual(len(O[0]), n + s)
                        m, lm = self.solve(cl), self.solve(lcl)
                        self.assertEqual(m is None, lm is None)
                        if m is None:
                            continue
                        c = sat.decode_circuit(m, n, sets, s, p, SEL, O)
                        self.assertTrue(c.verify() and c.is_correct())
                        # the legacy model decodes (legacy chan_sat decode logic) to a verifying circuit as well
                        M = set(x for x in lm if x > 0)
                        gates = [('not', [i for i, v in enumerate(A[k]) if v in M][0]) if k == p else
                                 ('and' if OP[k] in M else 'or', [i for i, v in enumerate(A[k]) if v in M][0],
                                  [i for i, v in enumerate(B[k]) if v in M][0]) for k in range(s)]
                        outs = [n + [k for k, v in enumerate(o) if v in M][0] for o in LO]
                        lc = Circuit(n, gates, sets, outs)
                        self.assertTrue(lc.verify() and lc.is_correct())

    def test_agrees_with_quadratic(self):
        """channel SAT at size s  <=>  quadratic SAT at some size <= s (padding)  (ov951-style `build`)"""
        from w951 import sat
        for n, sets in self.SYS:
            base = self.base(n, sets)
            for s in (base - 1, base):
                if s < 2:
                    continue
                for p in range(s - 1):
                    a = self.solve(sat.build_channel(n, sets, s, p)[0]) is not None
                    b = self.solve(sat.build(n, sets, s, p)[0]) is not None
                    ok = a == b or (a and not b)                                  # channel may use padding gates
                    self.assertTrue(ok, (n, sets, s, p))
                    if a and not b:                                              # then the padded circuit shrinks
                        self.assertTrue(any(self.solve(sat.build(n, sets, t, q)[0]) is not None
                                            for t in range(2, s) for q in range(t - 1)))
                self.assertTrue(any(self.solve(sat.build(n, sets, s, p)[0]) for p in range(s - 1)) or s < base)

    def test_legacy_cx_clauses(self):
        """cx-type instance (cx2: n=7, 3 sets) at tiny s: identical clause lists to chan_sat.py"""
        from w951 import sat
        c = dict(INST)['front-match__w8__cx2']
        sets = [tuple(S) for S in c.sets]
        leg = L.chan_sat(c.n, sets)
        for s, p in ((3, 0), (4, 2)):
            cl = sat.build_channel(c.n, sets, s, p)[0]
            lcl = leg(s, p)[0]
            self.assertEqual(cl[:len(lcl)], lcl)

    def test_enumerate_channel(self):
        from w951 import sat
        n, sets = self.SYS[0]
        s = self.base(n, sets) + 1
        cs = list(sat.enumerate_circuits(n, sets, s, 2, limit=4, encoding='channel'))
        self.assertTrue(cs and len(set(cs)) == len(cs))
        self.assertTrue(all(c.verify() and c.not_is_live() and c.not_wire == n + 2 for c in cs))

    def test_clause_count(self):
        from w951 import sat
        n, sets, s, p = 6, [(0, 1, 2), (2, 3), (3, 4, 5), (0, 5)], 10, 3
        q = len(sat.build(n, sets, s, p)[0])
        ch = len(sat.build_channel(n, sets, s, p)[0])
        print('\nclauses n=6 s=10: quadratic %d, channel %d (x%.1f smaller)' % (q, ch, q / ch))
        self.assertLess(ch * 4, q)


class TestBig(unittest.TestCase):
    """cxT4 (n = 15, 47 gates): the legacy scripts that are still feasible at this size."""

    def test_cxT4(self):
        c = dict(INST)['front-match__fc__cxT4']
        dn = D(c)
        self.assertEqual(systems.rstar(c), L.rstar.rstar(dn))
        self.assertEqual(systems.canon(c), L.hallcheck.canon(dn))
        self.assertEqual(rules.sandwich_classes(c), L.sand.classes(dn))
        self.assertEqual(systems.nsets(c), L.nsets.analyse(dn))
        self.assertEqual(rules.relmenu(c, 1), L.relrule.relmenu(dn, 1))
        self.assertEqual(rules.private(c), tuple(L.resid.private(dn)))
        M, M0 = systems.menus(c), L.allsys.menus(dn)
        self.assertEqual([list(m.items()) for m in M], [list(m.items()) for m in M0])
        self.assertTrue(close(lp.fraclp(c, M=M)[:2], L.fraclp.fraclp(dn, M=M0)[:2]))
        self.assertTrue(close(rules.rel_rule(c), L.relrule.run(dn, 'cxT4', 2, False, False)))
        self.assertEqual(c.verify(), L.verify.verify(dn))
        self.assertEqual(rules.hall(systems.rstar(c), c.demands), L.rstar.bmatch(L.rstar.rstar(dn), c.demands))


def summary():
    print('instances: %d (n <= %d: %d)   random arbitrary: %d   random correct: %d   climb mutants: %d   LP set: %d'
          % (len(INST), BIG_N, len(SMALL), len(RAND_ANY), len(RAND_OK), len(WALK), len(LPSET)))
    if hasattr(TestLP, 'fraclp_maxdiff'):
        print('fraclp: max |L*_legacy - L*_new| = %g' % TestLP.fraclp_maxdiff)
    if hasattr(TestMatching, 'two_world_stats'):
        print('two_world: %d circuits, legacy value differs from max-flow on %d' % TestMatching.two_world_stats)
    print('L* (full menu) / L_rel (WT=2) per instance:')
    for nm, c in SMALL:
        Lst = lp.fraclp(c)[0]
        print('   %-42s n=%-2d s=%-2d base=%-2d L*=%.6f L_rel=%s' % (nm, c.n, c.s, c.base, Lst, '%.6f' % rules.rel_rule(c)[0]))


if __name__ == '__main__':
    prog = unittest.main(exit=False, verbosity=1)
    summary()
    sys.exit(0 if prog.result.wasSuccessful() else 1)
