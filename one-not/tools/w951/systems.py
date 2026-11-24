"""Test systems, counted sets and menus for L-meta-951 (one definition each).

A test system for a set S is a zero point z (z = 0 on S) and one atom p_u per u in S (p_u(u) = 1);
a gate g is COUNTED if g(z) = 0 and g(p_u) = 1 for at least two u in S, within a wire set K.
Everything below is a choice of (z, atoms, K) plus a "Good" side condition on the NOT gate.

Points are ints (bit i = x_i), wires are ints, counted sets are sorted lists unless noted.
Functions take a `Circuit` or the JSON dict.
"""
from collections import Counter
from itertools import chain, combinations, product

from .circuit import as_circuit, bits, z_of

__all__ = ['counted', 'cnt_z', 'cnt_unit', 'rstar', 'good_zero_sets', 'canon_Q', 'canon', 'worlds',
           'chargeok', 'conedbl', 'lean_slack', 'menus', 'menu_sets', 'menu_witnesses',
           'nsets', 'gapg_systems', 'gapg', 'good_Qs', 'family', 'priv', 'system', 'merges', 'maxviol']


def _wires(mask, lo=0):
    return [i for i in bits(mask >> lo << lo)]


def _twice(masks):
    """Bits set in at least two of the int masks."""
    once = twice = 0
    for m in masks:
        twice |= once & m
        once |= m
    return twice


def _gate_mask(c, K=None):
    if K is None:
        return ((1 << c.W) - 1) >> c.n << c.n
    m = 0
    for i in K:
        if i >= c.n:
            m |= 1 << i
    return m


def counted_mask(c, S, z, atoms, K=None):
    """Bitmask (over wires) of the gates of K (default: all gates) with g(z) = 0 and g(atoms[u]) = 1
    for >= 2 u in S. `atoms` maps u -> point (dict or sequence aligned with S)."""
    pts = [atoms[u] for u in S] if isinstance(atoms, dict) else list(atoms)
    return _twice([c.point_mask(p) for p in pts]) & ~c.point_mask(z) & _gate_mask(c, K)


def counted(c, S, z, atoms, K=None):
    """Sorted counted set of the test system (z, atoms) for S within K (default all gates).
    Legacy: D_of (scaffold_opus/rules.py:25-29), the `cnt=` line of gapg_check.py:34."""
    c = as_circuit(c)
    return _wires(counted_mask(c, S, z, atoms, K))


def cnt_z(c, S, z, K=None):
    """System Σ(z): atoms z + e_u. Legacy: cnt_z (w8b/rstar.py:11-16), cntz (w9/fb/top2.py:13),
    cnt(..., unit=False) (w9/tw/tw.py:22-27). S: a set (list of inputs) or a set index."""
    c = as_circuit(c)
    if isinstance(S, int):
        S = c.sets[S]
    return _wires(counted_mask(c, S, z, [z | 1 << u for u in S], K))


def cnt_unit(c, S, z, K=None):
    """Zero point z, unit atoms e_u. Legacy: cnt(..., unit=True) (w9/tw/tw.py:22-27), the `d=`/`best=`
    lines of hallcheck.py:19, conedbl.py:22, chargeok_check.py:47."""
    c = as_circuit(c)
    if isinstance(S, int):
        S = c.sets[S]
    return _wires(counted_mask(c, S, z, [1 << u for u in S], K))


def rstar(c):
    """Rule R*: z_w = z_{S_w}, atoms z + e_u, K = all gates. Legacy: rstar (w8b/rstar.py:17-18),
    Dr of worlds (w9/tw/tw.py:42-47)."""
    c = as_circuit(c)
    return [cnt_z(c, S, z_of(c.n, S)) for S in c.sets]


# ---------------------------------------------------------------- Good zero sets Q ⊇ S (unit atoms)
def _du(c):
    """NOT false at every unit point (Lean's second Good disjunct)."""
    nw = c.not_wire
    return all(not c.value(nw, 1 << u) for u in range(c.n))


def good_zero_sets(c, w, good='cone_du'):
    """Yield (Q, z_Q) for the zero sets Q ⊇ S_w that are Good, in the legacy order (by |Q \\ S|, then
    lexicographically in the extra points). Q is a sorted tuple.
      good='strict'       NOT true at z_Q                                  (chargeok_check.py:45)
      good='du'           NOT true at z_Q, or NOT false at all units        (gen_clean.py:23)
      good='cone_du'      as 'du', but every Q is Good if the NOT is not in cone(o_w)
                          (hallcheck.py:18, conedbl.py:21, w9/tw/tw.py:36, gapg_check.py:21)
      good='cone_strict'  as 'strict', every Q Good if NOT not in cone(o_w)  (scaffold_opus/rules.py:37)
    """
    c = as_circuit(c)
    n, nw = c.n, c.not_wire
    R = set(c.sets[w])
    rest = [v for v in range(n) if v not in R]
    masked = good.startswith('cone') and (nw is None or nw not in c.cone(c.outs[w]))
    du = good.endswith('du') and nw is not None and _du(c)
    for r in range(len(rest) + 1):
        for ex in combinations(rest, r):
            Q = R | set(ex)
            z = z_of(n, Q)
            if masked or du or (nw is not None and c.value(nw, z)) or (nw is None):
                yield tuple(sorted(Q)), z


def canon_Q(c):
    """Per set: (Q, z_Q, cone(o_w)) for the FIRST Good ('cone_du') zero set, or None.
    Legacy: canonQ (w9/tw/tw.py:28-41)."""
    c = as_circuit(c)
    res = []
    for w in range(len(c.sets)):
        first = next(good_zero_sets(c, w, 'cone_du'), None)
        res.append(None if first is None else (set(first[0]), first[1], c.cone(c.outs[w])))
    return res


def canon(c):
    """Canonical counted sets: smallest Good Q ⊇ S_w (first in order), unit atoms, K = cone(o_w).
    None for a set without a Good Q. Legacy: canon (hallcheck.py:6-23), Dc of worlds (w9/tw/tw.py:42-47)."""
    c = as_circuit(c)
    return [None if q is None else cnt_unit(c, S, q[1], q[2]) for S, q in zip(c.sets, canon_Q(c))]


def worlds(c):
    """(Dc, Dr) = (canon(c), rstar(c)). Legacy: worlds (w9/tw/tw.py:42-47)."""
    return canon(c), rstar(c)


def _min_good(c, w, good, K):
    """First (Q, D) of minimum |D| over the Good zero sets (strict '<' as in the scripts)."""
    best = None
    for Q, z in good_zero_sets(c, w, good):
        d = cnt_unit(c, c.sets[w], z, K)
        if best is None or len(d) < len(best[1]):
            best = (list(Q), d)
    return best


def chargeok(c):
    """The charge inequality check of chargeok_check.py:24-56 `check`: returns (result, None) or
    (None, error). result = {'s', 'base', 'res': {'full'|'cone': (total, [(S sorted, (|D|, Q, D) | None)])}}
    with D of minimum size over Q ⊇ S with NOT true at z_Q ('strict'), K = all gates / cone(o_w)."""
    c = as_circuit(c)
    if len(c.nots) != 1:
        return None, "needs exactly one NOT gate (found %d)" % len(c.nots)
    if not c.is_correct():
        return None, "circuit incorrect"
    res = {}
    for variant in ('full', 'cone'):
        total, detail = 0, []
        for w, S in enumerate(c.sets):
            b = _min_good(c, w, 'strict', None if variant == 'full' else c.cone(c.outs[w]))
            if b is None:
                total = float('inf')
                detail.append((sorted(S), None))
            else:
                total += len(b[1])
                detail.append((sorted(S), (len(b[1]), b[0], b[1])))
        res[variant] = (total, detail)
    return {"s": c.s, "base": c.base, "res": res}, None


def conedbl(c):
    """conedbl.py:7-25 `analyse`: (slack = s - sum_w min |D|, {gate: multiplicity > 1}, info) with Good =
    'cone_du', K = cone(o_w); info[w] = (S sorted, (Q, D), NOT in cone(o_w))."""
    c = as_circuit(c)
    nw, mult, tot, info = c.not_wire, Counter(), 0, []
    for w, S in enumerate(c.sets):
        cone = c.cone(c.outs[w])
        b = _min_good(c, w, 'cone_du', cone)
        tot += len(b[1])
        mult.update(b[1])
        info.append((sorted(S), (b[0], b[1]), nw in cone))
    return c.s - tot, {k: v for k, v in mult.items() if v > 1}, info


def lean_slack(c):
    """s - sum_w min_{Q Good ('du')} |D(Q, S_w)| over all gates: the Lean inequality tested by
    slack (gen_clean.py:15-28)."""
    c = as_circuit(c)
    return c.s - sum(len(_min_good(c, w, 'du', None)[1]) for w in range(len(c.sets)))


# ---------------------------------------------------------------- the full menu (all Lean test systems)
def menus(c, coneonly=False):
    """ALL Lean test systems (z, fat atoms, K) per set; keeps the inclusion-maximal counted sets.

    Faithful port of menus (front-match work/notes951/scripts/w8/allsys.py:4-48), same enumeration
    order, so the witnesses agree too. Returns one dict per set:
        frozenset(counted gates) -> (z as a 0/1 tuple, [atom as (u, extra ones...)] per u in S)
    Systems: z any point with z = 0 on S; atom of u = e_u plus any subset of the ones of z; per u only
    the atoms that are undominated in (NOT value low, set of gates turned on high) are tried
    (allsys.py:23-32). A system is Good if NOT(z) = 1 or NOT is true at <= 1 atom; then K = all gates
    (coneonly: cone(o_w)). Otherwise, if o_w is not downstream of the NOT, K = the gates not downstream
    of the NOT (NOT-free K) (allsys.py:33-39). Requires exactly one NOT gate.
    """
    c = as_circuit(c)
    n, nw = c.n, c.not_wire
    if nw is None:
        raise ValueError('menus needs a NOT gate')
    gm = _gate_mask(c)
    down = _gate_mask(c, c.downstream())
    res = []
    for wi, R in enumerate(c.sets):
        cn = _gate_mask(c, c.cone(c.outs[wi]))
        rest = [v for v in range(n) if v not in R]
        cands = {}
        for zm in product([0, 1], repeat=len(rest)):
            ones = [v for v, b in zip(rest, zm) if b]
            zp = sum(1 << v for v in ones)
            wz = c.point_mask(zp)
            sig = {}
            for u in R:
                d = {}
                for T in chain.from_iterable(combinations(ones, r) for r in range(len(ones) + 1)):
                    wp = c.point_mask(1 << u | sum(1 << v for v in T))
                    d.setdefault((wp >> nw & 1, wp & ~wz & gm), (u,) + T)
                it = list(d.items())
                sig[u] = [a for a in it
                          if not any(b[0] != a[0] and b[0][0] <= a[0][0] and a[0][1] & ~b[0][1] == 0 for b in it)]
            zN = wz >> nw & 1
            for combo in product(*[sig[u] for u in R]):
                if zN == 1 or sum(k[0][0] for k in combo) <= 1:
                    K = cn if coneonly else gm
                elif not down >> c.outs[wi] & 1:
                    K = (cn if coneonly else gm) & ~down
                else:
                    continue
                cnt = _twice(k[0][1] for k in combo) & K
                if cnt not in cands:
                    cands[cnt] = (tuple(1 if zp >> v & 1 else 0 for v in range(n)), [k[1] for k in combo])
        mx = [x for x in cands if not any(x != y and x & ~y == 0 for y in cands)]
        res.append({frozenset(bits(x)): cands[x] for x in mx})
    return res


def menu_sets(c, coneonly=False):
    """Menus as sorted lists of sorted gate lists (no witnesses): the `M` of get_menus
    (tractability work/duals/dualp.py:10-15, without its pickle cache)."""
    return [sorted(sorted(x) for x in m) for m in menus(c, coneonly)]


def menu_witnesses(c, coneonly=False):
    """Per set the list of (sorted counted set, z tuple, h(z)), sorted by counted set.
    Legacy: full (tractability work/duals/resid.py:23-29)."""
    c = as_circuit(c)
    h = c.h_wire
    return [[(sorted(C), z, c.eval(list(z))[h]) for C, (z, at) in sorted(m.items(), key=lambda kv: sorted(kv[0]))]
            for m in menus(c, coneonly)]


def priv(c, M=None):
    """Rule PRIV (w9/fc/priv.py:6-12): per set (deficit, witness) where deficit = d_w - max_C |C minus the
    gates counted by any other set in any legal system|."""
    c = as_circuit(c)
    if M is None:
        M = menus(c, False)
    U = [set().union(*m) if m else set() for m in M]
    res = []
    for w, m in enumerate(M):
        oth = set().union(*[U[v] for v in range(len(M)) if v != w]) if len(M) > 1 else set()
        best = max(m, key=lambda C: len(C - oth))
        res.append((len(c.sets[w]) - 1 - len(best - oth), m[best]))
    return res


# ---------------------------------------------------------------- hard N-sets, Theorem X families, Gap-G
def nsets(c):
    """nsets.py:6-29 `analyse`: ('h0=1', None) | ('le1', k) | ('pairOK', k) | ('BAD', k), k = number of hard
    N-sets (NOT in cone(o_w) and h(z_S) = 1); pairOK iff minimal Q_w ⊇ S_w with h(z_Q) = 0 can be chosen
    with |S_a ∩ Q_b| <= 1 or |S_b ∩ Q_a| <= 1 for all pairs of hard N-sets."""
    c = as_circuit(c)
    n, hw, nw = c.n, c.h_wire, c.not_wire
    S = [set(x) for x in c.sets]
    h = lambda Q: c.value(hw, z_of(n, Q))
    if c.value(hw, 0) == 1:
        return 'h0=1', None
    hardN = [i for i, R in enumerate(S) if nw in c.cone(c.outs[i]) and h(R) == 1]
    if len(hardN) < 2:
        return 'le1', len(hardN)
    choices = []
    for i in hardN:
        rest = [v for v in range(n) if v not in S[i]]
        mins = []
        for r in range(len(rest) + 1):
            for ex in combinations(rest, r):
                Q = S[i] | set(ex)
                if h(Q) == 0 and not any(m <= Q for m in mins):
                    mins.append(Q)
        choices.append(mins)
    for combo in product(*choices):
        if all(len(S[a] & combo[jb]) <= 1 or len(S[b] & combo[ja]) <= 1
               for ja, a in enumerate(hardN) for jb, b in enumerate(hardN) if ja < jb):
            return 'pairOK', len(hardN)
    return 'BAD', len(hardN)


def good_Qs(c, permissive=False):
    """Minimal Good zero sets Q ⊇ S_w, cone-masked (w9/fc/lib.py:44-61 goodQs): [S_w] alone if the NOT is
    outside cone(o_w), or NOT is false at all units, or (permissive) NOT is true at <= 1 unit of S_w;
    otherwise the inclusion-minimal Q with NOT(z_Q) = 1. Lists of frozensets."""
    c = as_circuit(c)
    n, nw = c.n, c.not_wire
    unitN = [c.value(nw, 1 << u) for u in range(n)]
    du = all(x == 0 for x in unitN)
    res = []
    for wi, R in enumerate(c.sets):
        R = set(R)
        if nw not in c.cone(c.outs[wi]) or du or (permissive and sum(unitN[u] for u in R) <= 1):
            res.append([frozenset(R)])
            continue
        rest = [v for v in range(n) if v not in R]
        mins = []
        for r in range(len(rest) + 1):
            for ex in combinations(rest, r):
                Q = frozenset(R | set(ex))
                if any(m <= Q for m in mins):
                    continue
                if c.value(nw, z_of(n, Q)) == 1:
                    mins.append(Q)
        res.append(mins)
    return res


def family(c, permissive=False):
    """Theorem-X family (w9/fc/lib.py:62-76): Good Q_w ⊇ S_w with pairwise |S_a∩Q_b| <= 1 or |S_b∩Q_a| <= 1.
    Returns {w: sorted Q_w} or None."""
    c = as_circuit(c)
    S = [set(s) for s in c.sets]
    m = len(S)
    QQ = good_Qs(c, permissive)
    order = sorted(range(m), key=lambda w: len(QQ[w]))
    ch = {}
    okp = lambda a, b: len(S[a] & ch[b]) <= 1 or len(S[b] & ch[a]) <= 1

    def rec(k):
        if k == m:
            return True
        w = order[k]
        for Q in QQ[w]:
            ch[w] = Q
            if all(okp(w, order[j]) for j in range(k)) and rec(k + 1):
                return True
        ch.pop(w, None)
        return False
    return {w: sorted(ch[w]) for w in ch} if rec(0) else None


def gapg_systems(c, wi):
    """Type A(Q) / type B test systems of set wi with their cone-masked counted sets
    (gapg_check.py:5-36 `systems`): list of (type, Q tuple | None, frozenset counted).
    A(Q): Q Good ('cone_du'), z_Q, unit atoms. B (only if NOT in cone): z_S, p_u = e_u if h(e_u) = 1 else
    z_{S-u}, valid if h(z) = 0 or at most one u has h(p_u) = 0. Both then need GoodT in the cone:
    NOT(z) = 1 or NOT true at <= 1 atom."""
    c = as_circuit(c)
    n, nw, hw = c.n, c.not_wire, c.h_wire
    R = set(c.sets[wi])
    cone = c.cone(c.outs[wi])
    Nin = nw in cone
    out = [('A', Q, z, {u: 1 << u for u in R}) for Q, z in good_zero_sets(c, wi, 'cone_du')]
    if Nin:
        z = z_of(n, R)
        pu = {u: (1 << u) if c.value(hw, 1 << u) == 1 else z_of(n, R - {u}) for u in R}
        if c.value(hw, z) == 0 or sum(1 for u in R if c.value(hw, pu[u]) == 0) <= 1:
            out.append(('B', None, z, pu))
    res = []
    for typ, Q, z, pu in out:
        if Nin and not (c.value(nw, z) == 1 or sum(1 for u in R if c.value(nw, pu[u]) == 1) <= 1):
            continue
        res.append((typ, Q, frozenset(counted(c, R, z, pu, cone))))
    return res


def gapg(c, allow_B=True):
    """A choice of one system per set with pairwise disjoint counted sets, or None
    (gapg, gapg_check.py:37-49; allow_B=False is `choice(c, False)` of scaffold_runs/needsB.py:6-18)."""
    c = as_circuit(c)
    m = len(c.sets)
    opts = [[o for o in gapg_systems(c, wi) if allow_B or o[0] == 'A'] for wi in range(m)]
    if any(not o for o in opts):
        return None
    opts = [sorted({o[2]: o for o in os}.values(), key=lambda o: len(o[2])) for os in opts]

    def rec(i, used):
        if i == m:
            return []
        for o in opts[i]:
            if not (o[2] & used):
                r = rec(i + 1, used | o[2])
                if r is not None:
                    return [o] + r
        return None
    return rec(0, frozenset())


# ---------------------------------------------------------------- merge runs (fable A toolkit)
def system(c, S, z, atoms):
    """(good, wz, B) of w9/fa/lib.py:26-32: good = NOT(z) = 1 or NOT true at <= 1 atom; wz = wire values
    at z; B[i] = frozenset of u in S whose atom makes wire i true, for the wires that are 0 at z.
    z and atoms[u] may be points or 0/1 lists."""
    c = as_circuit(c)
    N = c.not_wire
    wz = c.eval(z)
    at = {u: c.eval(atoms[u]) for u in S}
    good = wz[N] == 1 or sum(at[u][N] for u in S) <= 1
    B = {i: frozenset(u for u in S if at[u][i]) for i in range(c.W) if wz[i] == 0}
    return good, wz, B


def merges(c, S, B):
    """Bottom-up union-find over the gates in order (w9/fa/lib.py:33-49): returns (merge gates, counted
    gates). Raises AssertionError if a gate merges more than two blocks or S does not end connected."""
    c = as_circuit(c)
    par = {u: u for u in S}

    def f(u):
        while par[u] != u:
            u = par[u]
        return u
    M, cnt = [], []
    for i in c.gate_wires:
        if i not in B:
            continue
        b = B[i]
        if len(b) >= 2:
            cnt.append(i)
        r = sorted({f(u) for u in b})
        if len(r) >= 2:
            assert len(r) == 2, (i, r)
            M.append(i)
            par[r[1]] = r[0]
    assert len({f(u) for u in S}) == 1
    return M, cnt


def maxviol(c):
    """max over proper nonempty families F of sets of P(F) - d(F), P(F) = number of gates outside the
    cones of the other outputs (= delete_outputs(F).removed). Returns (value, F) (w9/fb/irr.py:10-18)."""
    c = as_circuit(c)
    m, d, best = len(c.sets), c.demands, None
    for r in range(1, m):
        for F in combinations(range(m), r):
            v = c.delete_outputs(F).removed - sum(d[w] for w in F)
            if best is None or v > best[0]:
                best = (v, F)
    return best
