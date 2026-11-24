"""Rules: private / sandwich classes, the relative-sandwich rule, the X-rule, the coin rule.

`relmenu` / `rel_rule` have the semantics of tractability work/duals/relrule.py.
Functions take a `Circuit` or the JSON dict; gate sets are sets/sorted lists of wire ids.
"""
from itertools import combinations

from .circuit import as_circuit, z_of
from . import lp as _lp
from . import systems as _sys
from .matching import max_matched, simple_bmatch

__all__ = ['private', 'sandwich_classes', 'roles', 'relmenu', 'rel_rule', 'relmenus_minimal', 'rel_classes',
           'xrule', 'residual', 'mix', 'two_world', 'union_hall', 'hall']


def private(c):
    """(Dc, Pc), one set of gates per target set (private, tractability work/duals/resid.py:13-21):
    Dc[i] = gates g <= OR(S_i) pointwise that are true at >= 2 units of S_i        (dedicated, below)
    Pc[i] = gates g >= OR(S_i), g not constant 1, g not >= OR(S_j) for any j != i  (private above)."""
    c = as_circuit(c)
    t, full = c.tables(), c.full
    OR = [c.or_table(S) for S in c.sets]
    Dc, Pc = [], []
    for i, S in enumerate(c.sets):
        Dc.append({g for g in c.gate_wires if t[g] & ~OR[i] == 0 and sum(t[g] >> (1 << u) & 1 for u in S) >= 2})
        Pc.append({g for g in c.gate_wires if OR[i] & ~t[g] == 0 and t[g] != full
                   and not any(OR[j] & ~t[g] == 0 for j in range(len(OR)) if j != i)})
    return Dc, Pc


def sandwich_classes(c):
    """Per set (L, U) (classes, w9/fa/sand.py:19-29): L = gates <= o_w true at >= 2 units of S_w;
    U = gates >= o_w with g(z_{S_w}) = 0. Uses OR(S_w) for o_w (the script asserts they agree)."""
    c = as_circuit(c)
    t, res = c.tables(), []
    for S in c.sets:
        f, zS = c.or_table(S), z_of(c.n, S)
        L = {i for i in c.gate_wires if t[i] & ~f == 0 and sum(t[i] >> (1 << u) & 1 for u in S) >= 2}
        U = {i for i in c.gate_wires if f & ~t[i] == 0 and not t[i] >> zS & 1}
        res.append((L, U))
    return res


def roles(c):
    """Per gate wire a dict(op, ins, tags, cones, z0, units) (roles, tractability work/duals/dualp.py:103-127).
    tags: 'NOT', 'h', 'OUTw', and 'aboveN' (downstream of the NOT) / 'belowh' (in the cone of h) / 'side'."""
    c = as_circuit(c)
    n, nw, h = c.n, c.not_wire, c.h_wire
    down = c.downstream()
    hc = c.cone(h) | {h}
    oc = c.cones()
    z0 = c.eval(0)
    unit = [c.eval(1 << u) for u in range(n)]
    R = {}
    for k, g in enumerate(c.gates):
        i, t = n + k, []
        if i == nw:
            t.append('NOT')
        if i == h:
            t.append('h')
        if i in c.outs:
            t += ['OUT%d' % w for w, o in enumerate(c.outs) if o == i]
        t.append('aboveN' if i in down and i != nw else ('belowh' if i in hc and i != h else ('' if i in (nw, h) else 'side')))
        R[i] = dict(op=g[0], ins=list(g[1:]), tags=[x for x in t if x], cones=[w for w in range(len(oc)) if i in oc[w]],
                    z0=z0[i], units=[u for u in range(n) if unit[u][i] != z0[i]])
    return R


def relmenu(c, WT=2, above=False):
    """Relative-sandwich menu (relmenu, tractability work/duals/relrule.py:8-34).

    For set w and every zero point z of weight <= WT with z = 0 on S_w, the item
        I_z(w) = { g counted by Σ(z) (g(z) = 0, g(z+e_u) = 1 for >= 2 u in S_w) such that
                   g <= OR(S_w) on the upper cube {x >= z}        (relative dedicated)
                   or g in P_w = private-above class `private(c)[1][w]`
                   or (above=True) g >= OR(S_w) on the cube }.
    Returns per set the inclusion-maximal items as [(sorted gates, z as a tuple of its one-positions)],
    in the order of the script (the witness z is the LAST zero point giving that item)."""
    c = as_circuit(c)
    n, t = c.n, c.tables()
    _, Pc = private(c)
    M = []
    for i, S in enumerate(c.sets):
        OR = c.or_table(S)
        rest = [v for v in range(n) if v not in S]
        items = {}
        for k in range(WT + 1):
            for zs in combinations(rest, k):
                zr = sum(1 << v for v in zs)
                cube = c.cube_table(zr)
                I = set()
                for g in _sys.cnt_z(c, S, zr):
                    if (t[g] & cube) & ~OR == 0 or g in Pc[i] or (above and (OR & cube) & ~t[g] == 0):
                        I.add(g)
                items[frozenset(I)] = zs
        mx = [x for x in items if not any(x < y for y in items)]
        M.append([(sorted(x), items[x]) for x in mx])
    return M


def rel_rule(c, WT=2, above=False):
    """(L_rel, pi, F): the LP value of the relative-sandwich rule, flat optimal prices and the menu
    F = relmenu(c, WT, above). L_rel <= 1 iff the rule gives FracMatch; (inf, {}, F) if some set has
    only items shorter than its demand. Legacy: run (tractability work/duals/relrule.py:35-47)."""
    c = as_circuit(c)
    F = relmenu(c, WT, above)
    dem = c.demands
    M = [[C for C, z in m] for m in F]
    if any(all(len(C) < d for C in m) for m, d in zip(M, dem)):
        return float('inf'), {}, F
    L, pi, mu, D = _lp.lpdual(M, dem)
    return L, pi, F


def relmenus_minimal(c):
    """Front's earlier reading of the rule (relmenus, w9/fc/relrule.py:8-28): z = 0 or a minimal 1-point m
    of h with |m| <= 2, m ∩ S_w = ∅; item C_{w,z} = I_z(w) ∪ (P_w ∩ cnt_z(w)), P_w = L_w ∪ U_w the
    sandwich classes. Returns (M, info): M[w] = {frozenset item: (z tuple, None)},
    info[w] = (sorted P_w, {ones of z: sorted item})."""
    c = as_circuit(c)
    n, t, hw = c.n, c.tables(), c.h_wire
    ones = [x for x in range(1 << n) if t[hw] >> x & 1]
    # the script scans points in itertools.product order (x_0 most significant)
    ones.sort(key=lambda x: tuple(x >> i & 1 for i in range(n)))
    mins = [x for x in ones if bin(x).count('1') <= 2 and not any(y != x and y & ~x == 0 for y in ones)]
    cls = sandwich_classes(c)
    M, info = [], []
    for w, R in enumerate(c.sets):
        Sm = sum(1 << u for u in R)
        P = cls[w][0] | cls[w][1]
        OR = c.or_table(R)
        menu = {}
        for z in [0] + [m for m in mins if not m & Sm]:
            cnt = set(_sys.cnt_z(c, R, z))
            cube = c.cube_table(z)
            I = {g for g in cnt if (t[g] & cube) & ~OR == 0}
            menu[frozenset(I | (P & cnt))] = (tuple(z >> v & 1 for v in range(n)), None)
        M.append(menu)
        info.append((sorted(P), {tuple(v for v in range(n) if z[v]): sorted(Cz) for Cz, (z, _) in menu.items()}))
    return M, info


def rel_classes(c, maxw=2):
    """{(w, z): (low, up)} of analyse (w9/fe/rel.py:8-29): z = 0 or a minimal 1-point of h of weight
    <= maxw missing S_w; low = gates of cnt_z(w) that are <= OR(S_w) on {x >= z}; up = cnt_z(w) ∩ P_w,
    P_w = gates (NOT included) >= OR(S_w), not constant 1, not >= OR(S_j) for j != w."""
    c = as_circuit(c)
    n, t, H = c.n, c.tables(), c.h_wire
    _, Pc = private(c)
    minh = [x for x in range(1 << n) if t[H] >> x & 1 and bin(x).count('1') <= maxw
            and not any(t[H] >> (x & ~(1 << i)) & 1 for i in range(n) if x >> i & 1)]
    cls = {}
    for w, Sw in enumerate(c.sets):
        m = sum(1 << u for u in Sw)
        OR = c.or_table(Sw)
        for z in [0] + [x for x in minh if x & m == 0]:
            cnt = _sys.cnt_z(c, Sw, z)
            cube = c.cube_table(z)
            cls[(w, z)] = ({g for g in cnt if (t[g] & cube) & ~OR == 0}, {g for g in cnt if g in Pc[w]})
    return cls


def xrule(c, F=None):
    """X-rule (xrule, tractability work/duals/xrule.py:6-20): X_w = Pi_w ∪ E_w with Pi_w = D_w ∪ P_w
    (`private`) and E_w = gates downstream of the NOT lying in the cone of o_w only. Per set a dict
    (w, d, pi, x, xx, hz, z, used, PiE); the rule holds for w iff x >= d."""
    c = as_circuit(c)
    R = roles(c)
    dem = c.demands
    Dc, Pc = private(c)
    F = F or _sys.menu_witnesses(c)
    out = []
    allPi = set().union(*Dc, *Pc)
    for w, m in enumerate(F):
        Pi = Dc[w] | Pc[w]
        E = {g for g in R if 'aboveN' in R[g]['tags'] and R[g]['cones'] == [w]} - allPi
        Ex = {g for g in R if R[g]['cones'] == [w]} - allPi
        best = max(m, key=lambda it: (len(set(it[0]) & (Pi | E)), len(set(it[0]) & (Pi | Ex))))
        C = set(best[0])
        out.append(dict(w=w, d=dem[w], pi=max(len(set(it[0]) & Pi) for it in m), x=len(C & (Pi | E)),
                        xx=max(len(set(it[0]) & (Pi | Ex)) for it in m), hz=best[2],
                        z=[i for i, b in enumerate(best[1]) if b], used=sorted(C & (Pi | E)),
                        PiE=(sorted(Pi), sorted(E))))
    return out


def residual(c):
    """Residual ("private classes reserved") analysis (run, tractability work/duals/resid.py:36-61):
    dict(L, pi, m, short, dem, Lres, pires). L, pi: the full-menu LP value and flat prices;
    m[w] = max over menu items of |Pi_w ∩ C| with Pi_w = D_w ∪ P_w; short = sets with m[w] < d_w;
    Lres, pires: the LP where each item keeps its non-private gates and min(d_w, |Pi_w ∩ C|) free slots."""
    c = as_circuit(c)
    F = _sys.menu_witnesses(c)
    dem = c.demands
    Dc, Pc = private(c)
    Pi = [Dc[i] | Pc[i] for i in range(len(dem))]
    allP = set().union(*Pi)
    M = [[C for C, z, hz in m] for m in F]
    L, pi, mu, _ = _lp.lpdual(M, dem)
    m_i = [max(len(Pi[i] & set(C)) for C in M[i]) for i in range(len(dem))]
    short = [i for i in range(len(dem)) if m_i[i] < dem[i]]
    Mr = [[[g for g in C if g not in allP] + [('priv', i, t) for t in range(min(dem[i], len(Pi[i] & set(C))))]
           for C in m] for i, m in enumerate(M)]
    Lr, pir = _lp.resid_lp(Mr, dem)
    return dict(L=L, pi=pi, m=m_i, short=short, dem=dem, Lres=Lr, pires=pir)


def mix(c, a=0.5):
    """Coin rule: canonical counted set with weight a, R* with weight 1 - a; returns the min max load
    (mix, w9/mixrule.py:42-45). The rule works iff the value is <= 1."""
    c = as_circuit(c)
    dem = c.demands
    Dc, Dr = _sys.worlds(c)
    return _lp.fixed_load([[x, y] for x, y in zip(Dc, Dr)], [[a, 1 - a]] * len(dem), dem)


def hall(Ds, dem):
    """Number of matched slots when set w needs dem[w] distinct gates of Ds[w], each gate used once
    (the integer of the `bmatch(Ds, demand)` copies: hallcheck.py:24, allsys.py:49, rstar.py:19)."""
    return max_matched(Ds, dem)


def two_world(c, Dc=None, Dr=None):
    """(ok, matched, 2*base): both worlds (canonical and R*) matched at once into gates of capacity 2,
    each system using a gate at most once: twoworld (w9/tw/tw.py:48-63, its own capacity-2 `bmatch`),
    computed by max-flow (matching.max_matched(..., c=2, simple=True))."""
    c = as_circuit(c)
    if Dc is None:
        Dc, Dr = _sys.worlds(c)
    dem = c.demands
    got = max_matched(list(Dc) + list(Dr), dem + dem, 2, simple=True)
    return got == 2 * sum(dem), got, 2 * sum(dem)


def union_hall(c, Dc, Dr):
    """Hall for the unions Dc[w] ∪ Dr[w] with unit capacities (unionhall, w9/tw/tw.py:64-67)."""
    c = as_circuit(c)
    dem = c.demands
    return simple_bmatch([sorted(set(a) | set(b)) for a, b in zip(Dc, Dr)], dem)[0] is not None
