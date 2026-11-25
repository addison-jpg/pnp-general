"""Bit-sliced truth tables, slack at every cube, mixed slack at every 3^n state.  Serves refuter-951 (tensor backend).

A circuit is the dict of research/one-not/tools/search/core.py: {"n", "sets", "gates": [[op, a, b?]], "outs"}, op in not/and/or/const.
A truth table over the 2^n inputs is W = max(1, 2^n / 64) uint64 words, bit x of the table (word x // 64, bit x % 64) = the value
at the input vector x (bit v of x = x_v), the same order as core.tables (a table here == core.tables' int, little-endian bytes).
One gate = one array operation over all inputs at once.

Semantics copied EXACTLY from research/one-not/tools/search/continuous.py :: slack_table (which core.slack agrees with at R = 0):
  state (Q, R), Q and R disjoint subsets of the n inputs: x_Q = 1, x_R = 0.
  alive sets S' = S - R with |S'| >= 2 and S' meet Q empty;  base(Q, R) = sum over such sets of |S'| - 1.
  gate g (OR gates only, or every gate if any_gate) is a witness at Z when Z is disjoint from R and from S', g(Z) = 0 and g = 1 at
  at least two atoms Z + u, u in S'.  g counts at Q when it is a witness at some Z containing Q.   slack(Q, R) = #gates counted - base.
slack_cubes(c) is R = 0 for every Q (n numbers 2^n).  mixed_slack(c) is every (Q, R): an array [R, Q] of shape 2^n x 2^n, INVALID where
Q meets R (3^n valid cells).  The R axis is a batch axis of the same array program (inputs x_v for v in R are forced to the constant 0)."""
import numpy as np
from backend import get_backend, NumpyBackend

INVALID = np.iinfo(np.int32).min


class Ctx:
    """Constants for a given n and backend."""
    def __init__(self, n, be):
        self.n, self.be = n, be
        self.nb = min(1 << n, 64); self.W = max(1, (1 << n) // 64)
        vm = (1 << self.nb) - 1
        self.VM = be.const(vm)
        low = []                                  # positions (within a word) whose bit u is 0, u < 6
        for u in range(min(n, 6)):
            m = 0
            for j in range(self.nb):
                if not j >> u & 1: m |= 1 << j
            low.append(be.const(m))
        self.low = low
        X = np.zeros((max(n, 1), self.W), np.uint64)
        for i in range(n):
            if i < 6:
                m = 0
                for j in range(self.nb):
                    if j >> i & 1: m |= 1 << j
                X[i, :] = np.uint64(m)
            else:
                w = np.arange(self.W)
                X[i, :] = np.where((w >> (i - 6)) & 1, np.uint64(0xFFFFFFFFFFFFFFFF), np.uint64(0))
        self.X = be.from_numpy(X)

    def shift_down(self, T, u):
        """out[Z] = T[Z + 2^u] for Z with bit u clear, 0 elsewhere (T: [..., W])."""
        be = self.be
        if u < 6: return be.shr(T, 1 << u) & self.low[u]
        s = 1 << (u - 6); sh = T.shape
        T4 = T.reshape(sh[:-1] + (self.W // (2 * s), 2, s))
        return be.stack([T4[..., 1, :], be.zeros_like(T4[..., 1, :])], axis=-2).reshape(sh)


_CTX = {}
def ctx(n, be=None):
    be = be or _BE[0]
    k = (n, be.name)
    if k not in _CTX: _CTX[k] = Ctx(n, be)
    return _CTX[k]


_BE = [None]
def set_backend(name=None): _BE[0] = get_backend(name); return _BE[0]
set_backend(None)


def _eval_wires(c, cx, ins=None):
    """Wire tables.  ins: optional list (one per input) of arrays [B, W] replacing the plain input tables (restrictions, cofactors).
    Returns a list of arrays [W] (ins None) or [B, W]."""
    n = c['n']; VM = cx.VM
    w = [cx.X[i] for i in range(n)] if ins is None else list(ins)
    one = cx.be.zeros_like(w[0]) | VM
    for g in c['gates']:
        op = g[0]
        if op == 'not': w.append(~w[g[1]] & VM)
        elif op == 'and': w.append(w[g[1]] & w[g[2]])
        elif op == 'or': w.append(w[g[1]] | w[g[2]])
        elif op == 'const': w.append(one if g[1] else one & ~one)
        else: raise ValueError(g)
    return w


def tables(c, be=None):
    """All wire tables, numpy uint64 array [n + #gates, W]."""
    cx = ctx(c['n'], be); w = _eval_wires(c, cx)
    return np.stack([cx.be.to_numpy(x) for x in w])


def to_int(row):
    """One table row as a Python int in core.tables' format."""
    return int.from_bytes(np.ascontiguousarray(row, dtype='<u8').tobytes(), 'little')


def correct(c, be=None):
    """Every output wire equals the OR of its set (the same test as core.correct)."""
    cx = ctx(c['n'], be); w = _eval_wires(c, cx); be = cx.be
    for S, o in zip(c['sets'], c['outs']):
        t = be.zeros_like(w[0])
        for u in S: t = t | w[u]
        if bool(be.to_numpy(t ^ w[o]).any()): return False
    return True


def _unpack(cx, planes):
    """planes: list of [B, W] bit planes (weight 2^k) -> int32 array [B, 2^n]."""
    tot = None
    for k, p in enumerate(planes):
        a = cx.be.to_numpy(p); B = a.shape[0]
        bits = np.unpackbits(np.ascontiguousarray(a).view(np.uint8).reshape(B, -1), axis=1, bitorder='little')[:, :1 << cx.n]
        v = bits.astype(np.int32) << k
        tot = v if tot is None else tot + v
    return tot


def _add_plane(planes, b, k=0):
    """Vertical (carry-save) counter: add the bit plane b with weight 2^k to the counter planes (fixed width, least significant first)."""
    carry = b
    for i in range(k, len(planes)):
        planes[i], carry = planes[i] ^ carry, planes[i] & carry


def _free(n, Rs):
    """fr[b, i] = the i-th point outside R_b (ascending), int array [B, n - |R|]."""
    Rs = np.asarray(Rs, np.int64); m = n - bin(int(Rs[0])).count('1')
    pts = np.arange(n); fm = ((Rs[:, None] >> pts[None, :]) & 1) == 0
    return np.nonzero(fm)[1].reshape(len(Rs), m), fm


def _planes(c, Rs, any_gate, cx):
    """Packed (count planes, base planes) for the states (Q, R), R in Rs (all with the same number of points |R| = n - cx.n).
    The state space of R is the subcube x_R = 0 with m = n - |R| free points: bit i of the compact index = free point fr[i], the
    layout of continuous.slack_table.  The tables of all R in the batch have the same shape, so one array op serves the batch.
    Nothing is unpacked here."""
    n, be, VM, m = c['n'], cx.be, cx.VM, cx.n; B = len(Rs); Rs = np.asarray(Rs, np.int64)
    fr, fm = _free(n, Rs)
    posn = np.full((B, n), m, np.int64)                              # compact position of each input, m = absent (zero table)
    posn[np.nonzero(fm)[0], np.nonzero(fm)[1]] = np.tile(np.arange(m), B)
    Xx = np.concatenate([be.to_numpy(cx.X)[:m], np.zeros((1, cx.W), np.uint64)])
    Xb = Xx[posn]                                                    # [B, n, W]
    ins = [be.from_numpy(Xb[:, i, :]) for i in range(n)]
    w = _eval_wires(c, cx, ins)
    ALL1 = np.uint64(0xFFFFFFFFFFFFFFFF)
    Fm = [be.from_numpy(np.where(fm[:, i], ALL1, np.uint64(0)).reshape(B, 1)) for i in range(n)]   # input i free in R_b
    gi = [k for k, g in enumerate(c['gates']) if any_gate or g[0] == 'or']
    G = len(gi); z0 = be.zeros_like(w[0]) | VM; z0 = z0 ^ z0
    bplanes = [z0] * sum(max(len(S) - 1, 0) for S in c['sets']).bit_length()
    if G: T = be.stack([w[n + k] for k in gi], axis=1)               # [B, G, W]
    cache = {}
    def cof(u):
        """T[Z + point u] at every Z with x_u(Z) = 0 (the table of the gates with input u set to 1), zero where u is in R."""
        if u not in cache:
            ins1 = list(ins); ins1[u] = (z0 | VM) & Fm[u]
            w1 = _eval_wires(c, cx, ins1)
            cache[u] = be.stack([w1[n + k] for k in gi], axis=1) & Fm[u][:, None, :]
        return cache[u]
    U = be.zeros_like(T) if G else None
    for S in c['sets']:
        zero = VM | z0; sz = np.zeros(B, np.int64)
        for u in S:
            zero = zero & ~ins[u]                                    # no point of S - R is in Z (x_u = 0 table when u in R: no constraint)
            sz += fm[:, u]
        wt = np.maximum(sz - 1, 0)
        for k in range(int(wt.max()).bit_length()):
            Mk = be.from_numpy(np.where((wt >> k) & 1, ALL1, np.uint64(0)).reshape(B, 1))
            _add_plane(bplanes, zero & Mk, k)
        if G:
            one = be.zeros_like(T); two = be.zeros_like(T)
            for u in S:
                t = cof(u); two = two | (one & t); one = one | t
            U = U | (zero[:, None, :] & ~T & two)
    cplanes = [z0] * G.bit_length()
    if G:
        for u in range(m): U = U | cx.shift_down(U, u)               # witness at some Z containing Q
        for g in range(G): _add_plane(cplanes, U[:, g, :])
    return cplanes, bplanes


def _groups(c, budget):
    """(cx, Rs) batches covering every R subset of the n points, grouped by |R| (equal shapes), each batch within the memory budget."""
    n = c['n']; G = len(c['gates']); pc = np.array([bin(r).count('1') for r in range(1 << n)])
    for k in range(n + 1):
        m = n - k; cx = ctx(m); W = cx.W; Rk = np.nonzero(pc == k)[0]
        per = 8 * W * (n + G * (min(len(c['sets']) * 0 + n, 8) + 8) + 8) + (1 << m) * 4 * 4
        b = max(1, int(budget // per))
        for i in range(0, len(Rk), b): yield cx, Rk[i:i + b]


def _slack_compact(c, Rs, any_gate, cx):
    cp, bp = _planes(c, Rs, any_gate, cx); B = len(Rs); z = np.zeros((B, 1 << cx.n), np.int32)
    return (_unpack(cx, cp) if cp else z), (_unpack(cx, bp) if bp else z)


def slack_cubes(c, any_gate=False, parts=False, be=None):
    """slack(Q) for every cube Q (R = 0), int32 [2^n].  parts=True returns (count, base)."""
    cx = ctx(c['n'], be); cnt, base = _slack_compact(c, [0], any_gate, cx)
    return (cnt[0], base[0]) if parts else cnt[0] - base[0]


def mixed_slack(c, any_gate=False, parts=False, be=None, budget=2 << 30, rs=None, compact=False):
    """slack(Q, R) at every mixed state.  Default: int32 [len(rs) or 2^n, 2^n] indexed [R, Q], INVALID where Q meets R.
    compact=True: a list, one array per R (in rs order) over the 2^(n - |R|) cubes of the subcube x_R = 0, indexed by the sub-vector of Q
    on the free points, exactly continuous.slack_table(c, R).  parts=True: (count, base) instead of count - base."""
    n = c['n']; rs = list(range(1 << n)) if rs is None else [int(r) for r in rs]; where = {r: i for i, r in enumerate(rs)}
    sel = np.array(sorted(rs)); res = [None] * len(rs)
    pcs = {}
    for r in rs: pcs.setdefault(bin(r).count('1'), []).append(r)
    for k, lst in pcs.items():
        cx = ctx(n - k, be); G = len(c['gates']); per = 8 * cx.W * (n + G * 16 + 8) + (1 << cx.n) * 16; b = max(1, int(budget // per))
        for i in range(0, len(lst), b):
            ch = lst[i:i + b]; cnt, base = _slack_compact(c, ch, any_gate, cx)
            for j, r in enumerate(ch): res[where[r]] = (cnt[j], base[j]) if parts else cnt[j] - base[j]
    if compact: return res
    N = 1 << n; sh = (len(rs), N)
    out = (np.full(sh, INVALID, np.int32), np.full(sh, INVALID, np.int32)) if parts else np.full(sh, INVALID, np.int32)
    for i, r in enumerate(rs):
        _, idx = _spread(n, r)
        if parts: out[0][i][idx] = res[i][0]; out[1][i][idx] = res[i][1]
        else: out[i][idx] = res[i]
    return out


def _spread(n, R):
    fr = [v for v in range(n) if not R >> v & 1]; j = np.arange(1 << len(fr), dtype=np.int64); idx = np.zeros(1 << len(fr), np.int64)
    for i, v in enumerate(fr): idx |= ((j >> i) & 1) << v
    return fr, idx


def _popcount(x): return int(np.bitwise_count(x).sum())


def mixed_stats(c, any_gate=False, be=None, budget=2 << 30):
    """Reductions over all 3^n states, computed on the packed planes (bit-sliced subtract and compare, popcount; nothing unpacked):
    states, states with base > 0, least slack, number of states with slack < 0, histogram of slack."""
    n = c['n']; st = pos = neg = 0; hist = {}
    for cx, Rs in _groups(c, budget):
        be_ = cx.be
        cp, bp = _planes(c, Rs, any_gate, cx)
        Vp = (be_.zeros_like(cx.X[:1].reshape(1, -1)) | cx.VM)       # [1, W]: the real bits of a word
        L = max(len(cp), len(bp)) + 1
        zz = be_.zeros_like(Vp)
        cp = cp + [zz] * (L - len(cp)); bp = bp + [zz] * (L - len(bp))
        D = []; carry = ~zz
        for k in range(L):
            nb = ~bp[k]; D.append(cp[k] ^ nb ^ carry); carry = (cp[k] & nb) | (carry & (cp[k] ^ nb))
        B = len(Rs); st += B * (1 << cx.n)
        bany = zz
        for p in bp: bany = bany | p
        pos += _popcount(be_.to_numpy(bany & Vp)); neg += _popcount(be_.to_numpy(D[L - 1] & Vp))
        mx = (1 << (L - 1)) - 1
        for v in range(-mx, mx + 1):
            eq = Vp
            for k in range(L): eq = eq & (D[k] if (v >> k) & 1 else ~D[k])
            cntv = _popcount(be_.to_numpy(eq))
            if cntv: hist[v] = hist.get(v, 0) + cntv
    return dict(states=st, base_pos=pos, min_slack=min(min(hist), 0), neg=neg, hist=dict(sorted(hist.items())))


def dd_states(c):
    """DD states of a one-NOT circuit, A7/A14 definition, over EVERY (Q, D) with Q, D disjoint (3^n states).
    A set w is DD at (Q, D): S_w meet Q empty, |S_w - D| >= 2, h(Z_w) = 1, h(Q + t) = 0 for some t in S_w - D, h = the NOT gate's input,
    Z_w = 1 off S_w u D.  Returns a bool array [D, Q] (False where Q meets D): some w is DD there; and the count of (state, w) pairs."""
    n = c['n']; N = 1 << n
    ps = [k for k, g in enumerate(c['gates']) if g[0] == 'not']
    assert len(ps) == 1, 'one NOT gate expected'
    cx = ctx(n); w = _eval_wires(c, cx)
    a = _unpack(cx, [w[c['gates'][ps[0]][1]][None, :]])[0].astype(bool)
    idx = np.arange(N, dtype=np.int64); pc = np.zeros(N, np.int64)
    for v in range(n): pc += (idx >> v) & 1
    ALL = N - 1; anyd = np.zeros((N, N), bool); pairs = 0
    for S in c['sets']:
        sm = sum(1 << u for u in S); Qa = idx[None, :]; Da = idx[:, None]
        ok = ((Qa & Da) == 0) & ((Qa & sm) == 0) & (pc[sm & ~Da] >= 2)
        zw = ALL & ~(sm | Da)
        some = np.zeros((N, N), bool)
        for t in S: some |= ((Da >> t) & 1 == 0) & ~a[Qa | (1 << t)]
        dd = ok & a[zw + 0 * Qa] & some
        anyd |= dd; pairs += int(dd.sum())
    return anyd, pairs
