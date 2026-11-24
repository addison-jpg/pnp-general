"""Lifted price inequality (opus-global-price.md): LP test of
    for every price pi >= 0 on the lifted gates:  sum_w min_{t valid} pi(cls_w(t)) <= pi(U)
which by LP duality is the fractional LiftSDR: distributions lambda_w over valid lifted classes of w with
every gate's load sum_w sum_t lambda_w(t) [g in cls_w(t)] <= 1.  We compute
    t* = min over lambda of the maximal gate load;   price inequality (for the menu used) <=> t* <= 1.
Menus are SUB-families of Lean's liftMenu (PureGP.LTSValid + runMT), so t* <= 1 is a valid certificate
for the official (full lifted) family; t* > 1 refutes only the sub-family statement.
  real : real merge sets M_z(w): zeta = (z, nu z), atoms (z + e_u, nu(z + e_u)), z vanishing on S_w
  world: zeta = (z, b), atoms (z + e_u, b), b in {0, 1} (valid iff C_b(o_w)(z) = 0, C_b(o_w)(z + e_u) = 1)
  ext  : zeta = (z, b), atoms B + {u} + P_u, B in {0, ones(zeta)}, P_u = extra zero coordinates (y first, then
         x outside S_w) assigned to at most one atom; up to KMAX extra coordinates (scaffold's family)
Also the k-gate 0/1 test (k = 2, 3): max over gate sets K of sum_w min_t |cls_w(t) & K| - |K|.
Usage: python3 -I global_price.py ROOT_OR_FILES... [--nmax 9] [--menus real,world,ext] [--kmax 3] [--kgate 2]
"""
import sys, json, glob, itertools, collections, os

def load(paths):
    seen = set()
    files = []
    for p in paths:
        if os.path.isdir(p):
            files += sorted(glob.glob(p + '/**/*.json', recursive=True)) + sorted(glob.glob(p + '/**/*.jsonl', recursive=True))
        else:
            files.append(p)
    for f in files:
        if '/lean/' in f:
            continue
        try:
            if f.endswith('.jsonl'):
                items = [json.loads(l) for l in open(f) if l.strip()]
            else:
                d = json.load(open(f)); items = d if isinstance(d, list) else [d]
        except Exception:
            continue
        for i, c in enumerate(items):
            if not (isinstance(c, dict) and all(k in c for k in ('n', 'sets', 'gates', 'outs'))):
                continue
            try:
                G = [[g[0]] + [int(x) for x in g[1:]] for g in c['gates']]
                key = json.dumps([c['n'], c['sets'], G, c['outs']])
            except Exception:
                continue
            if key in seen:
                continue
            seen.add(key)
            yield '%s:%d' % (f, i), c['n'], [sorted(set(s)) for s in c['sets']], G, list(c['outs'])


class Lift:
    """Lifted circuit on points x | y << n.  Wire n + p (the NOT) becomes the input y; it is not a gate."""
    def __init__(self, n, G, outs):
        self.n, self.G, self.outs = n, G, outs
        nots = [k for k, g in enumerate(G) if g[0] == 'not']
        self.p = nots[0]
        N = n + 1; P = 1 << N; FULL = (1 << P) - 1
        W = []
        for v in range(n):
            W.append(sum(1 << x for x in range(P) if (x >> v) & 1))
        ytab = sum(1 << x for x in range(P) if (x >> n) & 1)
        for k, g in enumerate(G):
            if g[0] == 'not': W.append(ytab)
            elif g[0] == 'and': W.append(W[g[1]] & W[g[2]])
            elif g[0] == 'or': W.append(W[g[1]] | W[g[2]])
            else: raise ValueError(g[0])
        self.W = W
        self.gw = [n + k for k in range(len(G)) if k != self.p]  # lifted gate wires
        # V[P] = bitmask over gate wires (bit index = position in self.gw)
        self.V = [0] * P
        for j, i in enumerate(self.gw):
            t = W[i]
            for x in range(P):
                if (t >> x) & 1:
                    self.V[x] |= 1 << j
        hin = G[self.p][1]
        self.h = [(W[hin] >> x) & 1 for x in range(1 << n)]   # h at real x (wire before the NOT: y-free)
        self.nu = [1 - b for b in self.h]

    def val(self, wire, pt):
        return (self.W[wire] >> pt) & 1

    def real_ok(self, S):
        n = self.n
        for x in range(1 << n):
            pt = x | (self.nu[x] << n)
            for o, R in zip(self.outs, S):
                if self.val(o, pt) != (1 if any((x >> u) & 1 for u in R) else 0):
                    return False
        return True

    def run(self, R, zeta, atoms):
        """Lean runMT in the lift: gate wire merges iff 0 at zeta and its trace meets >= 2 current labels."""
        zm = self.V[zeta]; A = [self.V[a] for a in atoms]
        lab = list(range(len(R)))
        M = 0
        cand = 0
        for i in range(len(A)):
            for j in range(i + 1, len(A)):
                cand |= A[i] & A[j]
        cand &= ~zm
        j = 0
        while cand:
            if cand & 1:
                tr = {lab[u] for u in range(len(R)) if (A[u] >> j) & 1}
                if len(tr) >= 2:
                    M |= 1 << j
                    r = min(tr)
                    lab = [r if l in tr else l for l in lab]
            cand >>= 1; j += 1
        return M

    def valid(self, R, o, zeta, atoms):
        if self.val(o, zeta): return False
        if not all(self.val(o, a) for a in atoms): return False
        seen = 0
        for a in atoms:
            ex = a & ~zeta
            if ex & seen: return False
            seen |= ex
        return True

    def menu(self, R, o, kinds, KMAX=3):
        n = self.n; Y = 1 << n; Rm = sum(1 << u for u in R)
        cls = set()
        for z in range(1 << n):
            if z & Rm: continue
            if 'real' in kinds:
                zeta = z | (self.nu[z] << n)
                atoms = [(z | 1 << u) | (self.nu[z | 1 << u] << n) for u in R]
                if self.valid(R, o, zeta, atoms):
                    cls.add(self.run(R, zeta, atoms))
            if 'world' in kinds:
                for b in (0, 1):
                    zeta = z | (b << n)
                    atoms = [(z | 1 << u) | (b << n) for u in R]
                    if self.valid(R, o, zeta, atoms):
                        cls.add(self.run(R, zeta, atoms))
        if 'ext' in kinds:
            for zeta in range(1 << (n + 1)):
                if self.val(o, zeta): continue
                zeros = ([n] if not (zeta >> n) & 1 else []) + [v for v in range(n) if not (zeta >> v) & 1 and v not in R]
                zeros = zeros[:KMAX]
                for Bfull in (False, True):
                    base = zeta if Bfull else 0
                    for assign in itertools.product(range(len(R) + 1), repeat=len(zeros)):
                        atoms = []
                        for iu, u in enumerate(R):
                            a = base | (1 << u)
                            for e, k in zip(zeros, assign):
                                if k == iu + 1: a |= 1 << e
                            atoms.append(a)
                        if self.valid(R, o, zeta, atoms):
                            cls.add(self.run(R, zeta, atoms))
        return cls


def lp_load(menus, ngates):
    """t* = min max load over fractional choices; returns (t*, price pi from the dual) using HiGHS."""
    from scipy.optimize import linprog
    import numpy as np
    cols = [(w, c) for w, M in enumerate(menus) for c in sorted(M)]
    nv = len(cols) + 1
    U = 0
    for M in menus:
        for c in M: U |= c
    gl = [j for j in range(ngates) if (U >> j) & 1]
    A = np.zeros((len(gl), nv));
    for k, (w, c) in enumerate(cols):
        for r, j in enumerate(gl):
            if (c >> j) & 1: A[r, k] = 1
    A[:, -1] = -1
    Aeq = np.zeros((len(menus), nv))
    for k, (w, c) in enumerate(cols): Aeq[w, k] = 1
    cost = np.zeros(nv); cost[-1] = 1
    res = linprog(cost, A_ub=A, b_ub=np.zeros(len(gl)), A_eq=Aeq, b_eq=np.ones(len(menus)),
                  bounds=[(0, None)] * nv, method='highs')
    pi = {gl[r]: -res.ineqlin.marginals[r] for r in range(len(gl))}
    return res.fun, pi


def kgate(menus, ngates, k):
    """max over K (|K| = k, K within U) of sum_w min_c |c & K| - k, with the argmax."""
    import numpy as np
    U = 0
    for M in menus:
        for c in M: U |= c
    gl = [j for j in range(ngates) if (U >> j) & 1]
    if len(gl) < k: return None
    mats = [np.array([[(c >> j) & 1 for j in gl] for c in sorted(M)], dtype=np.int8) for M in menus]
    best = (-10 ** 9, None)
    if k == 2:
        tot = np.zeros((len(gl), len(gl)), dtype=np.int32)
        for Mw in mats:
            tot += (Mw[:, :, None] + Mw[:, None, :]).min(axis=0)
        for a in range(len(gl)):
            for b in range(a + 1, len(gl)):
                if tot[a, b] - 2 > best[0]: best = (int(tot[a, b]) - 2, (gl[a], gl[b]))
    elif k == 3:
        L = len(gl)
        tot = np.zeros((L, L, L), dtype=np.int32)
        for Mw in mats:
            tot += (Mw[:, :, None, None] + Mw[:, None, :, None] + Mw[:, None, None, :]).min(axis=0)
        for a, b, c in itertools.combinations(range(L), 3):
            if tot[a, b, c] - 3 > best[0]: best = (int(tot[a, b, c]) - 3, (gl[a], gl[b], gl[c]))
    return best


def main():
    args = sys.argv[1:]
    def opt(name, default):
        if name in args:
            i = args.index(name); v = args[i + 1]; del args[i:i + 2]; return v
        return default
    NMAX = int(opt('--nmax', 9)); kinds = opt('--menus', 'real,world').split(','); KMAX = int(opt('--kmax', 3))
    KG = int(opt('--kgate', 0)); verbose = '--v' in args
    args = [a for a in args if a != '--v']
    st = collections.Counter(); worst = []
    for name, n, S, G, outs in load(args):
        if n > NMAX or sum(1 for g in G if g[0] == 'not') != 1 or any(len(R) < 2 for R in S):
            st['skipped'] += 1; continue
        if any(len(set(a) & set(b)) > 1 for a, b in itertools.combinations(S, 2)):
            st['skipped'] += 1; continue
        try:
            L = Lift(n, G, outs)
        except Exception:
            st['skipped'] += 1; continue
        if not L.real_ok(S):
            st['incorrect'] += 1; continue
        st['circuits'] += 1
        menus = [L.menu(R, o, kinds, KMAX) for R, o in zip(S, outs)]
        ng = len(L.gw)
        base = sum(len(R) - 1 for R in S)
        U = 0
        for M in menus:
            for c in M: U |= c
        t, pi = lp_load(menus, ng)
        rec = {'name': name, 'n': n, 's': len(G), 'base': base, 'U': bin(U).count('1'), 'tstar': round(t, 6)}
        if KG:
            r = kgate(menus, ng, KG)
            if r is not None:
                rec['kgate_excess'] = r[0]
                rec['kgate_K'] = [L.gw[j] for j in r[1]] if r[1] else None
                st['kgate_viol'] += r[0] > 0
        if t > 1 + 1e-7:
            st['tstar>1'] += 1
            rec['price'] = {str(L.gw[j]): round(v, 4) for j, v in pi.items() if v > 1e-9}
            print('VIOLATION', json.dumps(rec), flush=True)
        elif verbose:
            print(json.dumps(rec), flush=True)
        worst.append((t, name))
    worst.sort(reverse=True)
    print('STATS', dict(st), 'menus', kinds)
    print('max t*', worst[:5])

if __name__ == '__main__':
    main()
