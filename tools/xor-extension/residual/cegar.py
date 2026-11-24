# Search: residual-shape circuit with r gates on k y-variables + x (last input), output flips with x
# everywhere, sides locally irredundant; CEGAR on f: block f if C(f)<=r-4 or C(not f)<=r-4.
import sys, itertools, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc
from synth import synth

def build(k, r, local=True):
    N = k + 1; R = 1 << N; x = k
    cnt = [0]
    def nv():
        cnt[0] += 1; return cnt[0]
    cl = []
    n = [nv() for _ in range(r)]; a = [nv() for _ in range(r)]
    s1 = [[nv() for w in range(N + i)] for i in range(r)]
    s2 = [[nv() for w in range(N + i)] for i in range(r)]
    v = [[nv() for _ in range(R)] for i in range(r)]
    p = [[nv() for _ in range(R)] for i in range(r)]
    q = [[nv() for _ in range(R)] for i in range(r)]
    def exactly_one(lits):
        cl.append(list(lits))
        for xx, yy in itertools.combinations(lits, 2): cl.append([-xx, -yy])
    for i in range(r):
        W = N + i
        exactly_one(s1[i]); exactly_one(s2[i])
        for w in range(W):
            cl.append([-n[i], -s1[i][w], s2[i][w]])
            for w2 in range(w + 1):
                cl.append([n[i], -s1[i][w], -s2[i][w2]])
            for (s, pin) in ((s1[i], p[i]), (s2[i], q[i])):
                for row in range(R):
                    if w < N:
                        cl.append([-s[w], pin[row] if (row >> w) & 1 else -pin[row]])
                    else:
                        cl.append([-s[w], -pin[row], v[w - N][row]])
                        cl.append([-s[w], pin[row], -v[w - N][row]])
        for row in range(R):
            V, P, Q = v[i][row], p[i][row], q[i][row]
            cl += [[-n[i], V, P], [-n[i], -V, -P]]
            cl += [[n[i], -a[i], -V, P], [n[i], -a[i], -V, Q], [n[i], -a[i], V, -P, -Q]]
            cl += [[n[i], a[i], V, -P], [n[i], a[i], V, -Q], [n[i], a[i], -V, P, Q]]
        if i < r - 1:
            cl.append([s[j][N + i] for j in range(i + 1, r) for s in (s1, s2)])
    # output flips with x
    for row in range(R >> 1):
        cl += [[v[r-1][row], v[r-1][row | (1 << x)]], [-v[r-1][row], -v[r-1][row | (1 << x)]]]
    # shape
    rd = [nv() for _ in range(r)]
    for i in range(r):
        cl += [[-rd[i], s1[i][x], s2[i][x]], [rd[i], -s1[i][x]], [rd[i], -s2[i][x]]]
        cl.append([-rd[i], -n[i]])
    enc = CardEnc.equals(lits=rd, bound=2, top_id=cnt[0]); cnt[0] = max(cnt[0], enc.nv); cl += enc.clauses
    ra = [nv() for _ in range(r)]
    for i in range(r):
        cl += [[-ra[i], rd[i]], [-ra[i], a[i]], [ra[i], -rd[i], -a[i]]]
    enc = CardEnc.equals(lits=ra, bound=1, top_id=cnt[0]); cnt[0] = max(cnt[0], enc.nv); cl += enc.clauses
    use = {}
    for i in range(r - 1):
        users = []
        for j in range(i + 1, r):
            u = nv(); users.append((j, u)); use[(i, j)] = u
            cl += [[-u, s1[j][N + i], s2[j][N + i]], [u, -s1[j][N + i]], [u, -s2[j][N + i]]]
        for (j, u), (j2, u2) in itertools.combinations(users, 2):
            cl.append([-rd[i], -u, -u2])
        for j, u in users:
            cl.append([-rd[i], -u, -n[j]])
            cl.append([-rd[i], -u, -a[i], -a[j]])
            cl.append([-rd[i], -u, a[i], a[j]])
    cl.append([-rd[r - 1]])
    # H gates
    uG = [nv() for _ in range(r)]
    for j in range(r):
        ts = []
        for i in range(j):
            tt_ = nv(); ts.append(tt_)
            cl += [[-tt_, rd[i]], [-tt_, use[(i, j)]], [tt_, -rd[i], -use[(i, j)]]]
        cl.append([-uG[j]] + ts)
        for tt_ in ts: cl.append([uG[j], -tt_])
    red = [[nv() for _ in range(r)] for c in (0, 1)]  # red[0]: G or H1(OR); red[1]: G or H2(AND)
    for j in range(r):
        # red0 = rd or (uG and not a) ; red1 = rd or (uG and a)
        cl += [[-red[0][j], rd[j], uG[j]], [-red[0][j], rd[j], -a[j]], [red[0][j], -rd[j]], [red[0][j], -uG[j], a[j]]]
        cl += [[-red[1][j], rd[j], uG[j]], [-red[1][j], rd[j], a[j]], [red[1][j], -rd[j]], [red[1][j], -uG[j], -a[j]]]
    if local:
        rows = {c: [row for row in range(R) if ((row >> x) & 1) == c] for c in (0, 1)}
        for i in range(r):
            cl.append([v[i][row] for row in range(R)]); cl.append([-v[i][row] for row in range(R)])
            for w in range(N):
                cl.append([(-v[i][row] if (row >> w) & 1 else v[i][row]) for row in range(R)])
            for c in (0, 1):
                cl.append([red[c][i]] + [v[i][row] for row in rows[c]])
                cl.append([red[c][i]] + [-v[i][row] for row in rows[c]])
                for w in range(k):
                    cl.append([red[c][i]] + [(-v[i][row] if (row >> w) & 1 else v[i][row]) for row in rows[c]])
        for i in range(r):
            for j in range(i + 1, r):
                d = [nv() for _ in range(R)]
                for row in range(R):
                    cl += [[-d[row], v[i][row], v[j][row]], [-d[row], -v[i][row], -v[j][row]]]
                cl.append(d)
                for c in (0, 1):
                    cl.append([red[c][i], red[c][j]] + [d[row] for row in rows[c]])
                if j == r - 1:  # wire i is not the complement of the output on side c
                    e = [nv() for _ in range(R)]
                    for row in range(R):
                        cl += [[-e[row], v[i][row], -v[j][row]], [-e[row], -v[i][row], v[j][row]]]
                    for c in (0, 1):
                        cl.append([red[c][i]] + [e[row] for row in rows[c]])
        cl.append([-n[r-1]])
    return cl, dict(n=n, a=a, s1=s1, s2=s2, v=v, N=N, r=r, k=k)

def decode(m, V):
    m = set(l for l in m if l > 0); N, r = V['N'], V['r']; out = []
    for i in range(r):
        i1 = [w for w in range(N + i) if V['s1'][i][w] in m][0]; i2 = [w for w in range(N + i) if V['s2'][i][w] in m][0]
        out.append(('NOT', i1) if V['n'][i] in m else (('AND' if V['a'][i] in m else 'OR'), i1, i2))
    return out

def variants(f, k):
    R = 1 << k; res = set()
    for pi in itertools.permutations(range(k)):
        g = [0] * R
        for row in range(R):
            r2 = sum(((row >> i) & 1) << pi[i] for i in range(k)); g[r2] = f[row]
        res.add(tuple(g)); res.add(tuple(g[R - 1 - row] for row in range(R)))  # f(not y): also a solution family (dual circuit)
    return res

if __name__ == '__main__':
    k, r = int(sys.argv[1]), int(sys.argv[2]); local = (len(sys.argv) < 4)
    cl, V = build(k, r, local)
    S = Cadical153(bootstrap_with=cl); R = 1 << k; out = V['v'][r - 1]
    cache = {}; nblk = 0; t0 = time.time()
    while S.solve():
        m = set(l for l in S.get_model() if l > 0)
        f = tuple(1 if out[row] in m else 0 for row in range(R))
        nf = tuple(1 - b for b in f)
        easy = synth(k, list(f), r - 4) or synth(k, list(nf), r - 4) if r > 4 else None
        if not easy:
            print('COUNTEREXAMPLE CANDIDATE f', f, decode(m, V), flush=True); break
        for g in variants(f, k):
            S.add_clause([(-out[row] if g[row] else out[row]) for row in range(R)]); nblk += 1
        if nblk % 200 < 50: print('blocked', nblk, 'last f', f, decode(m, V), round(time.time() - t0), flush=True)
    else:
        print('k', k, 'r', r, 'local', local, 'NO counterexample; blocked', nblk, 'time', round(time.time() - t0), flush=True)
