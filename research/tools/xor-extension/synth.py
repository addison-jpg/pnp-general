# Exact synthesis by SAT: is there a circuit with r gates (AND/OR fan-in 2, NOT, all counted) for a target?
import sys, itertools, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc

def synth(N, tt, r, shape=False):
    """tt: list of 0/1 of length 2^N (row a: bit i = input i). Returns list of gates or None."""
    R = 1 << N
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
        for x, y in itertools.combinations(lits, 2): cl.append([-x, -y])
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
    for row in range(R):
        cl.append([v[r - 1][row] if tt[row] else -v[r - 1][row]])
    if shape:
        # residual shape: input x = N-1 is read by exactly one AND and one OR; each has exactly one
        # reader; the AND's reader is an OR gate, the OR's reader is an AND gate.
        x = N - 1
        rd = [nv() for _ in range(r)]
        for i in range(r):
            cl += [[-rd[i], s1[i][x], s2[i][x]], [rd[i], -s1[i][x]], [rd[i], -s2[i][x]]]
            cl.append([-rd[i], -n[i]])
        enc = CardEnc.equals(lits=rd, bound=2, top_id=cnt[0]); cnt[0] = max(cnt[0], enc.nv); cl += enc.clauses
        enc = CardEnc.equals(lits=[nv() for _ in range(0)] or rd, bound=2, top_id=cnt[0]); cnt[0] = max(cnt[0], enc.nv)
        ra = [nv() for _ in range(r)]  # reader that is an AND
        for i in range(r):
            cl += [[-ra[i], rd[i]], [-ra[i], a[i]], [ra[i], -rd[i], -a[i]]]
        enc = CardEnc.equals(lits=ra, bound=1, top_id=cnt[0]); cnt[0] = max(cnt[0], enc.nv); cl += enc.clauses
        for i in range(r - 1):
            users = []
            for j in range(i + 1, r):
                u = nv(); users.append((j, u))
                cl += [[-u, s1[j][N + i], s2[j][N + i]], [u, -s1[j][N + i]], [u, -s2[j][N + i]]]
            # if i reads x: exactly one user; user op: OR if i is AND, AND if i is OR; user not NOT
            for (j, u), (j2, u2) in itertools.combinations(users, 2):
                cl.append([-rd[i], -u, -u2])
            for j, u in users:
                cl.append([-rd[i], -u, -n[j]])
                cl.append([-rd[i], -u, -a[i], -a[j]])
                cl.append([-rd[i], -u, a[i], a[j]])
        cl.append([-rd[r - 1]])
    with Cadical153(bootstrap_with=cl) as S:
        if not S.solve(): return None
        m = set(l for l in S.get_model() if l > 0)
        out = []
        for i in range(r):
            i1 = [w for w in range(N + i) if s1[i][w] in m][0]; i2 = [w for w in range(N + i) if s2[i][w] in m][0]
            out.append(('NOT', i1) if n[i] in m else (('AND' if a[i] in m else 'OR'), i1, i2))
        return out

def xor_ext(k, f):  # f: truth table int over k vars -> tt list over k+1 vars of x XOR f, x = last input
    return [((f >> (row & ((1 << k) - 1))) & 1) ^ (row >> k) for row in range(1 << (k + 1))]

if __name__ == '__main__':
    sz = {}
    for l in open('sizes3.txt'):
        u, w = l.split(); sz[int(u)] = int(w)
    f = [g for g in range(1, 255) if sz[g] == 3 and sz[255 ^ g] == 3][0]
    for r, sh in ((6, False), (7, False), (7, True), (6, True)):
        t = time.time(); c = synth(4, xor_ext(3, f), r, sh); print('f', f, 'r', r, 'shape', sh, 'SAT' if c else 'UNSAT', round(time.time() - t, 2), c)
