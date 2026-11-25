# Conjecture C3_k (k-point step) at EVERY cube. Serves README items L5, C3.
# depth(Q) = least |D|, D a set of unfixed points, with base(Q+D) < base(Q) and slack(Q+D) <= slack(Q)
# (slack = |realWitness| - base; by the chain sum L5 this is: some path of |D| points has sum(gain - cost) >= 0 at its end).
# 'alive' variant: every point of the path lies on an alive set when it is fixed (the form chain_depth.py tests).
# Run from the repo root: python3 -I research/one-not/tools/kill_tests/c3_allq.py [cap] [files...]   (default: all witness files)
import sys, os, json, glob, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import f2lib as L
def slack_table(c):
    n = c['n']; S = c['S']; N = 1 << n
    smask = [sum(1 << u for u in R) for R in S]
    items = collections.defaultdict(list)
    for (i, wi), M in c['wm'].items(): items[wi].append((i, M))
    cnt = [0] * N; base = [0] * N
    def rec(v, Q, cb):
        if v == n:
            al = [w for w in range(len(S)) if not smask[w] & Q]
            base[Q] = sum(len(S[w]) - 1 for w in al)
            cnt[Q] = len({i for w in al for i, M in items[w] if M & cb}); return
        rec(v + 1, Q, cb); rec(v + 1, Q | 1 << v, cb & c['X'][v])
    rec(0, 0, c['FULL'])
    return cnt, base, smask
def depths(c, cap):
    n = c['n']; cnt, base, smask = slack_table(c); N = 1 << n
    hist = collections.Counter(); hista = collections.Counter(); worst = None; minslack = None
    for Q in range(N):
        if base[Q] == 0: continue
        s0 = cnt[Q] - base[Q]; minslack = s0 if minslack is None else min(minslack, s0)
        free = [v for v in range(n) if not Q >> v & 1]
        d = None
        for k in range(1, cap + 1):
            for D in itertools.combinations(free, k):
                Q2 = Q | sum(1 << v for v in D)
                if base[Q2] < base[Q] and cnt[Q2] - base[Q2] <= s0: d = k; break
            if d: break
        hist[d] += 1
        if d != 1 and (worst is None or (d or 99) > worst[0]): worst = (d or 99, Q)
        # alive paths
        fr = {Q}; da = None
        for k in range(1, cap + 1):
            nx = set()
            for P in fr:
                alp = 0
                for w in range(len(smask)):
                    if not smask[w] & P: alp |= smask[w]
                for v in range(n):
                    if alp >> v & 1:
                        P2 = P | 1 << v
                        if cnt[P2] - base[P2] <= s0: da = k
                        nx.add(P2)
            if da: break
            fr = nx
        hista[da] += 1
    return hist, hista, worst, minslack
if __name__ == '__main__' and len(sys.argv) > 2 and sys.argv[2] == 'corpus':
    # python3 -I research/one-not/tools/kill_tests/c3_allq.py cap corpus NMAX seed count : every circuit file under research/one-not/ with n <= NMAX, plus randgen
    cap = int(sys.argv[1]); CS = L.corpus(int(sys.argv[3])) + L.randgen(int(sys.argv[4]), int(sys.argv[5]))
    tot = collections.Counter(); deep = []
    for c in CS:
        h, ha, worst, ms = depths(c, cap); tot.update(h)
        if any(k != 1 for k in h): deep.append((c['name'], dict(h)))
    print('circuits', len(CS), 'cubes with base > 0:', sum(tot.values()), 'depth histogram:', dict(sorted(tot.items(), key=str)))
    for x in deep[:20]: print('  depth > 1:', x)
elif __name__ == '__main__':
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    files = sys.argv[2:] or sorted(glob.glob('research/one-not/data/witnesses/*.json') + glob.glob('research/one-not/data/witnesses/nonlocal/*.json'))
    print('| circuit | n | cubes with base > 0 | depth histogram (free) | depth histogram (alive paths) | min slack | a cube of largest depth |'); print('|---|---|---|---|---|---|---|')
    tot = collections.Counter()
    for f in files:
        d = json.load(open(f))
        if d['n'] > 16: continue                      # larger witnesses: c3_tab.py, c3_dnf.py, c3_cert.py
        c = L.mk(d.get('name', f), d['n'], d['sets'], d['gates'], d['outs'], need_not=False)
        if c is None: print('|', os.path.basename(f), '| INCORRECT |'); continue
        h, ha, worst, ms = depths(c, cap); tot.update(h)
        print('|', os.path.basename(f), '|', d['n'], '|', sum(h.values()), '|', dict(sorted(h.items(), key=str)), '|', dict(sorted(ha.items(), key=str)), '|', ms, '|', (worst[0], [v for v in range(d['n']) if worst[1] >> v & 1]) if worst else '', '|', flush=True)
    print('total (free):', dict(sorted(tot.items(), key=str)))
