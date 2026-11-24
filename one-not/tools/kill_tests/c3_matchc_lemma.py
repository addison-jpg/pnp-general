# Kill test for Lemma 3 and Theorem 4 of board/agents/fable-chain-sum.md (MATCH-C(k), every set D of points).
# Serves README item C3.  Index i is TOUCHED by D if u_i or a_i is in D.  Lemma 3: every OR gate outside the list
#   p_i, p'_i, e_i (i touched), tree gates of f_A and f_B over a touched index, h, X_A, X_B, o_A, o_B
# is in realWitness(D).  Theorem 4: slack(D) - slack(empty) >= k - 5 - 2*ceil(log2 k) - j*(5 + 2*ceil(log2(k/j))), j = |D| >= 1.
# Run: python3 -I one-not/tools/kill_tests/c3_matchc_lemma.py [trials per k=200] [k ...]
import sys, os, random, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c3_dnf as C, f2_nonlocal_build as B
trials = int(sys.argv[1]) if len(sys.argv) > 1 else 200
ks = [int(x) for x in sys.argv[2:]] or [7, 8, 11, 16, 23, 32, 40]
rng = random.Random(7); tot = bad = 0
for k in ks:
    d = B.match(k, 's', True); n = d['n']; c = C.load(d); G = d['gates']
    ors = [n + i for i, g in enumerate(G) if g[0] == 'or']; assert len(ors) == 5 * k + 3
    # leaves under each gate below the NOT gate: the indices i whose p_i or p'_i feeds it
    leaf = {}
    for i, g in enumerate(G):
        w = n + i
        if g[0] == 'not': break
        if g[0] == 'or' and g[1] < n: leaf[w] = {g[1] % (k + 1)}                    # p_i = x_{u_i} v j_i, p'_i = x_{a_i} v j'_i
        elif g[0] == 'or': leaf[w] = leaf[g[1]] | leaf[g[2]]
    hw = [n + i for i, g in enumerate(G) if g[0] == 'not'][0] - 1                 # h is the gate before the NOT gate
    special = {hw} | set(d['outs'][:2]) | set(d['outs'][-2:])                      # h, o_A, o_B, X_A, X_B
    eout = {d['outs'][2 + i]: i for i in range(k)}
    F0 = C.rw(c, 0); s0 = len(F0) - C.base(c, 0); assert len(F0) == len(ors)
    for _ in range(trials):
        j = rng.choice([1, 1, 2, 2, 3, 4, 5, rng.randint(1, n)]); D = rng.sample(range(n), j); Q = sum(1 << v for v in D)
        T = {v % (k + 1) for v in D if v % (k + 1) != k}
        allowed = set(special) | {w for w, I in leaf.items() if w != hw and I & T} | {w for w, i in eout.items() if i in T}
        F = set(C.rw(c, Q)); gone = set(ors) - F
        ds = (len(F) - C.base(c, Q)) - s0
        bound = k - 5 - 2 * math.ceil(math.log2(k)) - j * (5 + 2 * math.ceil(math.log2(k / j))) if j <= k else None
        tot += 1
        if not gone <= allowed or (bound is not None and ds < bound): bad += 1; print('FAIL k', k, 'D', D, sorted(gone - allowed), ds, bound)
    print('k', k, 'n', n, 'trials', trials, 'ok', flush=True)
print('Lemma 3 and Theorem 4: %d of %d random D pass' % (tot - bad, tot))
