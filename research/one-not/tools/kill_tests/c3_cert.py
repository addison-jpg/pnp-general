# Certificate check of a counterexample to Conjecture C3_k on a circuit too large for truth tables (n > 26).
# Serves README items L5, C3.  For every set D of at most cap points (with smaller base) it asks c3_dnf.py for one witness
# (set, zero point Z, atoms u, u') per gate and CHECKS each witness here by evaluating the circuit at Z, Z+e_u, Z+e_u'
# (no shared evaluator; c3_dnf is an untrusted oracle).  This certifies |realWitness(Q+D)| >= r(D).  With the trivial bound
# |realWitness(Q)| <= number of OR gates it certifies slack(Q+D) - slack(Q) >= r(D) - base(Q+D) - (#OR - base(Q)) for all D.
# Correctness of the circuit itself is checked on sampled inputs and all inputs of weight <= 2 only (state this with the result).
# Run: python3 -I research/one-not/tools/kill_tests/c3_cert.py FILE.json cap
import sys, os, json, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c3_dnf as O
d = json.load(open(sys.argv[1])); cap = int(sys.argv[2]); n = d['n']; S = d['sets']; G = d['gates']
def ev(x):
    w = [x >> i & 1 for i in range(n)]
    for g in G: w.append(1 - w[g[1]] if g[0] == 'not' else (w[g[1]] & w[g[2]] if g[0] == 'and' else w[g[1]] | w[g[2]]))
    return w
assert O.sample_correct(d), 'incorrect on a sampled input'
c = O.load(d); ors = [n + k for k, g in enumerate(G) if g[0] == 'or']; b0 = sum(len(R) - 1 for R in S)
ub0 = len(ors) - b0; least = {}; checked = 0; cache = {}
def evc(x):
    if x not in cache:
        if len(cache) > 400000: cache.clear()
        cache[x] = ev(x)
    return cache[x]
for k in range(1, cap + 1):
    for D in itertools.combinations(range(n), k):
        Q = sum(1 << v for v in D); b = sum(len(R) - 1 for R in S if not set(R) & set(D))
        if b == b0: continue
        r = 0
        for i in ors:
            if i not in c['cands']: continue
            wt = O.witness(c, i, Q)
            if wt is None: continue
            w, Z, u, u2 = wt; R = S[w]
            assert Z & Q == Q and not any(Z >> x & 1 for x in R) and u != u2 and u in R and u2 in R and not set(R) & set(D)
            assert evc(Z)[i] == 0 and evc(Z | 1 << u)[i] == 1 and evc(Z | 1 << u2)[i] == 1, 'bad witness'
            r += 1; checked += 1
        ds = (r - b) - ub0
        if k not in least or ds < least[k][0]: least[k] = (ds, list(D))
print(d.get('name'), 'n', n, 'OR gates', len(ors), 'base', b0, 'slack(empty) <=', ub0, '; witnesses checked:', checked)
print('certified lower bound on slack(D) - slack(empty), least over |D| = j:', {k: v[0] for k, v in least.items()}, 'at', {k: v[1] for k, v in least.items()})
print('C3_%d at the empty cube:' % cap, 'FAILS (certified)' if all(v[0] > 0 for v in least.values()) else 'not refuted by this certificate')
