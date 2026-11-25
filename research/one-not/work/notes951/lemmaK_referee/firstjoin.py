"""Kill test for Step 2-prime of PROOF_PLAN_SUGGESTIONS §6 (dwV8p): first-joining gates f(u), u in P minus v (first wire,
zero at Q, whose real block contains v and u). Checks f(u) is an OR gate in F2(Q) ∩ SEE(v); counts ROOT-OK (some v with
cost(v) distinct f-gates, all dying) and, at heavy v, whether other dying gates cover the deficit.
Run from research/one-not/:  python3 work/notes951/lemmaK_referee/firstjoin.py N SEED"""
import random, sys
sys.path.insert(0, 'tools'); sys.path.insert(0, 'work/notes951/lemmaK_referee')
from kcheck import random_circuit
from juf import f2set
from w951 import Circuit
import json

def analyse(c, Q, st):
    n = c.n; T = c.tables(); h = T[c.h_wire]
    sets = [sum(1 << u for u in S) for S in c.sets]
    alive = [i for i, m in enumerate(sets) if m & Q == 0]
    if not alive: return
    apts = sorted({u for i in alive for u in c.sets[i]})
    F2 = f2set(c, T, Q)
    st['inst'] += 1
    root_ok = m0zero = False
    for v in apts:
        star = [i for i in alive if sets[i] >> v & 1]
        P = sorted({u for i in star for u in c.sets[i]}); cost = len(P) - 1
        F2v = f2set(c, T, Q | 1 << v); gain = F2 - F2v
        # f(u): first wire whose block (zero at Q; points x of P with real wire(Q + e_x) = 1) contains v and u
        first = {}
        for w_ in range(n, n + len(c.gates)):
            if T[w_] >> Q & 1: continue
            blk = {x for x in P if T[w_] >> (Q | 1 << x) & 1}
            if v in blk:
                for u in blk:
                    if u != v and u not in first: first[u] = w_
        assert set(first) == set(P) - {v}, 'some u never joins v'
        Fv = set(first.values())
        for g in Fv:
            assert c.gates[g - n][0] == 'or' and g in F2 and (T[g] >> (Q | 1 << v) & 1), 'f(u) not an OR SEE gate'
        st['pairs'] += 1; st['m0_total'] += cost - len(Fv)
        if len(Fv) == cost: m0zero = True
        if len(Fv) >= cost and all(g in gain for g in Fv): root_ok = True
        heavy = h >> (Q | 1 << v) & 1
        if heavy:
            st['heavy_pairs'] += 1
            st['heavy_extra_ge_m0'] += len(gain - Fv) >= cost - len(Fv)
    st['root_ok'] += root_ok; st['m0zero'] += m0zero

N, seed = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(seed)
st = dict(inst=0, pairs=0, root_ok=0, m0zero=0, m0_total=0, nvm_in_gain=0, nvm_not_F2=0, heavy_pairs=0, heavy_extra_ge_m0=0)
for _ in range(N):
    n = rng.choice((4, 5, 6)); c = random_circuit(rng, n, rng.randrange(6, 18))
    if c is None or len(c.sets) < 2: continue
    analyse(c, rng.randrange(1 << n) & rng.randrange(1 << n), st)
print('random', st)
st = dict(inst=0, pairs=0, root_ok=0, m0zero=0, m0_total=0, nvm_in_gain=0, nvm_not_F2=0, heavy_pairs=0, heavy_extra_ge_m0=0)
import glob
for p in sorted(glob.glob('research/data/witnesses/*.json')):
    c = Circuit.from_dict(json.load(open(p)))
    if len(c.nots) != 1: continue
    for Q in range(0, 1 << c.n, max(1, (1 << c.n) // 16)): analyse(c, Q, st)
print('witnesses', st)
