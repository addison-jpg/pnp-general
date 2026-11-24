"""Kill test for INTERNAL (PROOF_PLAN_SUGGESTIONS §6, dwV8p): for each block B that one first-joining gate absorbs at once,
the union-find restricted to B over earlier OR gates whose real blocks avoid v gives |B| - 1 internal merges; INTERNAL at v:
they are distinct, all in F2(Q), all die, and no first-joining gate survives. Run from 951/:  python3 .../internal.py"""
import random, sys, json, glob
sys.path.insert(0, 'tools'); sys.path.insert(0, 'work/notes951/lemmaK_referee')
from kcheck import random_circuit
from juf import f2set
from w951 import Circuit

def check(c, Q, st):
    n = c.n; T = c.tables(); h = T[c.h_wire]
    sets = [sum(1 << u for u in S) for S in c.sets]
    alive = [i for i, m in enumerate(sets) if m & Q == 0]
    if not alive: return
    apts = sorted({u for i in alive for u in c.sets[i]})
    F2 = f2set(c, T, Q)
    st['inst'] += 1
    any_root = any_int = any_step = False
    why = {}
    for v in apts:
        star = [i for i in alive if sets[i] >> v & 1]
        P = sorted({u for i in star for u in c.sets[i]}); cost = len(P) - 1
        gain = F2 - f2set(c, T, Q | 1 << v)
        any_step |= len(gain) >= cost
        first = {}
        blk = {}
        for w_ in range(n, n + len(c.gates)):
            if T[w_] >> Q & 1: continue
            b = {x for x in P if T[w_] >> (Q | 1 << x) & 1}
            blk[w_] = b
            if v in b:
                for u in b:
                    if u != v and u not in first: first[u] = w_
        F = set(first.values())
        surv = F - gain
        groups = {}
        for u, g in first.items(): groups.setdefault(g, []).append(u)
        internal = []
        for g, B in groups.items():
            if len(B) < 2: continue
            comp = {x: x for x in B}
            def find(x):
                while comp[x] != x: x = comp[x]
                return x
            for w_ in range(n, g):
                if c.gates[w_ - n][0] != 'or' or w_ not in blk or v in blk[w_]: continue
                a, b2 = c.gates[w_ - n][1:]
                ba = [x for x in B if a in blk and x in blk[a]] if a >= n else ([a] if a in B else [])
                bb = [x for x in B if b2 in blk and x in blk[b2]] if b2 >= n else ([b2] if b2 in B else [])
                if ba and bb and find(ba[0]) != find(bb[0]):
                    comp[find(ba[0])] = find(bb[0]); internal.append(w_)
            if len({find(x) for x in B}) != 1:
                why['B not joined'] = why.get('B not joined', 0) + 1
        ok_int = (not surv) and len(internal) == len(set(internal)) and all(g in gain for g in internal) \
            and not (set(internal) & F)
        if cost - len(F) == 0 and not surv: any_root = True
        if ok_int: any_int = True
        else:
            if surv: why['F survivor'] = why.get('F survivor', 0) + 1
            if len(internal) != len(set(internal)): why['internal collide'] = why.get('internal collide', 0) + 1
            if any(g not in F2 for g in internal): why['internal not in F2'] = why.get('internal not in F2', 0) + 1
            elif any(g not in gain for g in internal): why['internal survives'] = why.get('internal survives', 0) + 1
    st['root'] += any_root; st['internal'] += any_int; st['step'] += any_step
    if not any_int:
        st['int_fail'] += 1
        for k, x in why.items(): st['why_' + k] = st.get('why_' + k, 0) + 1

st = dict(inst=0, root=0, internal=0, step=0, int_fail=0)
for seed in (51, 52):
    rng = random.Random(seed)
    for _ in range(60000):
        n = rng.choice((4, 5, 6)); c = random_circuit(rng, n, rng.randrange(6, 18))
        if c is None or len(c.sets) < 2: continue
        check(c, rng.randrange(1 << n) & rng.randrange(1 << n), st)
print('random', st)
st = dict(inst=0, root=0, internal=0, step=0, int_fail=0)
for p in sorted(glob.glob('data/witnesses/*.json')):
    c = Circuit.from_dict(json.load(open(p)))
    if len(c.nots) != 1: continue
    for Q in range(0, 1 << c.n, max(1, (1 << c.n) // 16)): check(c, Q, st)
print('witnesses', st)
