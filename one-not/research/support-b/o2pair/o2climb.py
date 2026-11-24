r"""F2 (fable_worlds.md): hill-climb attack on LEMMA O2-PAIR. Two sets A, B (|A ∩ B| <= 1) in configuration O2:
  O2 := for every z' with z' ∩ B = ∅ and |A \ z'| <= 1: h(z') = 1 and h(z' & ~mask(A)) = 0; and the same with A, B swapped.
O2-PAIR claims: some zero points z_A, z_B have disjoint merge sets M_{z_A}(A), M_{z_B}(B).
Score = number of disjoint (z_A, z_B) pairs (all zero points); 0 with O2 holding = COUNTEREXAMPLE (MergeSDR fails on 2 sets).
Kept invariant: correct, exactly one NOT, O2, every gate read (gadgets are spliced as o' = o | g when g <= OR(S),
else o' = o | (g & o), which leaves o's function unchanged). Moves: rewire one gate input, flip and/or, insert a gadget
G(top,top) = (x_u1 & x_v1) | (x_u2 & x_v2), G(chain) = ((x_u1 & N) | x_v1) | ((x_u2 & N) | x_v2), or a random 2-gate junk.
Usage: python3 o2climb.py START(cfgI|cxT2) SEED SECONDS OUT.jsonl"""
import itertools, json, os, random, sys, time
sys.path.insert(0, os.environ.get('W951_TOOLS', '/home/user/c951/tools'))
from w951 import Circuit, systems
CORP = '/home/user/pequalnp-proofs/research/front/no_minCE/supportB/corpora/w9/'

def start(name):
    if name == 'cfgI':
        c = Circuit.from_dict(json.load(open(CORP + 'fb__cfgI.json'))); keep = [0, 1]
    else:
        c = Circuit.from_dict(json.load(open(CORP + 'fc__cxT2.json')))
        keep = [i for i, S in enumerate(c.sets) if set(S) in ({1, 2, 7, 8}, {0, 2, 3, 4})]
    drop = [i for i in range(len(c.sets)) if i not in keep]
    r = c.delete_outputs(drop) if drop else None
    c2 = r.circuit if r is not None else c
    return c2.cleanup().circuit if hasattr(c2, 'cleanup') else c2

def zeros(c, S):
    rest = [v for v in range(c.n) if v not in S]
    return [sum(1 << v for v, b in zip(rest, bits) if b) for bits in itertools.product((0, 1), repeat=len(rest))]

def merges(c, S, z):
    g, wz, B = systems.system(c, S, z, {u: z | (1 << u) for u in S})
    return frozenset(systems.merges(c, S, B)[0])

def hval(c, x): return c.eval(x)[c.h_wire]

def o2(c, A, B):
    mA = sum(1 << u for u in A)
    for X, Y in ((A, B), (B, A)):
        mX = sum(1 << u for u in X)
        for z in zeros(c, Y):
            if len([u for u in X if not z >> u & 1]) <= 1:
                if hval(c, z) != 1 or hval(c, z & ~mX) != 0: return False
    return True

def score(c):
    A, B = c.sets[0], c.sets[1]
    MA = [merges(c, A, z) for z in zeros(c, A)]; MB = [merges(c, B, z) for z in zeros(c, B)]
    return sum(1 for a in MA for b in MB if not (a & b)), len(MA) * len(MB)

def ok(c):
    return len(c.sets) == 2 and len(c.nots) == 1 and c.s <= 45 and c.is_correct() and c.all_read() and o2(c, c.sets[0], c.sets[1])

def splice(d, gates, w):
    """append gates (list of [op,a,b] with symbolic 'G<k>' refs to earlier new gates) and OR the last into output w."""
    n = d['n']; G = d['gates']; base = n + len(G); idx = []
    for op, a, b in gates:
        f = lambda x: idx[int(x[1:])] if isinstance(x, str) else x
        G.append([op, f(a), f(b)]); idx.append(n + len(G) - 1)
    o = d['outs'][w]; g = idx[-1]
    G.append(['and', g, o]); G.append(['or', o, n + len(G) - 1]); d['outs'][w] = n + len(G) - 1
    return d

def mutate(d, rng, c):
    d = json.loads(json.dumps(d)); n = d['n']; G = d['gates']; A, B = d['sets'][0], d['sets'][1]
    N = c.not_wire; r = rng.random()
    if r < 0.45:
        k = rng.randrange(len(G)); g = G[k]
        if g[0] != 'not':
            if rng.random() < 0.75: g[rng.choice([1, 2])] = rng.randrange(n + k)
            else: g[0] = 'and' if g[0] == 'or' else 'or'
        return d
    u1, u2 = rng.sample(A, 2); v1, v2 = rng.sample(B, 2); w = rng.randrange(2)
    if r < 0.65:   # G(top,top)
        return splice(d, [['and', u1, v1], ['and', u2, v2], ['or', 'G0', 'G1']], w)
    if r < 0.85:   # G(chain)
        return splice(d, [['and', u1, N], ['or', 'G0', v1], ['and', u2, N], ['or', 'G2', v2], ['or', 'G1', 'G3']], w)
    a, b = rng.randrange(n + len(G)), rng.randrange(n + len(G))
    return splice(d, [[rng.choice(['and', 'or']), a, b], [rng.choice(['and', 'or']), 'G0', rng.randrange(n + len(G))]], w)

if __name__ == '__main__':
    name, seed, secs, out = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
    rng = random.Random(seed); c = start(name)
    assert ok(c), ('start circuit fails invariants', c.sets, c.is_correct(), c.all_read())
    cur = c.to_dict(); cs = score(c); best = cs
    print(f'start {name}: sets {c.sets} n={c.n} s={c.s} disjoint pairs {cs[0]}/{cs[1]}', flush=True)
    fo = open(out, 'a', buffering=1); t0 = time.time(); it = acc = 0
    while time.time() - t0 < secs:
        it += 1
        try:
            d = mutate(cur, rng, Circuit.from_dict(cur)); c2 = Circuit.from_dict(d)
            if not ok(c2): continue
            s2 = score(c2)
        except Exception:
            continue
        frac = s2[0] / s2[1]
        if frac <= cs[0] / cs[1] or rng.random() < 0.01:
            cur, cs = d, s2; acc += 1
            if frac < best[0] / best[1]:
                best = s2
                fo.write(json.dumps({'disjoint': s2[0], 'pairs': s2[1], 's': c2.s, 'ess': c2.is_essential(), 'c': d}) + '\n')
                print(f'{time.time()-t0:6.0f}s it={it} best disjoint {s2[0]}/{s2[1]} s={c2.s} ess={c2.is_essential()}', flush=True)
                if s2[0] == 0: print('!!! O2-PAIR COUNTEREXAMPLE', flush=True); break
    print(f'done it={it} acc={acc} best={best[0]}/{best[1]}', flush=True)
