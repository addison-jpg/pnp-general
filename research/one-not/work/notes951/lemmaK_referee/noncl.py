"""Random non-CubeLocal instances (h depends on >= 2 inputs on the cube) for the F2 step / SEE+K3 (dwV8p). Run from research/one-not/."""
import random, sys
sys.path.insert(0, 'tools'); sys.path.insert(0, 'work/notes951/lemmaK_referee')
from kcheck import random_circuit
from f2synth import run

def h_support_on_cube(h, n, Q):
    cube = [x for x in range(1 << n) if x & Q == Q]
    dep = []
    for i in range(n):
        if Q >> i & 1: continue
        if any((h >> x & 1) != (h >> (x | 1 << i) & 1) for x in cube if not x >> i & 1): dep.append(i)
    return dep

def essential_not(c):
    T = c.tables()
    return any(T[o] != c.tables(force=0)[o] for o in c.outs) and any(T[o] != c.tables(force=1)[o] for o in c.outs)

if __name__ == '__main__':
    N, seed = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(seed)
    mk = lambda: {'heavy': 0, 'heavy_step': 0, 'heavy_see': 0, 'heavy_see_at_heavy_v': 0, 'light': 0, 'light_step': 0,
                  'light_see': 0, 'surv_nonempty_light': 0, 'see_gap_examples': [], 'heavy_seeK3': 0, 'light_seeK3': 0,
                  'seek3_gap_examples': []}
    st = {'noncl': mk(), 'noncl_ess': mk()}; bad = []
    for _ in range(N):
        n = rng.choice((4, 5, 6)); c = random_circuit(rng, n, rng.randrange(6, 18))
        if c is None or len(c.sets) < 2: continue
        Q = rng.randrange(1 << n) & rng.randrange(1 << n)
        h = c.tables()[c.h_wire]
        if len(h_support_on_cube(h, n, Q)) < 2: continue
        run(c, Q, st['noncl'], bad)
        if essential_not(c): run(c, Q, st['noncl_ess'], bad)
        if bad: print('FAIL', bad[0][0]); break
    for k, d in st.items():
        d.pop('see_gap_examples'); ex = d.pop('seek3_gap_examples')
        inst = d['heavy'] + d['light']
        print(k, 'instances', inst, '| step', d['heavy_step'] + d['light_step'], '| SEE+K3', d['heavy_seeK3'] + d['light_seeK3'], '| examples where SEE+K3 fails but step holds:', len(ex))

