"""Wall check for main 14:30 [ASK] (dwV8p): F2 step and SEE+K3 on essential-NOT circuits at cubes Q where h depends on >= 2
inputs (non-CubeLocal). Run from research/one-not/:  python3 work/notes951/lemmaK_referee/noncl_corpus.py K FILE.jsonl  (K circuits, 3 Q each)
or ... noncl_corpus.py all FILE.json (every Q)."""
import random, sys, json
sys.path.insert(0, 'tools'); sys.path.insert(0, 'work/notes951/lemmaK_referee')
from w951 import Circuit
from f2synth import run
from noncl import h_support_on_cube, essential_not
import gadget
rng = random.Random(7)
mk = lambda: {'heavy': 0, 'heavy_step': 0, 'heavy_see': 0, 'heavy_see_at_heavy_v': 0, 'light': 0, 'light_step': 0,
              'light_see': 0, 'surv_nonempty_light': 0, 'see_gap_examples': [], 'heavy_seeK3': 0, 'light_seeK3': 0,
              'seek3_gap_examples': []}
st = mk(); bad = []; circuits = 0; allq = sys.argv[1] == 'all'
for path in sys.argv[2:]:
    for c in (gadget.circuits_of(path) if not path.endswith('ladder.json') else
              [Circuit.from_dict(d) for d in json.load(open(path))]):
        if len(c.nots) != 1 or not c.sets or len(c.sets) != len(c.outs) or c.n > 9: continue
        try: c.validate(sums=True, one_not=True)
        except Exception: continue
        if not essential_not(c): continue
        circuits += 1
        h = c.tables()[c.h_wire]
        Qs = range(1 << c.n) if allq else [0] + [rng.randrange(1 << c.n) & rng.randrange(1 << c.n) for _ in range(2)]
        for Q in Qs:
            if len(h_support_on_cube(h, c.n, Q)) < 2: continue
            run(c, Q, st, bad)
            if bad: print('FAIL', bad[0][0], path); sys.exit(1)
        if circuits >= int(sys.argv[1] if not allq else 10**9) and not allq: break
ex = st.pop('seek3_gap_examples'); st.pop('see_gap_examples')
inst = st['heavy'] + st['light']
print(sys.argv[2].split('/')[-1], 'essential-NOT circuits', circuits, '| non-CubeLocal (circuit, Q)', inst, '| step', st['heavy_step'] + st['light_step'], '| SEE+K3', st['heavy_seeK3'] + st['light_seeK3'])
for e in ex[:1]: print('  SEE+K3 fails, step holds:', e[0][:200], 'Q =', e[1])
