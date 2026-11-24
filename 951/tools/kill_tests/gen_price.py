"""Random correct one-NOT circuits with junk (light_gen.py's generator) through the global price LP
(global_price.py): t* = min max load over fractional choices of real merge sets (and other menus), and the
2-gate 0/1 excess.  Run from the repo root: python3 -I 951/tools/kill_tests/gen_price.py SEED COUNT [menus]"""
import sys, os, random, collections, json
here = os.path.dirname(os.path.abspath(__file__))
SEED0 = int(sys.argv[1]); COUNT0 = int(sys.argv[2]); kinds = (sys.argv[3] if len(sys.argv) > 3 else 'real').split(',')
sys.argv = [sys.argv[0], '951', str(SEED0), '0']
src = open(os.path.join(here, 'light_gen.py')).read()
exec(src[:src.index('RULES={}')])
sys.path.insert(0, here)
import global_price as GP
rng = random.Random(SEED0); st = collections.Counter(); ts = []
for it in range(COUNT0):
    n, S, G, outs = gen(rng)
    if sum(g[0] == 'not' for g in G) != 1: continue
    try: L = GP.Lift(n, G, outs)
    except Exception: continue
    if not L.real_ok(S): st['incorrect'] += 1; continue
    st['circuits'] += 1
    menus = [L.menu(R, o, kinds) for R, o in zip(S, outs)]
    t, pi = GP.lp_load(menus, len(L.gw)); ts.append(t)
    r = GP.kgate(menus, len(L.gw), 2)
    if r and r[0] > 0: st['kgate2_viol'] += 1
    if t > 1 + 1e-7:
        st['tstar>1'] += 1
        print('VIOLATION', json.dumps({'n': n, 'sets': S, 'gates': G, 'outs': outs, 'tstar': t}), flush=True)
print('STATS', dict(st), 'menus', kinds, 'max t*', max(ts) if ts else None,
      'hist', collections.Counter(round(t, 3) for t in ts).most_common(6))
