"""Random correct one-NOT circuits with junk (light_gen.py's generator) through the lifted tests of lift_price.py:
kill test of Theorem G (a won U-game / pure game gives valid, pairwise disjoint classes with |S_w| - 1 gates each)
and the lifted price LP (sub-menu norm + world + ext); real-merge t* for comparison.
Run from the repo root: python3 -I 951/tools/kill_tests/gen_lift.py SEED COUNT [UMAX]"""
import sys, os, random, collections, json
here = os.path.dirname(os.path.abspath(__file__))
SEED0 = int(sys.argv[1]); COUNT0 = int(sys.argv[2]); UMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 6
sys.argv = [sys.argv[0], '951', str(SEED0), '0']
src = open(os.path.join(here, 'light_gen.py')).read()
exec(src[:src.index('RULES={}')])
sys.path.insert(0, here)
import global_price as GP, lift_price as LP, ugame
rng = random.Random(SEED0); st = collections.Counter(); ts = []
for it in range(COUNT0):
    n, S, G, outs = gen(rng)
    if sum(g[0] == 'not' for g in G) != 1 or len(S) < 2: continue
    try: L = GP.Lift(n, G, outs)
    except Exception: continue
    if not L.real_ok(S): st['incorrect'] += 1; continue
    st['circuits'] += 1
    h = L.h; mt = LP.minterms(h, n); Y = 1 << n; full = (1 << n) - 1
    g1 = LP.game1(n, S, h); g0 = LP.game0(n, S, h, mt)
    if g1 is not None:
        st['G1 won'] += 1; st['G1 check ' + LP.check_systems(L, S, outs, [(g1[w] | Y, [(1 << u) | Y for u in R]) for w, R in enumerate(S)])] += 1
    if g0 is not None:
        st['G0 won'] += 1; st['G0 check ' + LP.check_systems(L, S, outs, [(full & ~sum(1 << u for u in R), [g0[w][u] for u in R]) for w, R in enumerate(S)])] += 1
    if n <= UMAX:
        O = [[L.val(o, x) for x in range(1 << (n + 1))] for o in outs]
        sol = ugame.solve(n + 1, S, O); st['U-game run'] += 1
        if sol is not None:
            st['U-game won'] += 1; st['U-game check ' + LP.check_systems(L, S, outs, [(sol[w][0], list(sol[w][1])) for w in range(len(S))])] += 1
        else: st['U-game lost'] += 1
    menus = [LP.norm_menu(L, n, S, w, o, h, mt) | L.menu(R, o, ['world', 'ext'], 3) for w, (R, o) in enumerate(zip(S, outs))]
    t, _ = GP.lp_load(menus, len(L.gw)); ts.append(t)
    if t > 1 + 1e-7:
        st['lift t*>1 (sub-menu)'] += 1
        print('SUBMENU', json.dumps({'n': n, 'sets': S, 'gates': G, 'outs': outs, 'tstar': t}), flush=True)
    tr, _ = GP.lp_load([L.menu(R, o, ['real']) for R, o in zip(S, outs)], len(L.gw)); st['real t*>1'] += tr > 1 + 1e-7
print('STATS', dict(sorted(st.items())), 'max lifted t*', max(ts) if ts else None)
