"""Smallest (sets, h) on which the U-GAME (ugame.py, exact function-level reach of Theorem U, DD-normal outputs) is
lost; cross-check of the dichotomy Theorem D (all |S_w| >= 3: U-game won <=> a pure-world game G0 / G1 of
lift_price.py is won); and what the lifted price LP says on the DD-normal circuit of such a pair:
    o_w = ((s_w | h) & N) | (s_w & h),  s_w = OR(S_w), N = NOT h   (lift: O_w(x,0) = s_w & h, O_w(x,1) = s_w | h),
with the h-formula and the selector gates placed BEFORE the sums when --junkfirst.
Usage: python3 -I lift_obstruction.py N [--minsize K] [--maxsets M] [--lp]   (all non-constant monotone h on N inputs)
"""
import sys, os, itertools, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import global_price as GP, lift_price as LP, ugame

def monotone_fns(n):
    P = 1 << n; out = []
    def rec(x, f):
        if x == P: out.append(tuple(f)); return
        lo = max((f[x & ~(1 << v)] for v in range(n) if x >> v & 1), default=0)
        for b in ((1,) if lo else (0, 1)):
            f.append(b); rec(x + 1, f); f.pop()
    rec(0, []); return out

def families(n, maxsets=3):
    subs = [c for r in range(2, n + 1) for c in itertools.combinations(range(n), r)]
    seen = set()
    for m in range(2, maxsets + 1):
        for F in itertools.combinations(subs, m):
            if any(len(set(a) & set(b)) > 1 for a, b in itertools.combinations(F, 2)): continue
            yield [list(s) for s in F]

def dd_circuit(n, S, h):
    """DD-normal circuit: h as OR of minterms (monotone prefix), NOT, then for every set the chain and the selectors."""
    G = []; w = lambda: n + len(G) - 1
    def fold(op, ws):
        cur = ws[0]
        for x in ws[1:]:
            G.append([op, cur, x]); cur = w()
        return cur
    mt = LP.minterms(h, n)
    terms = [fold('and', [v for v in range(n) if m >> v & 1]) for m in mt]
    hw = fold('or', terms)
    if hw < n: G.append(['or', hw, hw]); hw = w()        # make h a gate wire
    G.append(['not', hw]); N = w()
    outs = []
    for R in S:
        s = fold('or', list(R))
        G.append(['or', s, hw]); a = w(); G.append(['and', a, N]); b = w()
        G.append(['and', s, hw]); c = w(); G.append(['or', b, c]); outs.append(w())
    return G, outs

def main():
    n = int(sys.argv[1]); LPF = '--lp' in sys.argv
    MS = int(sys.argv[sys.argv.index('--minsize') + 1]) if '--minsize' in sys.argv else 2
    MX = int(sys.argv[sys.argv.index('--maxsets') + 1]) if '--maxsets' in sys.argv else 3
    st = collections.Counter(); shown = 0
    fns = [f for f in monotone_fns(n) if 0 < sum(f) < len(f)]
    fams = [F for F in families(n, MX) if min(len(R) for R in F) >= MS]
    for S in fams:
        for h in fns:
            mt = LP.minterms(h, n)
            if not mt or mt == [0]: continue
            st['pairs (sets, h)'] += 1
            g1 = LP.game1(n, S, h); g0 = LP.game0(n, S, h, mt)
            st['G1 won'] += g1 is not None; st['G0 won'] += g0 is not None
            pure = g1 is not None or g0 is not None
            u = ugame.solve(n + 1, S, ugame.dd_outputs(n, S, h)) is not None
            st['U-game won'] += u; st['pure won, U lost (must be 0)'] += pure and not u
            if MS >= 3: st['U won, pure lost (Theorem D: must be 0)'] += u and not pure
            if not u:
                st['U-game lost'] += 1
                if LPF:
                    G, outs = dd_circuit(n, S, h)
                    L = GP.Lift(n, G, outs); assert L.real_ok(S)
                    menus = [LP.norm_menu(L, n, S, w, o, list(h), mt) | L.menu(R, o, ['world', 'ext'], 4)
                             for w, (R, o) in enumerate(zip(S, outs))]
                    t, _ = GP.lp_load(menus, len(L.gw))
                    st['U-game lost: DD circuit t* <= 1'] += t <= 1 + 1e-7; st['U-game lost: DD circuit t* > 1 (sub-menu)'] += t > 1 + 1e-7
                    if t > 1 + 1e-7 and shown < 5:
                        shown += 1; print('SUBMENU FAIL', S, 'minterms', [bin(m) for m in mt], 't*', t, json.dumps({'n': n, 'sets': S, 'gates': G, 'outs': outs}))
                elif shown < 5:
                    shown += 1; print('LOST', S, 'minterms of h', [[v for v in range(n) if m >> v & 1] for m in mt])
    print('n =', n, 'families', len(fams), 'monotone h (non-constant)', len(fns), dict(sorted(st.items())))

if __name__ == '__main__':
    main()
