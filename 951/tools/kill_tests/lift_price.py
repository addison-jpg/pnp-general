"""Lifted price inequality, function-level part (951/board/agents/fable-global-price.md).

For a correct one-NOT circuit (sets S_w, h = input of the NOT) this script
  1. solves the two PURE-WORLD U-GAMES on (sets, h) alone (Theorems G0 / G1 of the note):
       world 0: zero (top_w, 0), atoms (A_u, 0), h(A_u) = 1, A_u & S_w = {u}; certificate w -> w' iff at most one
                atom of w meets S_w';
       world 1: zero (Z_w, 1), Z_w a maximal h-zero subset of top_w, atoms (e_u, 1); certificate w -> w' iff
                |S_w \\ Z_w'| <= 1;
     a game is WON if every pair of sets has a certificate in one direction;
  2. KILL TEST of Theorems G0 / G1: for a won game the chosen lifted test systems are checked on the actual circuit:
     valid (Lean LTSValid), every class has exactly |S_w| - 1 gates, classes pairwise disjoint;
  3. LP (HiGHS): t* = min over fractional choices of the max gate load, over the menu
     norm (all world-0 / world-1 normal systems) + world + ext (global_price.py); t* <= 1 certifies the lifted price
     inequality for EVERY price (the menu is a sub-menu of Lean's liftMenu); and the real-merge-set t* for comparison.
  4. for n <= umax: the exact U-GAME (ugame.py) on the circuit's own lifted outputs and on the DD-normal outputs of
     (sets, h); a winning selection is checked on the circuit as in 2.
Usage: python3 -I lift_price.py ROOT_OR_FILES... [--nmax 9] [--umax 6] [--lp] [--v]
"""
import sys, os, itertools, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import global_price as GP, ugame

CAP = 4000

def minterms(h, n):
    P = 1 << n
    return [x for x in range(P) if h[x] and not any(h[x & ~(1 << v)] for v in range(n) if x >> v & 1)]

def maxzeros(h, n, inside):
    """maximal Z within the mask `inside` with h(Z) = 0"""
    out = []
    sub = inside
    cands = []
    while True:
        if not h[sub]: cands.append(sub)
        if sub == 0: break
        sub = (sub - 1) & inside
    for z in cands:
        if not any((z | 1 << v) != z and (inside >> v) & 1 and not h[z | 1 << v] for v in range(n)): out.append(z)
    return out

def game1(n, S, h):
    """world-1 game.  Returns {w: Z_w} or None."""
    full = (1 << n) - 1; m = len(S); Sm = [sum(1 << u for u in R) for R in S]
    opts = []
    for w in range(m):
        o = {}
        for Z in maxzeros(h, n, full & ~Sm[w]):
            In = frozenset(v for v in range(m) if v != w and bin(Sm[v] & ~Z).count('1') <= 1)
            if not any(In < J for J in o.values()): o[Z] = In
        if not o: return None
        opts.append(o)
    return tournament(m, opts, into=True)

def game0(n, S, h, mt):
    """world-0 game.  Returns {w: {u: A_u}} or None."""
    m = len(S); Sm = [sum(1 << u for u in R) for R in S]
    opts = []
    for w in range(m):
        per = []
        for u in S[w]:
            c = {}
            for mu in mt:
                if mu & Sm[w] & ~(1 << u): continue
                A = mu | 1 << u
                H = frozenset(v for v in range(m) if v != w and A & Sm[v])
                if not any(H2 <= H for H2 in c.values()):
                    c = {a: h2 for a, h2 in c.items() if not H <= h2}; c[A] = H
            if not c: return None
            per.append(list(c.items()))
        o = {}; cnt = 0
        for combo in itertools.product(*per):
            cnt += 1
            if cnt > CAP: break
            hit = collections.Counter(v for _, H in combo for v in H)
            Out = frozenset(v for v in range(m) if v != w and hit[v] <= 1)
            key = tuple(a for a, _ in combo)
            if not any(Out <= J for J in o.values()):
                o = {k: J for k, J in o.items() if not J <= Out}; o[key] = Out
        opts.append(o)
    r = tournament(m, opts, into=False)
    if r is None: return None
    return {w: dict(zip(S[w], r[w])) for w in range(m)}

def tournament(m, opts, into):
    """choose one option per set so that every pair {w, v} has v in rel(w) or w in rel(v)."""
    order = sorted(range(m), key=lambda w: len(opts[w]))
    ch = {}
    def rec(i):
        if i == m: return True
        w = order[i]
        for k, rel in opts[w].items():
            if all(v in rel or w in opts[v][ch[v]] for v in order[:i]):
                ch[w] = k
                if rec(i + 1): return True
                del ch[w]
        return False
    return dict(ch) if rec(0) else None

def check_systems(L, S, outs, systems):
    """systems[w] = (zeta, atoms).  Kill test: valid, |class| = d_w, pairwise disjoint."""
    cl = []
    for w, R in enumerate(S):
        zeta, atoms = systems[w]
        if not L.valid(R, outs[w], zeta, atoms): return 'INVALID'
        c = L.run(R, zeta, atoms)
        if bin(c).count('1') != len(R) - 1: return 'CARD'
        cl.append(c)
    for a, b in itertools.combinations(range(len(S)), 2):
        if cl[a] & cl[b]: return 'COLLISION'
    return 'ok'

def norm_menu(L, n, S, w, o, h, mt):
    R = S[w]; Y = 1 << n; Rm = sum(1 << u for u in R); top = ((1 << n) - 1) & ~Rm
    cls = set()
    for Z in maxzeros(h, n, top):
        zeta = Z | Y; atoms = [(1 << u) | Y for u in R]
        if L.valid(R, o, zeta, atoms): cls.add(L.run(R, zeta, atoms))
    per = []
    for u in R:
        c = sorted({mu | 1 << u for mu in mt if not mu & Rm & ~(1 << u)})
        c = [a for a in c if not any(b != a and b & a == b for b in c)]
        per.append(c)
    if all(per):
        cnt = 0
        for combo in itertools.product(*per):
            cnt += 1
            if cnt > CAP: break
            if L.valid(R, o, top, list(combo)): cls.add(L.run(R, top, list(combo)))
    return cls

def main():
    args = sys.argv[1:]
    def opt(name, default):
        if name in args:
            i = args.index(name); v = args[i + 1]; del args[i:i + 2]; return v
        return default
    NMAX = int(opt('--nmax', 9)); UMAX = int(opt('--umax', 6)); LPF = '--lp' in args; V = '--v' in args
    args = [a for a in args if a not in ('--lp', '--v')]
    st = collections.Counter(); worst = []
    for name, n, S, G, outs in GP.load(args):
        if n > NMAX or sum(1 for g in G if g[0] == 'not') != 1 or any(len(R) < 2 for R in S) or len(S) < 1: continue
        if any(len(set(a) & set(b)) > 1 for a, b in itertools.combinations(S, 2)): continue
        try: L = GP.Lift(n, G, outs)
        except Exception: continue
        if not L.real_ok(S): st['incorrect'] += 1; continue
        st['circuits'] += 1
        h = L.h; mt = minterms(h, n); Y = 1 << n; full = (1 << n) - 1
        rec = {'name': name, 'n': n, 's': len(G), 'base': sum(len(R) - 1 for R in S)}
        g1 = game1(n, S, h); g0 = game0(n, S, h, mt)
        rec['game1'] = g1 is not None; rec['game0'] = g0 is not None
        if g1 is not None:
            r = check_systems(L, S, outs, [(g1[w] | Y, [(1 << u) | Y for u in R]) for w, R in enumerate(S)])
            st['G1 won'] += 1; st['G1 check ' + r] += 1
        if g0 is not None:
            r = check_systems(L, S, outs, [(full & ~sum(1 << u for u in R), [g0[w][u] for u in R]) for w, R in enumerate(S)])
            st['G0 won'] += 1; st['G0 check ' + r] += 1
        if g1 is None and g0 is None: st['both pure games lost'] += 1
        if n <= UMAX:
            # exact U-game on the ACTUAL lifted outputs of this circuit, and kill test of Theorem G
            N1 = n + 1; O = [[L.val(o, x) for x in range(1 << N1)] for o in outs]
            sol = ugame.solve(N1, S, O)
            rec['ugame'] = sol is not None; st['U-game (actual outputs) won'] += sol is not None; st['U-game run'] += 1
            if sol is not None:
                st['U-game check ' + check_systems(L, S, outs, [(sol[w][0], list(sol[w][1])) for w in range(len(S))])] += 1
            dd = ugame.solve(N1, S, ugame.dd_outputs(n, S, h)) is not None
            rec['ugame_dd'] = dd; st['U-game (DD-normal outputs) won'] += dd
            if dd and sol is None: st['DD won but actual lost (must be 0)'] += 1
        if LPF:
            menus = []
            for w, (R, o) in enumerate(zip(S, outs)):
                M = norm_menu(L, n, S, w, o, h, mt) | L.menu(R, o, ['world', 'ext'], 3)
                menus.append(M)
            t, pi = GP.lp_load(menus, len(L.gw)); rec['t_lift'] = round(t, 6)
            st['lift t*<=1'] += t <= 1 + 1e-7; st['lift t*>1 (sub-menu)'] += t > 1 + 1e-7
            tr, _ = GP.lp_load([L.menu(R, o, ['real']) for R, o in zip(S, outs)], len(L.gw)); rec['t_real'] = round(tr, 6)
            st['real t*>1'] += tr > 1 + 1e-7
            worst.append((t, name))
        if V or (LPF and (rec['t_lift'] > 1 + 1e-7 or rec['t_real'] > 1 + 1e-7)):
            print(json.dumps(rec), flush=True)
    print('STATS', dict(sorted(st.items())))
    if worst: print('max lifted t*', sorted(worst, reverse=True)[:3])

if __name__ == '__main__':
    main()
