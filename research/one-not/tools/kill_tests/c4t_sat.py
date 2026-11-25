# C4(t) SAT search (README C4(t), D9). Exact synthesis of a circuit of fan-in-2 AND / OR gates and
# fan-in-1 NOT gates (every gate counts) computing OR(S_w) for every set w, with exactly s gates and
# at most t NOT gates. SAT at s < base refutes C4(t); UNSAT at s = base - 1 is 'tested' evidence.
# Every found circuit is re-verified by brute force on all 2^n inputs, and its general witness count
# |witness(emptyset)| (D9: g(Z)=0, g(Z+e_u)=g(Z+e_u')=1, Z avoiding S_w, u != u' in S_w) is reported.
# Run: python3 -I research/one-not/tools/kill_tests/c4t_sat.py SYSTEM s t [--exact-not] [--no-nn] [--sb] [--wbelow] [--fclasses F (at most F flip classes; F = base-1 tests S3(b))] [--enum K] [--out FILE]
import sys, json, itertools, time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

SYSTEMS = {
    'tri3':   (6, [(0, 1, 3), (1, 2, 4), (0, 2, 5)]),            # triangle, lines of size 3, base 6
    'pasch':  (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]),  # Pasch, base 8
    'star3':  (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6)]),             # star of 3 triples, base 6
    'k4tri':  (7, [(0, 1, 4), (0, 2, 5), (0, 3, 6), (1, 2, 6), (1, 3, 5), (2, 3, 4)]),  # (1,1)-disjoint, base 12
    'fano':   (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]),  # base 14
    'tri4':   (6, [(0, 1, 3, 4), (1, 2, 5), (0, 2)]),             # mixed sizes, base 6
    'fano6':  (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6)]),  # Fano minus a line, base 12
    'fano5':  (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6)]),  # base 10
    'fano4':  (7, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]),  # = Pasch on 6 pts inside Fano (n=7 w/ idle pt)
    'q4':     (6, [(0, 1, 2, 3), (0, 4, 5), (1, 4), (2, 5)]),     # base 7
    'two3':   (5, [(0, 1, 2), (0, 3, 4)]),                        # two triples, base 4
    'star44': (7, [(0, 1, 2, 3), (0, 4, 5, 6)]),                  # base 6; the system of general_count_below_base_min (t = 4)
    'star333':(7, [(0, 1, 2), (0, 3, 4), (0, 5, 6)]),             # = star3
    'tri44':  (9, [(0, 1, 3, 4), (1, 2, 5, 6), (0, 2, 7, 8)]),    # base 9
    'ag23':   (9, [(0, 1, 2), (3, 4, 5), (6, 7, 8), (0, 3, 6), (1, 4, 7), (2, 5, 8),
                   (0, 4, 8), (1, 5, 6), (2, 3, 7), (0, 5, 7), (1, 3, 8), (2, 4, 6)]),  # base 24
}

def build(n, sets, s, t, exact_not=False, no_nn=False, sb=False, wbelow=False, fbelow=None):
    N = 1 << n; nodes = n + s
    vid = [0]
    def new():
        vid[0] += 1; return vid[0]
    cl = []
    val = [[None] * N for _ in range(nodes)]
    for i in range(n):
        for r in range(N): val[i][r] = (r >> i) & 1  # constants (python bools)
    for k in range(s):
        for r in range(N): val[n + k][r] = new()
    typ = [{c: new() for c in ('and', 'or', 'not')} for _ in range(s)]
    sel = []
    for k in range(s):
        g = n + k
        d = {}
        for i in range(g):
            for j in range(i + 1, g): d[(i, j)] = new()
        dn = {i: new() for i in range(g)}  # NOT input
        sel.append((d, dn))
        T = typ[k]
        cl.append([T['and'], T['or'], T['not']])
        for a, b in itertools.combinations(T.values(), 2): cl.append([-a, -b])
        # exactly one pair if AND/OR; exactly one NOT input if NOT
        cl.append([-T['not']] + list(dn.values()))
        cl.append([T['not']] + list(d.values()))
        for x in d.values(): cl.append([-T['not'], -x])
        for x in dn.values(): cl.append([T['not'], -x])
        for a, b in itertools.combinations(list(d.values()), 2): cl.append([-a, -b])
        for a, b in itertools.combinations(list(dn.values()), 2): cl.append([-a, -b])
    def lit(node, r):
        v = val[node][r]
        return v
    # semantics
    for k in range(s):
        g = n + k; d, dn = sel[k]; T = typ[k]
        for r in range(N):
            o = val[g][r]
            for (i, j), x in d.items():
                a, b = lit(i, r), lit(j, r)
                # AND: o <-> a & b ; OR: o <-> a | b   (a,b may be constants 0/1)
                for op in ('and', 'or'):
                    pre = [-x, -T[op]]
                    def C(*ls):
                        c = list(pre)
                        for l in ls:
                            if l is True or l == 'T': return
                            if l is False or l == 'F': continue
                            c.append(l)
                        cl.append(c)
                    def L(v, pos):  # literal for "v is pos"
                        if isinstance(v, int) and v in (0, 1) and (i < n or j < n) and v is not None and not isinstance(v, bool) and False: pass
                        return v
                    A = ('T' if a == 1 else 'F') if i < n else None
                    B = ('T' if b == 1 else 'F') if j < n else None
                    def pl(node, c, pos):  # positive literal of node value, or constant
                        if node < n:
                            v = c
                            return ('T' if v == 1 else 'F') if pos else ('F' if v == 1 else 'T')
                        return c if pos else -c
                    if op == 'and':
                        C(-o, pl(i, a, True)) if True else None
                        C(-o, pl(j, b, True))
                        C(o, pl(i, a, False), pl(j, b, False))
                    else:
                        C(o, pl(i, a, False))
                        C(o, pl(j, b, False))
                        C(-o, pl(i, a, True), pl(j, b, True))
            for i, x in dn.items():
                pre = [-x, -T['not']]
                if i < n:
                    c = val[i][r]
                    cl.append(pre + ([-o] if c == 1 else [o]))
                else:
                    a = val[i][r]
                    cl.append(pre + [o, a]); cl.append(pre + [-o, -a])
    # NOT budget
    nots = [typ[k]['not'] for k in range(s)]
    enc = (CardEnc.equals if exact_not else CardEnc.atmost)(lits=nots, bound=t, top_id=vid[0], encoding=EncType.seqcounter)
    vid[0] = max(vid[0], enc.nv); cl += enc.clauses
    # outputs
    outv = []
    for w, R in enumerate(sets):
        m = sum(1 << u for u in R)
        ov = {k: new() for k in range(s)}
        outv.append(ov)
        cl.append(list(ov.values()))
        for k, x in ov.items():
            for r in range(N):
                tv = 1 if r & m else 0
                cl.append([-x, val[n + k][r] if tv else -val[n + k][r]])
    # every gate used (as an input or an output): otherwise a smaller circuit exists
    for k in range(s):
        g = n + k; users = []
        for k2 in range(k + 1, s):
            d, dn = sel[k2]
            users += [x for (i, j), x in d.items() if g in (i, j)]
            if g in dn: users.append(dn[g])
        users += [outv[w][k] for w in range(len(sets))]
        cl.append(users)
    if sb:  # co-lexicographic gate order: if gate k+1 does not read gate k, its input key is not below gate k's
        def keys(k):
            d, dn = sel[k]
            return [((j, i), x) for (i, j), x in d.items()] + [((i, i), x) for i, x in dn.items()]
        for k in range(s - 1):
            g = n + k; A = keys(k); B = keys(k + 1)
            for kb, xb in B:
                if g in kb: continue
                for ka, xa in A:
                    if kb < ka: cl.append([-xa, -xb])
    if wbelow:  # D9 witness count <= base - 1: at least s - base + 1 gates are NOT witnesses
        N = 1 << n; nw = []
        for k in range(s):
            x = new(); nw.append(x); g = n + k
            for R in sets:
                m = sum(1 << u for u in R)
                for Z in range(N):
                    if Z & m: continue
                    for u, u2 in itertools.combinations(R, 2):
                        cl.append([-x, val[g][Z], -val[g][Z | 1 << u], -val[g][Z | 1 << u2]])
        base = sum(len(R) - 1 for R in sets)
        if s - base + 1 > 0:
            enc = CardEnc.atleast(lits=nw, bound=s - base + 1, top_id=vid[0], encoding=EncType.seqcounter)
            vid[0] = max(vid[0], enc.nv); cl += enc.clauses
    if fbelow is not None:  # S3(b) FlipClasses.count: at most fbelow flip classes (flip: g(Z+e_u) != g(Z) at two atoms u of a set,
        # Z a zero point; class: function up to complement). A gate is 'free' if it is not a flip gate (nf) or equals / complements an
        # earlier gate (dup); flip classes = s - #free when free is chosen maximally, so require #free >= s - fbelow.
        N = 1 << n; free = []
        for k in range(s):
            g = n + k; nf = new()
            for R in sets:
                m = sum(1 << u for u in R)
                for Z in range(N):
                    if Z & m: continue
                    for u, u2 in itertools.combinations(R, 2):
                        a, b, c = val[g][Z], val[g][Z | 1 << u], val[g][Z | 1 << u2]
                        cl.append([-nf, -a, b, c]); cl.append([-nf, a, -b, -c])
            dups = []
            for j in range(n + k):  # inputs are never flip gates, so j < n is never needed; keep j >= n
                if j < n: continue
                for comp in (0, 1):
                    x = new(); dups.append(x)
                    for r in range(N):
                        A, B = val[g][r], val[j][r]
                        if comp: cl.append([-x, A, B]); cl.append([-x, -A, -B])
                        else: cl.append([-x, -A, B]); cl.append([-x, A, -B])
            fr = new(); cl.append([-fr, nf] + dups); free.append(fr)
        if s - fbelow > 0:
            enc = CardEnc.atleast(lits=free, bound=s - fbelow, top_id=vid[0], encoding=EncType.seqcounter)
            vid[0] = max(vid[0], enc.nv); cl += enc.clauses
    if no_nn:  # no NOT gate reads a NOT gate (removes trivial double negation)
        for k in range(s):
            d, dn = sel[k]
            for i, x in dn.items():
                if i >= n: cl.append([-x, -typ[i - n]['not']])
    return cl, typ, sel, outv, vid

def decode(model, n, s, typ, sel, outv):
    m = set(x for x in model if x > 0)
    G = []
    for k in range(s):
        d, dn = sel[k]; T = typ[k]
        if T['not'] in m: G.append(['not', next(i for i, x in dn.items() if x in m)])
        else:
            op = 'and' if T['and'] in m else 'or'
            i, j = next(p for p, x in d.items() if x in m); G.append([op, i, j])
    outs = [n + next(k for k, x in ov.items() if x in m) for ov in outv]
    return G, outs

sys.path.insert(0, 'research/one-not/tools/kill_tests')

def tables(n, G):
    N = 1 << n; M = (1 << N) - 1; w = []
    for i in range(n):
        w.append(sum(1 << x for x in range(N) if x >> i & 1))
    for g in G:
        w.append(M ^ w[g[1]] if g[0] == 'not' else (w[g[1]] & w[g[2]] if g[0] == 'and' else w[g[1]] | w[g[2]]))
    return w

def correct(n, S, G, outs):
    w = tables(n, G)
    return all(w[o] == (lambda t: t)(eval_or(w, R)) for R, o in zip(S, outs))

def eval_or(w, R):
    t = 0
    for u in R: t |= w[u]
    return t

def witness(n, S, G):
    w = tables(n, G); out = set()
    for k in range(len(G)):
        t = w[n + k]; hit = False
        for R in S:
            rest = [v for v in range(n) if v not in R]
            for r in range(len(rest) + 1):
                for Zs in itertools.combinations(rest, r):
                    Z = sum(1 << v for v in Zs)
                    if t >> Z & 1: continue
                    if sum(t >> (Z | 1 << u) & 1 for u in R) >= 2: hit = True; break
                if hit: break
            if hit: break
        if hit: out.add(k)
    return out

def flip_classes(n, S, G):  # brute force, same definition as research/one-not/tools/search/conjectures.py count_flip_classes
    w = tables(n, G); M = (1 << (1 << n)) - 1; cls = set()
    for k in range(len(G)):
        t = w[n + k]; hit = False
        for R in S:
            m = sum(1 << u for u in R)
            for Z in range(1 << n):
                if Z & m: continue
                b = t >> Z & 1
                if sum((t >> (Z | 1 << u) & 1) != b for u in R) >= 2: hit = True; break
            if hit: break
        if hit: cls.add(min(t, M ^ t))
    return len(cls)

def essential_nots(n, S, G, outs):
    # a NOT gate is essential if replacing it by each input / constant breaks correctness is too strong;
    # report simply whether the circuit with every NOT gate replaced by identity is still correct.
    return None

if __name__ == '__main__':
    name, s, t = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    exact = '--exact-not' in sys.argv
    K = int(sys.argv[sys.argv.index('--enum') + 1]) if '--enum' in sys.argv else 1
    outf = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None
    n, S = SYSTEMS[name]
    base = sum(len(R) - 1 for R in S)
    t0 = time.time()
    cl, typ, sel, outv, vid = build(n, S, s, t, exact, '--no-nn' in sys.argv, '--sb' in sys.argv, '--wbelow' in sys.argv,
                                     (int(sys.argv[sys.argv.index('--fclasses') + 1]) if '--fclasses' in sys.argv else None))
    sol = Solver(name='cadical153', bootstrap_with=cl)
    found = []
    while len(found) < K:
        ok = sol.solve()
        if not ok: break
        model = sol.get_model()
        G, outs = decode(model, n, s, typ, sel, outv)
        assert correct(n, S, G, outs), 'decoded circuit incorrect'
        nn = sum(g[0] == 'not' for g in G)
        wc = len(witness(n, S, G)); fc = flip_classes(n, S, G)
        found.append({'gates': G, 'outs': outs, 'nots': nn, 'witness': wc, 'flip_classes': fc})
        print(f"{name} n={n} base={base} s={s} t<={t}: SAT  nots={nn} witness={wc} {'>=base' if wc >= base else '<BASE'} flipclasses={fc} {'>=base' if fc >= base else '<BASE'}  {G} outs={outs}", flush=True)
        # block this exact gate list
        msk = set(x for x in model if x > 0)
        blk = []
        for k in range(s):
            d, dn = sel[k]; T = typ[k]
            blk += [-x for x in list(T.values()) + list(d.values()) + list(dn.values()) if x in msk]
        sol.add_clause(blk)
    if not found:
        print(f"{name} n={n} base={base} s={s} t<={t}{' (exact)' if exact else ''}: UNSAT  ({time.time() - t0:.1f}s, {len(cl)} clauses)", flush=True)
    else:
        print(f"{name}: {len(found)} circuits ({time.time() - t0:.1f}s)")
    if outf and found:
        json.dump({'n': n, 'sets': [list(R) for R in S], 'base': base, 's': s, 't': t, 'circuits': found}, open(outf, 'w'))
