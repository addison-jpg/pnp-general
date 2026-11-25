# Occurrence-substitution test for L-meta-951 (helper tooling, not a proof).
# For a correct circuit with one live NOT (gate p): can every READ of the NOT's wire be replaced by a constant
# (level 0), or a constant / earlier monotone wire (level 1), so that all outputs stay correct and no NOT is read?
import sys, time, itertools, random, collections
sys.path.insert(0, 'research/tools/l951_charging'); import live951
from pysat.solvers import Cadical153
build, decode = live951.build_live, live951.decode
SYSTEMS = [(5, [(0, 1, 2), (0, 3, 4)]), (5, [(0, 1, 2), (2, 3), (3, 4, 0)]), (6, [(0, 1), (2, 3), (4, 5), (0, 2, 4)]),
           (6, [(0, 1, 2), (3, 4, 5), (0, 3)]), (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]),
           (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]), (7, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 6), (5, 6)]),
           (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (2, 4)]), (6, [(0, 1, 2), (0, 3, 4), (1, 3), (2, 4), (5, 0)]),
           (7, [(0, 1), (0, 2), (1, 3), (2, 3), (4, 5, 6), (3, 4)]), (7, [(0, 1, 2, 3), (0, 4), (1, 5), (2, 6), (4, 5, 6)])]
def evalc(n, gates, outs, x, sub):
    # sub: dict (gate index k, slot) -> ('c', bool) or ('w', wire); applies to reads of the NOT wire
    w = list(x)
    for k, (op, a, b) in enumerate(gates):
        def rd(slot, j):
            s = sub.get((k, slot))
            if s is None: return w[j]
            return s[1] if s[0] == 'c' else w[s[1]]
        if op == 'not': w.append(not w[a])
        elif op == 'and': w.append(rd(0, a) and rd(1, b))
        else: w.append(rd(0, a) or rd(1, b))
    return [w[o] for o in outs]
def correct(n, sets, gates, outs, sub):
    for m in range(2 ** n):
        x = [(m >> i) & 1 == 1 for i in range(n)]
        if evalc(n, gates, outs, x, sub) != [any(x[v] for v in S) for S in sets]: return False
    return True
def test(n, sets, gates, outs, p):
    nw = n + p
    occ = [(k, s) for k, (op, a, b) in enumerate(gates) if op != 'not' for s, j in ((0, a), (1, b)) if j == nw]
    assert nw not in outs or True
    if nw in outs: return 'out', occ
    for choice in itertools.product([False, True], repeat=len(occ)):
        if correct(n, sets, gates, outs, {o: ('c', c) for o, c in zip(occ, choice)}):
            return ('all0' if not any(choice) else 'all1' if all(choice) else 'mixed'), occ
    # level 1: constants or earlier wires that do not depend on the NOT
    dep = [False] * (n + len(gates))
    for k, (op, a, b) in enumerate(gates):
        dep[n + k] = (k == p) or dep[a] or (op != 'not' and dep[b])
    opts = {o: [('c', False), ('c', True)] + [('w', j) for j in range(n + o[0]) if not dep[j]] for o in occ}
    for choice in itertools.product(*[opts[o] for o in occ]):
        if correct(n, sets, gates, outs, dict(zip(occ, choice))): return 'wire', occ
    return 'FAIL', occ
idx = int(sys.argv[1]); extra = [int(a) for a in sys.argv[2].split(',')]; CAP = int(sys.argv[3]); SECS = float(sys.argv[4])
n, sets = SYSTEMS[idx]; base = sum(len(S) - 1 for S in sets)
for ex in extra:
    s = base + ex; hist = collections.Counter(); t0 = time.time(); fails = []
    for p in range(1, s - 1):
        cl, SEL, O = build(n, sets, s, p, [])
        cl = cl + [[SEL[p][0][w] for w in range(n, n + p)]]  # hgate: the NOT reads a gate, not an input
        sol = Cadical153(bootstrap_with=cl); found = 0
        rng = random.Random(p * 7919 + s); vs = list(range(1, sol.nof_vars() + 1)); sol.set_phases([v if rng.random() < .5 else -v for v in vs])
        while found < CAP and time.time() - t0 < SECS and sol.solve():
            M = sol.get_model(); gates, outs = decode(M, n, s, p, SEL, O)
            if not correct(n, sets, gates, outs, {}): hist['GENERATOR_WRONG'] += 1
            else:
                r, occ = test(n, sets, gates, outs, p); hist[r] += 1
                if r in ('FAIL', 'wire') and len(fails) < 3: fails.append((gates, outs, p))
            found += 1
            pos = set(l for l in M if l > 0)
            block = [-SEL[k][0][gates[k][1]] for k in range(s)]
            block += [-SEL[k][1][gates[k][2]] for k in range(s) if k != p]
            block += [(-SEL[k][2] if SEL[k][2] in pos else SEL[k][2]) for k in range(s) if k != p]
            block += [-O[i][outs[i]] for i in range(len(sets))]
            sol.add_clause(block)
        sol.delete()
    print('sys', idx, 'size base+%d' % ex, dict(hist), 'sec', round(time.time() - t0), flush=True)
    for f in fails: print('  FAIL', f, flush=True)
