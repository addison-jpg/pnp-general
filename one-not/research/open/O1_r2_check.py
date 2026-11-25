"""O1 (O1_r2.md): rule R2 of B9 s3.2 is false. Independent checker (not B9 needed() nor B11 indep_count) of the
cleanup count after removing private points, run on the three exact-SAT counterexamples found by
`B11_r2_sat.py r2sat`, plus PHC@0 (U1 s2.2, via U1_payment_hall.partition) on the same programs.
Run: python3 -I one-not/research/open/O1_r2_check.py
Inputs: a line is (op, A, B); op '|' union, '&' intersection, '-' A minus B, 'r' B minus A; A, B a leaf (a set) or an
earlier line index."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
OPS = {'|': lambda a, b: a | b, '&': lambda a, b: a & b, '-': lambda a, b: a - b, 'r': lambda a, b: b - a}
def run(prog, S, T, rm):
    rm = set(rm); S2, T2 = set(S) - rm, set(T) - rm
    pt = lambda v: len(v & S2) <= 1 and len(v & T2) <= 1
    vals = []
    for op, a, b in prog:
        f = lambda x: (frozenset(x) - rm) if not isinstance(x, int) else vals[x]
        vals.append(frozenset(OPS[op](f(a), f(b))))
    alias = {}
    def res(x):   # resolve an input to ('L', set) or ('X', i) after redirects
        if not isinstance(x, int): return ('L', frozenset(x) - rm)
        while x in alias:
            x = alias[x]
            if not isinstance(x, int): return ('L', x)
        return ('X', x)
    live = []
    for i, (op, a, b) in enumerate(prog):
        v = vals[i]; ra, rb = res(a), res(b)
        va = ra[1] if ra[0] == 'L' else vals[ra[1]]; vb = rb[1] if rb[0] == 'L' else vals[rb[1]]
        if pt(v): alias[i] = v; continue
        if v == va: alias[i] = ra[1]; continue
        if v == vb: alias[i] = rb[1]; continue
        e = [j for j in live if vals[j] == v]
        if e: alias[i] = e[0]; continue
        live.append(i)
    need = set(); st = []
    for tg in (S2, T2):
        if not pt(frozenset(tg)): st.append([j for j in live if vals[j] == frozenset(tg)][0])
    while st:
        i = st.pop()
        if i in need: continue
        need.add(i)
        for x in prog[i][1:]:
            r = res(x)
            if r[0] == 'X': st.append(r[1])
    return len(need)
def r2(prog, S, T):
    K = len(prog); priv = sorted((set(S) ^ set(T)))
    base = run(prog, S, T, [])
    one = {u: run(prog, S, T, [u]) for u in priv}
    two = {(a, e): run(prog, S, T, [a, e]) for a in priv if a in S for e in priv if e in T}
    ok = any(c <= K - 1 for c in one.values()) or any(c <= K - 2 for c in two.values())
    return base, K, min(one.values()), min(two.values()), 'R2 holds' if ok else 'R2 FAILS'

def values(prog):
    v = []
    for op, a, b in prog:
        f = lambda x: frozenset(x) if not isinstance(x, int) else v[x]
        v.append(frozenset(OPS[op](f(a), f(b))))
    return v

def phc0(prog, S, T):
    from U1_payment_hall import partition
    v = values(prog); pay = list(range(len(prog)))
    sets = [({u: u for u in W}, {g: [v[g] & frozenset(W)] for g in pay}) for W in (S, T)]
    return partition(pay, sets)

CEX = {
 '(4,4) disjoint, 9 lines': ([0, 1, 2, 3], [4, 5, 6, 7],
    [('|', {2, 4}, {1, 5}), ('|', {0, 7}, {3, 6}), ('|', 0, 1), ('|', {0, 4}, {3, 5}), ('|', 0, 3),
     ('|', {1, 6}, {2, 7}), ('|', 5, 1), ('&', 4, 6), ('-', 2, 7)]),
 '(3,5) disjoint, 8 lines': ([0, 1, 2], [3, 4, 5, 6, 7],
    [('|', {0, 7}, {1, 4}), ('|', {2, 3}, {1, 6}), ('|', {0, 5}, 1), ('|', 0, 2), ('r', {2, 7}, 3), ('r', 0, 4),
     ('r', 5, 2), ('r', 6, 3)]),
 '(3,5) shared, 8 lines': ([0, 1, 2], [0, 3, 4, 5, 6],
    [('|', {0}, {2, 5}), ('|', 0, {1, 6}), ('|', {0}, {2, 4}), ('|', {1, 3}, 2), ('|', 1, 3), ('&', 1, 3),
     ('r', 5, 4), ('|', {0}, 6)]),
}

if __name__ == '__main__':
    for name, (S, T, prog) in CEX.items():
        v = values(prog)
        assert frozenset(S) in v and frozenset(T) in v
        base, K, one, two, verdict = r2(prog, S, T)
        print(name, '| reduced lines', base, 'of', K, '| min after one private point', one,
              '| min after a private pair', two, '|', verdict, '| PHC@0 (ranks, holds)', phc0(prog, S, T))
