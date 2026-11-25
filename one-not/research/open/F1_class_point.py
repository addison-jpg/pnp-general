"""Seat F1: exact search for the CLASS POINT LEMMA (F1_phc.md section 2) on small two-set systems.  Repo root:
  nice python3 -I one-not/research/open/F1_class_point.py
S, T with |S cap T| <= 1, each partitioned into classes.  Leaf = any set of points meeting S inside one class and T
inside one class.  Lines A o B, o in {union, intersection, A - B, B - A}, inputs leaves or earlier lines.
Question: is there a program of K = |pi_S| + |pi_T| - 3 lines (one below the bound) with S and T among its lines?
Exhaustive depth-first search over the sets of line values (points as bits).  'none' = the class point lemma holds
for that system at that K (exact); a program printed = the class point lemma is false there."""
import itertools, sys

def search(Scl, Tcl, K):
    pts = sorted({u for c in Scl + Tcl for u in c}); idx = {u: i for i, u in enumerate(pts)}
    bm = lambda c: sum(1 << idx[u] for u in c)
    S = bm([u for c in Scl for u in c]); T = bm([u for c in Tcl for u in c])
    def subs(cl):
        out = {0}
        for c in cl:
            for r in range(1, len(c) + 1):
                for x in itertools.combinations(c, r): out.add(bm(x))
        return out
    # a leaf: part in S within one class, part in T within one class (a shared point belongs to both)
    leaves = set()
    for a in subs(Scl):
        for b in subs(Tcl):
            v = a | b
            okS = any(v & S == v & bm(c) for c in Scl) or v & S == 0
            okT = any(v & T == v & bm(c) for c in Tcl) or v & T == 0
            if okS and okT: leaves.add(v)
    leaves = sorted(leaves)
    def derive(av):
        out = set()
        for a in av:
            for b in av:
                out.add(a | b); out.add(a & b); out.add(a & ~b)
        return out - set(av)
    seen = set()
    def go(lines, k):
        have = (S in lines) + (T in lines)
        if have == 2: return lines
        if k == 0 or 2 - have > k: return None
        key = (frozenset(lines), k)
        if key in seen: return None
        seen.add(key)
        new = derive(leaves + list(lines))
        if 2 - have == k: new = new & {S, T}
        for v in sorted(new, key=lambda v: (v not in (S, T), v)):
            r = go(lines + (v,), k - 1)
            if r: return r
        return None
    r = go((), K)
    return None if r is None else [[pts[i] for i in range(len(pts)) if v >> i & 1] for v in r]

if __name__ == '__main__':
    shapes = [[1, 1], [2, 1], [1, 1, 1], [2, 1, 1], [2, 2, 1], [3, 1, 1], [1, 1, 1, 1], [2, 1, 1, 1], [2, 2]]
    for sa, sb in itertools.combinations_with_replacement(shapes, 2):
        for shared in (False, True):
            K = len(sa) + len(sb) - 3
            if K < 1 or K > 4 or sum(sa) + sum(sb) > 9: continue
            it = iter(range(100))
            Scl = [[next(it) for _ in range(s)] for s in sa]
            Tcl = [[next(it) for _ in range(s)] for s in sb]
            variants = [None] if not shared else sorted({(i, j) for i in range(len(sa)) for j in range(len(sb))}, key=lambda ij: (sa[ij[0]], sb[ij[1]]))
            done = set()
            for var in variants:
                Tc = [list(c) for c in Tcl]
                if var is not None:
                    i, j = var
                    if (sa[i], sb[j]) in done: continue
                    done.add((sa[i], sb[j])); Tc[j][0] = Scl[i][0]
                r = search(Scl, Tc, K)
                print('S classes', sa, 'T classes', sb, 'shared' if shared else 'disjoint', '' if var is None else 'class sizes at the common point %d,%d' % (sa[var[0]], sb[var[1]]),
                      'K =', K, ':', 'none' if r is None else 'PROGRAM %s' % r, flush=True)
