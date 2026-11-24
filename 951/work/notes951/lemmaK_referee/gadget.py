"""Referee test of scaffold's RESOLUTION-GADGET shape claim (board agents/scaffold-core-sat.md 08:25):

  "the missing 3rd+ merges of a hard 4-set are always (A | y) & (A | ~y) = A, A = the partial OR of S_w,
   y = h restricted off S_w; the y-polluted ORs pay and die under restrictions fixing y."

For every correct one-NOT circuit and every HARD set S (h(z_S) = 1) with |S| >= 4 and |Pi_w| < d_w (merges missing from
the class count of Lemma K), look in the cone of o_w for AND gates g = P & Q with T[g] = OR(T), T ⊆ S nonempty, and
both P, Q strictly above OR(T) (a resolution). Classify the set:
  strict : some such g has {P, Q} = {A | y, A | ~y} with A = OR(T) and y = h with x_S := 0 (the claim's shape);
  loose  : some such g exists, none of the strict shape;
  none   : no resolution AND gate onto a partial OR of S in the cone of o_w.
For strict gadgets, "die": some single restriction x_v := b (v outside S) makes y constant and removes P or Q
(tools/w951 Circuit.restrict, semantic).

Run from the 951/ directory (or the repository root of pequalnp-work):  python3 work/notes951/lemmaK_referee/gadget.py FILE_OR_DIR...
"""
import glob
import json
import os
import sys

sys.path.insert(0, 'tools')
from w951 import Circuit, load  # noqa: E402


def files_of(args):
    out = []
    for a in args:
        if os.path.isdir(a):
            out += sorted(glob.glob(os.path.join(a, '**', '*.json*'), recursive=True))
        else:
            out.append(a)
    return out


def circuits_of(path):
    try:
        if path.endswith('.jsonl'):
            res = []
            for line in open(path):
                line = line.strip()
                if not line.startswith('{'):
                    continue
                try:
                    res.append(Circuit.from_dict(json.loads(line)))
                except Exception:
                    pass
            return res
        return load(path) if path.endswith('.json') else []
    except Exception:
        return []


def analyse(c):
    """Yield (set index, class) for every hard set with |S| >= 4 and missing merges."""
    if len(c.nots) != 1 or not c.sets or len(c.sets) != len(c.outs):
        return
    try:
        c.validate(sums=True, one_not=True)
    except ValueError:
        return
    n, s = c.n, len(c.gates)
    T, full = c.tables(), c.full
    if any(T[o] != c.or_table(S) for S, o in zip(c.sets, c.outs)):
        return
    N = c.not_wire
    h = T[c.h_wire]
    O = [c.or_table(S) for S in c.sets]

    def leq(a, b):
        return a & ~b & full == 0

    def units(g):
        return sum(1 for u in range(n) if T[g] >> (1 << u) & 1)

    def unitset(g, S):
        return {u for u in S if T[g] >> (1 << u) & 1}

    for i, S in enumerate(c.sets):
        if len(S) < 4:
            continue
        maskS = sum(1 << u for u in S)
        zS = ((1 << n) - 1) & ~maskS
        if not (h >> zS & 1):
            continue                                    # easy set
        D = {g for g in range(n, n + s) if leq(T[g], O[i]) and len(unitset(g, S)) >= 2}
        P = {g for g in range(n, n + s) if leq(O[i], T[g]) and T[g] != full
             and all(not leq(O[j], T[g]) for j in range(len(c.sets)) if j != i)}
        if len(D | P) >= len(S) - 1:
            continue                                    # no merge missing
        # y = h with x_S := 0, as a table
        y = 0
        for pt in range(1 << n):
            if h >> (pt & ~maskS) & 1:
                y |= 1 << pt
        cone = c.cone(c.outs[i])
        found_strict, found_loose, dies = False, False, False
        for g in cone:
            if g < n or c.gates[g - n][0] != 'and':
                continue
            Tset = [u for u in range(n) if T[g] >> (1 << u) & 1]
            if not Tset or not set(Tset) <= set(S) or T[g] != c.or_table(Tset):
                continue
            a, b = c.gates[g - n][1:]
            if T[a] == T[g] or T[b] == T[g]:
                continue                                # not a resolution
            A = T[g]
            if {T[a], T[b]} == {A | y, A | (full & ~y)}:
                found_strict = True
                for v in range(n):
                    if v in S:
                        continue
                    for bit in (0, 1):
                        sub = [pt for pt in range(1 << n) if (pt >> v & 1) == bit]
                        vals = {y >> pt & 1 for pt in sub}
                        if len(vals) == 1:
                            r = c.restrict(v, bit)
                            gone = set(r.detail.get('const', [])) | set(r.detail.get('merged', [])) | \
                                set(r.detail.get('dead', []))
                            if a in gone or b in gone:
                                dies = True
            else:
                found_loose = True
        cls = 'strict' if found_strict else ('loose' if found_loose else 'none')
        yield i, cls, dies, len(D | P), len(S), s - sum(len(S2) - 1 for S2 in c.sets)


def main():
    stats = {'strict': 0, 'loose': 0, 'none': 0, 'strict_dies': 0, 'circuits': 0}
    minex = {'strict': None, 'loose': None, 'none': None}
    examples = {'loose': [], 'none': []}
    for f in files_of(sys.argv[1:]):
        for k, c in enumerate(circuits_of(f)):
            stats['circuits'] += 1
            for i, cls, dies, npi, size, excess in analyse(c):
                stats[cls] += 1
                if minex[cls] is None or excess < minex[cls]:
                    minex[cls] = excess
                stats['strict_dies'] += cls == 'strict' and dies
                if cls in examples and len(examples[cls]) < 3:
                    examples[cls].append({'file': f, 'index': k, 'set': i, 'size': size, 'Pi': npi, 's-base': excess,
                                          'circuit': c.to_dict()})
    print(json.dumps(stats), 'min s-base per class:', json.dumps(minex))
    for cls, ex in examples.items():
        for e in ex:
            print(cls.upper(), json.dumps(e))


if __name__ == '__main__':
    main()
