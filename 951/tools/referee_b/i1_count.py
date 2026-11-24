"""Count distinct pure classes per set (coord 11:46). Discovery only. Same definitions as puresdr_check.py.

Per set w: (a) distinct I1 classes over D-maximal Z (Z maximal with Z ∩ S_w = ∅, h(Z) = 0), atoms e_u;
(b) distinct I1 classes over Lean's wider validity (every Z with Z ∩ S_w = ∅, h(Z) = 0);
(c) distinct pure classes = (b) ∪ I0 classes (all tuples of minimal m_u).
Speed-up: in world 1 the trace of a gate {u : g(e_u) = 1} does not depend on Z, so the I1 class at Z depends only on which
gates with |trace| >= 2 are 0 at Z; Z is grouped by that pattern (numpy over all 2^n points), one union-find per pattern.
Usage: python3 -I i1_count.py files... --out result.json
"""
import json, sys
from collections import Counter
import numpy as np
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import puresdr_check as P


def tables_np(c, y):
    """Wire values of C_y on all 2^n points, as numpy uint8 arrays."""
    n, Pn = c.n, 1 << c.n
    idx = np.arange(Pn, dtype=np.int64)
    W = [((idx >> i) & 1).astype(np.uint8) for i in range(n)]
    for g in c.gates:
        if g[0] == "not":
            W.append(np.full(Pn, y, dtype=np.uint8))
        elif g[0] == "and":
            W.append(W[g[1]] & W[g[2]])
        else:
            W.append(W[g[1]] | W[g[2]])
    return W


def classes_for_pattern(c, R, gates_rel, traces, zero_bits):
    lab = {u: u for u in R}
    M = []
    for j, i in enumerate(gates_rel):
        if not zero_bits[j]:
            continue
        tr = {lab[u] for u in traces[j]}
        if len(tr) >= 2:
            M.append(i)
            r = min(tr)
            for u in R:
                if lab[u] in tr:
                    lab[u] = r
    return frozenset(M)


def per_set(c, Treal, W1):
    n, Pn = c.n, 1 << c.n
    h = Treal[c.gates[c.p][1]]
    hv = np.array([(h >> x) & 1 for x in range(Pn)], dtype=np.uint8)
    idx = np.arange(Pn, dtype=np.int64)
    res = []
    I0menus = P.menus(c, Treal)
    for w, S in enumerate(c.sets):
        Rm = sum(1 << u for u in S)
        valid = ((idx & Rm) == 0) & (hv == 0)
        Zs = idx[valid]
        at = {u: [W1[i][1 << u] for i in range(len(W1))] for u in S}
        gates_rel, traces = [], []
        for k, g in enumerate(c.gates):
            i = n + k
            if g[0] == "not":
                continue
            tr = [u for u in S if at[u][i]]
            if len(tr) >= 2:
                gates_rel.append(i); traces.append(tr)
        # maximal Z among valid: no free bit v with Z|e_v valid
        free = [v for v in range(n) if not (Rm >> v) & 1]
        ismax = np.ones(len(Zs), dtype=bool)
        for v in free:
            ext = Zs | (1 << v)
            ismax &= ~(((Zs >> v) & 1 == 0) & (hv[ext] == 0))
        if gates_rel:
            pat = np.stack([W1[i][Zs] == 0 for i in gates_rel], axis=1)
            keys = np.packbits(pat, axis=1)
            _, first, inv = np.unique(keys, axis=0, return_index=True, return_inverse=True)
            cls_of_pat = [classes_for_pattern(c, S, gates_rel, traces, pat[f]) for f in first]
            inv = inv.reshape(-1)
            wide = {cls_of_pat[k] for k in set(inv.tolist())}
            dmax = {cls_of_pat[k] for k in set(inv[ismax].tolist())}
        else:
            wide = {frozenset()} if len(Zs) else set()
            dmax = {frozenset()} if ismax.any() else set()
        i0 = {o[3] for o in I0menus[w]["opts"] if o[0] == "I0"}
        res.append((len(dmax), len(wide), len(wide | i0), len(dmax | i0), I0menus[w]["typeA"]))
    return res


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    out = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else None
    if out in args:
        args.remove(out)
    H = {"a_dmax_I1": Counter(), "b_wide_I1": Counter(), "c_pure_wide": Counter(), "c_pure_dmax": Counter(),
         "a_dmax_I1_typeA": Counter(), "a_dmax_I1_nontypeA": Counter()}
    nc = 0; ex_multi = []
    for p in args:
        for k, d in P.items(p):
            if not isinstance(d, dict) or "gates" not in d:
                continue
            c = P.Circ(d)
            if not c.ok1 or c.n > 12:
                continue
            Treal = c.table()
            W1 = tables_np(c, 1)
            nc += 1
            for a, b, cc, cd, tA in per_set(c, Treal, W1):
                H["a_dmax_I1"][a] += 1; H["b_wide_I1"][b] += 1; H["c_pure_wide"][cc] += 1; H["c_pure_dmax"][cd] += 1
                H["a_dmax_I1_typeA" if tA else "a_dmax_I1_nontypeA"][a] += 1
                if a != 1 and len(ex_multi) < 10:
                    ex_multi.append(f"{p}#{k} dmax_I1={a}")
    r = {"circuits": nc, **{key: dict(sorted(v.items())) for key, v in H.items()},
         "examples_dmax_not_one": ex_multi}
    s = json.dumps(r, indent=1)
    if out:
        open(out, "w").write(s + "\n")
    print(s)
