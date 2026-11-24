#!/usr/bin/env python3
"""Independent checker (no imports from w951 code). Light CPU, single process."""
import json, glob, sys, os

def tables(c, force=None):
    n = c["n"]; N = 1 << n; FULL = (1 << N) - 1
    w = []
    for i in range(n):
        t = 0
        for x in range(N):
            if (x >> i) & 1: t |= 1 << x
        w.append(t)
    for g in c["gates"]:
        if g[0] == "not":
            v = (~w[g[1]]) & FULL
            if force is not None: v = FULL if force else 0
        elif g[0] == "and": v = w[g[1]] & w[g[2]]
        elif g[0] == "or": v = w[g[1]] | w[g[2]]
        else: raise ValueError(g)
        w.append(v)
    return w

def bit(t, x): return (t >> x) & 1

def mask(S): return sum(1 << i for i in S)

def correct(c, force=None):
    n = c["n"]; w = tables(c, force)
    for S, o in zip(c["sets"], c["outs"]):
        m = mask(S)
        for x in range(1 << n):
            if bit(w[o], x) != (1 if x & m else 0): return False
    return True

def not_info(c):
    nots = [k for k, g in enumerate(c["gates"]) if g[0] == "not"]
    assert len(nots) == 1, "NOT count %d" % len(nots)
    return nots[0], c["gates"][nots[0]][1]

def essential(c):
    return (not correct(c, 0)) and (not correct(c, 1))

def zero_points(n, S):
    m = mask(S)
    return [z for z in range(1 << n) if z & m == 0]

def merge_set(c, w, S, z, flags):
    n = c["n"]
    par = {u: u for u in S}
    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    M = []
    for i in range(n, len(w)):
        if bit(w[i], z): continue
        B = [u for u in S if bit(w[i], z | (1 << u))]
        blocks = {find(u) for u in B}
        if len(blocks) >= 2:
            if len(blocks) >= 3: flags.append((i, len(blocks), z))
            r = blocks.pop()
            for b in blocks: par[b] = r
            M.append(i)
    return frozenset(M)

def score(c):
    w = tables(c); n = c["n"]
    A, B = c["sets"][0], c["sets"][1]
    flags = []
    MA = [merge_set(c, w, A, z, flags) for z in zero_points(n, A)]
    MB = [merge_set(c, w, B, z, flags) for z in zero_points(n, B)]
    d = sum(1 for a in MA for b in MB if not (a & b))
    return d, len(MA) * len(MB), flags

def o2_half(c, w, h, A, B):
    n = c["n"]; mA, mB = mask(A), mask(B)
    for z in range(1 << n):
        if z & mB: continue
        if sum(1 for u in A if not (z >> u) & 1) > 1: continue
        if bit(w[h], z) != 1: return False
        if bit(w[h], z & ~mA) != 0: return False
    return True

def O2(c):
    w = tables(c); _, h = not_info(c)
    A, B = c["sets"][0], c["sets"][1]
    return o2_half(c, w, h, A, B) and o2_half(c, w, h, B, A)

def restrict(c, keep):
    """keep: list of set indices. Prune unreachable gates, renumber."""
    n = c["n"]; outs = [c["outs"][k] for k in keep]; sets = [c["sets"][k] for k in keep]
    need = set(); st = list(outs)
    while st:
        x = st.pop()
        if x < n or x in need: continue
        need.add(x)
        g = c["gates"][x - n]
        st.extend(g[1:])
    mp = {i: i for i in range(n)}; gates = []
    for k, g in enumerate(c["gates"]):
        if n + k in need:
            mp[n + k] = n + len(gates)
            gates.append([g[0]] + [mp[a] for a in g[1:]])
    return {"n": n, "sets": sets, "gates": gates, "outs": [mp[o] for o in outs]}

def full(c):
    d, t, fl = score(c)
    return dict(correct=correct(c), O2=O2(c), ess=essential(c), d=d, t=t, fl=fl)

def main():
    base = "/home/user/pnp-general/951/research/front612/o2pair/"
    out = []
    P = out.append
    corp = "/home/user/pequalnp-proofs/research/front/no_minCE/supportB/corpora/w9/"
    a = json.load(open(corp + "fb__cfgI.json"))
    b = json.load(open(corp + "fc__cxT2.json"))
    sa = restrict(a, [0, 1])
    want = [{1, 2, 7, 8}, {0, 2, 3, 4}]
    idx = []
    for W in want:
        idx.append(next(k for k, S in enumerate(b["sets"]) if set(S) == W))
    sb = restrict(b, idx)
    P("== Task 1: start circuits (climber: cfgI 960/1024 O2 True; cxT2 547/1024 O2 True) ==")
    for name, c in (("cfgI", sa), ("cxT2", sb)):
        r = full(c)
        sw = dict(c); sw["sets"] = c["sets"][::-1]; sw["outs"] = c["outs"][::-1]
        r2 = full(sw)
        P("%s sets=%s gates=%d correct=%s O2=%s essential=%s score=%d/%d (swapped order: %d/%d O2=%s) >=3-block=%s"
          % (name, c["sets"], len(c["gates"]), r["correct"], r["O2"], r["ess"], r["d"], r["t"], r2["d"], r2["t"], r2["O2"], r["fl"]))
    P("")
    P("== Task 2: climber records ==")
    P("file:line | claimed disj/pairs ess | mine disj/pairs correct O2 ess | status")
    seen = {}
    mism = 0; total = 0; low = None; flags_all = []
    def passes():
        nonlocal mism, total, low
        for f in sorted(glob.glob(base + "climb_*.jsonl")):
            fn = os.path.basename(f)
            with open(f) as fh:
                lines = fh.read().split("\n")
            for ln, line in enumerate(lines, 1):
                if not line.strip() or (fn, ln) in seen: continue
                try: rec = json.loads(line)
                except Exception: continue  # partial line, retry later
                c = rec["c"]
                r = full(c)
                bad = []
                if not r["correct"]: bad.append("INCORRECT")
                if not r["O2"]: bad.append("O2 false")
                if r["d"] != rec["disjoint"]: bad.append("disjoint %d!=%d" % (rec["disjoint"], r["d"]))
                if r["t"] != rec["pairs"]: bad.append("pairs %d!=%d" % (rec["pairs"], r["t"]))
                if r["ess"] != rec["ess"]: bad.append("ess %s!=%s" % (rec["ess"], r["ess"]))
                if r["fl"]: flags_all.append((fn, ln, r["fl"]))
                total += 1
                if bad: mism += 1
                if low is None or r["d"] < low[0]: low = (r["d"], fn, ln)
                seen[(fn, ln)] = 1
                P("%s:%d | %d/%d %s | %d/%d %s %s %s | %s" % (fn, ln, rec["disjoint"], rec["pairs"], rec["ess"],
                  r["d"], r["t"], r["correct"], r["O2"], r["ess"], "OK" if not bad else "MISMATCH " + "; ".join(bad)))
    passes()
    n1 = total
    passes()   # re-read once more at end for newly appended lines
    P("")
    P("records checked: %d (%d in first read, %d new in second read)" % (total, n1, total - n1))
    P("mismatches: %d" % mism)
    P("lowest score: %d/.. at %s:%d" % low if low else "none")
    P("Task 3: gates seeing >=3 blocks: %s" % (flags_all if flags_all else "none"))
    txt = "\n".join(out)
    open(base + "indep_check.txt", "w").write(txt + "\n")
    print(txt)

if __name__ == "__main__":
    main()
