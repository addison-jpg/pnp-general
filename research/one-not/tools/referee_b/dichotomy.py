"""Independent test of the board integrator's DICHOTOMY (coord 11:48; PROOF_PLAN_SUGGESTIONS §0 'Third run').
Discovery only. Own code (no kill_tests / w951); merge run = puresdr_check.run (validated against Lean witnesses).

Domains (Lean validity, widened I1, as stated in kill_tests/csp.py's header):
  I1: Z with Z ∩ S_w = ∅ and h(Z) = 0; test points {u} ∪ A for one common A ⊆ Z; world y = 1.
  I0: zero point top_w; test points m_u ∪ {u} with h(m_u) = 1, m_u ∩ S_w ⊆ {u}; world y = 0. All tuples of valid m_u
      if there are at most 20,000 tuples, else tuples of minterms (as csp.py), first 20,000.
Sets with h(top_w) = 0 are FIXED at their free class K_1(w) (y = 1, zero point top_w, test points e_u).
Filter as csp.py: one NOT, correct, every set of size >= 2, pairwise |S_w ∩ S_w'| <= 1; n <= NMAX (default 12).
Then arc consistency (AC-3) on the type-A sets, and for every surviving class: does it extend to a full pure SDR?
DICHOTOMY: either every surviving class extends (globally consistent), or every set that has a non-extendable surviving
class has <= 2 surviving classes. Reports: circuits, failures of the dichotomy (smallest witness), not globally consistent,
AC wipe-outs, no SDR at all.
Usage: python3 -I dichotomy.py files... [--nmax 12] [--out result.json]
"""
import itertools, json, sys
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import puresdr_check as P
CAP = 20000
CAPPED = []
ST_SIZE = []


def subsets(mask):
    s = mask
    while True:
        yield s
        if s == 0:
            return
        s = (s - 1) & mask


def domains(c, T):
    n, Pn = c.n, 1 << c.n
    h = T[c.gates[c.p][1]]
    hv = lambda x: (h >> x) & 1
    dom, typeA, free = [], [], {}
    for w, S in enumerate(c.sets):
        Rm = sum(1 << u for u in S)
        top = (Pn - 1) & ~Rm
        tA = hv(top) == 1
        typeA.append(tA)
        if not tA:
            free[w] = P.run(c, top, {u: 1 << u for u in S}, S, 1)
            dom.append([free[w]])
            continue
        cls = set()
        for Z in subsets(top):
            if hv(Z):
                continue
            for A in subsets(Z):
                cls.add(P.run(c, Z, {u: (1 << u) | A for u in S}, S, 1))
        per = [[m for m in range(Pn) if hv(m) and (m & Rm) & ~(1 << u) == 0] for u in S]
        if all(per):
            ST_SIZE.append(len(per))
            size = 1
            for q in per:
                size *= len(q)
            if size > CAP:
                CAPPED.append(1)
                mint = [x for x in range(Pn) if hv(x) and not any(hv(x & ~(1 << v)) for v in range(n) if (x >> v) & 1)]
                per = [[m for m in mint if (m & Rm) & ~(1 << u) == 0] for u in S]
            for ms in itertools.islice(itertools.product(*per), CAP):
                cls.add(P.run(c, top, {u: ms[i] | (1 << u) for i, u in enumerate(S)}, S, 0))
        dom.append(list(cls))
    return dom, typeA, free


def ac3(d, vs):
    changed = True
    while changed:
        changed = False
        for a in vs:
            for b in vs:
                if a == b:
                    continue
                keep = [x for x in d[a] if any(not (x & y) for y in d[b])]
                if len(keep) != len(d[a]):
                    d[a] = keep
                    changed = True
                    if not keep:
                        return False
    return True


def extends(d, vs, w, x):
    """Is there a pairwise disjoint choice over vs with w = x (others from their domains)?"""
    rest = sorted((v for v in vs if v != w), key=lambda v: len(d[v]))

    def rec(k, used):
        if k == len(rest):
            return True
        for y in d[rest[k]]:
            if not (y & used) and rec(k + 1, used | y):
                return True
        return False
    return rec(0, x)


def check(d0, st, name):
    c = P.Circ(d0)
    if not c.ok1 or c.n > NMAX or any(len(S) < 2 for S in c.sets):
        return
    if any(len(set(a) & set(b)) > 1 for a, b in itertools.combinations(c.sets, 2)):
        st["skip_pairwise_intersection"] += 1
        return
    T = c.table()
    if not c.correct(T):
        st["incorrect"] += 1
        return
    st["circuits"] += 1
    dom, typeA, free = domains(c, T)
    if any(free[a] & free[b] for a, b in itertools.combinations(free, 2)):
        st["free_classes_collide"] += 1
    used = frozenset().union(*free.values()) if free else frozenset()
    A = [w for w in range(len(c.sets)) if typeA[w]]
    if not A:
        st["no_typeA_set"] += 1
        return
    d = {w: [x for x in dom[w] if not (x & used)] for w in A}
    if not ac3(d, A):
        st["ac_wipeout"] += 1
        EX["ac_wipeout"].append(name)
        return
    bad = {w: [x for x in d[w] if not extends(d, A, w, x)] for w in A}
    nonext = [w for w in A if bad[w]]
    if all(len(bad[w]) == len(d[w]) for w in A) and all(bad[w] for w in A):
        st["no_sdr"] += 1
        EX["no_sdr"].append(name)
        return
    if not nonext:
        st["globally_consistent"] += 1
        return
    st["not_globally_consistent"] += 1
    sizes = tuple(sorted(len(d[w]) for w in nonext))
    EX["not_gc"].append((c.n, len(c.gates), name, sizes))
    if max(sizes) >= 3:
        st["dichotomy_FAILS"] += 1
        EX["fail"].append((c.n, len(c.gates), name, sizes))


if __name__ == "__main__":
    args = sys.argv[1:]
    NMAX = int(args[args.index("--nmax") + 1]) if "--nmax" in args else 12
    CAP = int(args[args.index("--cap") + 1]) if "--cap" in args else 20000
    out = args[args.index("--out") + 1] if "--out" in args else None
    files = [a for i, a in enumerate(args) if not a.startswith("--") and (i == 0 or args[i - 1] not in ("--nmax", "--out", "--cap"))]
    st = Counter()
    EX = {"ac_wipeout": [], "no_sdr": [], "not_gc": [], "fail": []}
    for p in files:
        for k, d0 in P.items(p):
            if isinstance(d0, dict) and "gates" in d0 and "sets" in d0:
                try:
                    check(d0, st, f"{p}#{k}")
                except Exception as e:
                    st["error"] += 1
    st["circuits_with_a_capped_I0_menu_sets"] = len(CAPPED)
    r = {**st, "examples_fail": sorted(EX["fail"])[:10], "examples_not_gc": sorted(EX["not_gc"])[:10],
         "examples_ac_wipeout": EX["ac_wipeout"][:10], "examples_no_sdr": EX["no_sdr"][:10]}
    s = json.dumps(r, indent=1)
    if out:
        open(out, "w").write(s + "\n")
    print(s)
