"""Independent PureSDR checker (pnp-subproblem, coord assignment 11:35). Discovery only, NOT proof authority.

No research/tools/w951, no research/tools/kill_tests code. Definitions follow proofs/w951/PEqualNP/W951/PureSDR.lean (PureValid, pureI1,
pureI0, runMT in MergeRunT.lean), translated to REAL wire numbers (the NOT gate itself is never a merge):

  C_y = the circuit with the NOT gate's output forced to the constant y.
  Merge run (runMT): walk the gates in order (skipping the NOT); with zero point z and test points p_u (u in R),
    a gate g merges iff g(z) = 0 in C_y and its trace {u in R : g(p_u) = 1 in C_y} meets >= 2 union-find labels;
    then those labels are joined. The class is the set of merging gates.
  I1(R, Z): world y = 1, zero point Z, test points e_u.          VALID: Z = 0 on R and h(Z) = 0 (NOT(Z) = 1).
  I0(R, m): world y = 0, zero point top_R (0 exactly on R), test points m_u ∪ {u}.
                                                                 VALID: m_u ∩ R ⊆ {u} and h(m_u) = 1.
  Menus (coord: minimal choices suffice): I1 over the MAXIMAL Z with Z ∩ R = ∅, h(Z) = 0; I0 over all tuples of
  MINIMAL m_u (minterms of h with m_u ∩ R ⊆ {u}).
Reports: (a) a pure SDR exists; (b) every valid class has exactly |R| - 1 merges; (c) for type-A sets (h(top_R) = 1),
the collisions among menu pairs (option of a type-A set w vs option of any other set w'), by kind:
  (i)   I1 vs I1 where some Z vanishes at >= 2 points of the other set,
  (ii)  I0 vs I0 where some m_u meets the other set,
  (iii) I1 vs I0,
  and 'other' (collisions outside (i)-(iii): must be 0 by the Lean disjointness lemmas; a nonzero count is a bug or a
  counterexample to those lemmas).
Usage: python3 -I puresdr_check.py files... [--out summary.json]
"""
import itertools, json, sys
from collections import Counter


def popcount(x):
    return bin(x).count("1")


class Circ:
    def __init__(self, d):
        self.n, self.sets, self.gates, self.outs = d["n"], [list(S) for S in d["sets"]], d["gates"], d["outs"]
        nots = [k for k, g in enumerate(self.gates) if g[0] == "not"]
        self.ok1 = len(nots) == 1
        self.p = nots[0] if nots else None
        self.N = self.n + self.p if nots else None  # wire of the NOT gate

    def eval(self, x, y=None):
        """Wire values at the point x (bitmask over inputs); y forces the NOT gate (None = real circuit)."""
        n, v = self.n, [(x >> i) & 1 for i in range(self.n)]
        for k, g in enumerate(self.gates):
            if g[0] == "not":
                v.append((1 - v[g[1]]) if y is None else y)
            elif g[0] == "and":
                v.append(v[g[1]] & v[g[2]])
            else:
                v.append(v[g[1]] | v[g[2]])
        return v

    def table(self):
        """Truth tables (ints over 2^n points) of every wire of the real circuit (bit-parallel)."""
        n, P = self.n, 1 << self.n
        full = (1 << P) - 1
        T = []
        for i in range(n):
            t = 0
            for x in range(P):
                if (x >> i) & 1:
                    t |= 1 << x
            T.append(t)
        for g in self.gates:
            if g[0] == "not":
                T.append(full ^ T[g[1]])
            elif g[0] == "and":
                T.append(T[g[1]] & T[g[2]])
            else:
                T.append(T[g[1]] | T[g[2]])
        return T

    def correct(self, T):
        P = 1 << self.n
        for w, S in enumerate(self.sets):
            want = 0
            for x in range(P):
                if any((x >> u) & 1 for u in S):
                    want |= 1 << x
            if T[self.outs[w]] != want:
                return False
        return True


def run(c, z, pts, R, y):
    """runMT in real wires: merge set at zero point z, test points pts[u], world y."""
    wz = c.eval(z, y)
    at = {u: c.eval(pts[u], y) for u in R}
    lab = {u: u for u in R}
    M = []
    for k, g in enumerate(c.gates):
        i = c.n + k
        if g[0] == "not" or wz[i]:
            continue
        tr = {lab[u] for u in R if at[u][i]}
        if len(tr) >= 2:
            M.append(i)
            rep = min(tr)
            for u in R:
                if lab[u] in tr:
                    lab[u] = rep
    return frozenset(M)


def menus(c, T):
    n, P = c.n, 1 << c.n
    h = T[c.gates[c.p][1]]  # the NOT gate's input
    hv = lambda x: (h >> x) & 1
    out = []
    for w, S in enumerate(c.sets):
        Rm = sum(1 << u for u in S)
        top = (P - 1) & ~Rm
        typeA = hv(top) == 1
        opts = []
        # I1: maximal Z with Z & Rm == 0, h(Z) = 0
        free = [v for v in range(n) if not (Rm >> v) & 1]
        for Z in range(P):
            if Z & Rm or hv(Z):
                continue
            if any(not (Z >> v) & 1 and not hv(Z | (1 << v)) for v in free):
                continue  # not maximal
            pts = {u: 1 << u for u in S}
            opts.append(("I1", Z, None, run(c, Z, pts, S, 1)))
        # I0: per u, minimal m with h(m) = 1 and m & Rm subset of {u}
        mins = []
        for u in S:
            allowed = top | (1 << u)
            cand = [m for m in range(P) if (m & ~allowed) == 0 and hv(m)]
            minimal = [m for m in cand if not any(hv(m & ~(1 << v)) for v in range(n) if (m >> v) & 1)]
            mins.append(minimal)
        if all(mins):
            for tup in itertools.product(*mins):
                pts = {u: tup[k] | (1 << u) for k, u in enumerate(S)}
                opts.append(("I0", None, dict(zip(S, tup)), run(c, top, pts, S, 0)))
        out.append({"typeA": typeA, "Rm": Rm, "opts": opts})
    return out


def sdr(mn):
    order = sorted(range(len(mn)), key=lambda w: len(mn[w]["opts"]))
    pick = {}

    def rec(k, used):
        if k == len(order):
            return True
        w = order[k]
        for o in mn[w]["opts"]:
            if not (o[3] & used):
                pick[w] = o
                if rec(k + 1, used | o[3]):
                    return True
        return False
    return rec(0, frozenset()), pick


def kind(o, Rm_o, q, Rm_q):
    if o[0] == "I1" and q[0] == "I1":
        two = lambda Z, Rm: popcount(Rm & ~Z) >= 2  # Z vanishes at >= 2 points of the other set
        return "i" if (two(q[1], Rm_o) or two(o[1], Rm_q)) else "other_I1I1"
    if o[0] == "I0" and q[0] == "I0":
        meets = lambda m, Rm: any(mu & Rm for mu in m.values())
        return "ii" if (meets(o[2], Rm_q) or meets(q[2], Rm_o)) else "other_I0I0"
    return "iii"


def check(d, stats):
    c = Circ(d)
    if not c.ok1 or not any(len(S) >= 2 for S in c.sets) or c.n > 16:
        stats["skipped"] += 1
        return
    T = c.table()
    if not c.correct(T):
        stats["incorrect"] += 1
        return
    stats["circuits"] += 1
    mn = menus(c, T)
    for w, m in enumerate(mn):
        for o in m["opts"]:
            if len(o[3]) != len(c.sets[w]) - 1:
                stats["class_size_bad"] += 1
        if not m["opts"]:
            stats["empty_menu"] += 1
        if m["typeA"]:
            stats["typeA_sets"] += 1
    ok, _ = sdr(mn)
    if ok:
        stats["sdr_yes"] += 1
    elif len(stats["sdr_fail_examples"]) < 10:
        stats["sdr_fail_examples"].append(stats["cur"])
    seen = Counter()
    for w, m in enumerate(mn):
        if not m["typeA"]:
            continue
        for w2, m2 in enumerate(mn):
            if w2 == w or (mn[w2]["typeA"] and w2 < w):
                continue
            for o in m["opts"]:
                for q in m2["opts"]:
                    if o[3] & q[3]:
                        k = kind(o, m["Rm"], q, m2["Rm"])
                        stats["collisions"][k] += 1
                        seen[k] += 1
    for k in seen:
        stats["circuits_with"][k] += 1
        if k.startswith("other") and len(stats["other_examples"]) < 10:
            stats["other_examples"].append(stats["cur"])


def items(path):
    if path.endswith(".jsonl"):
        for k, line in enumerate(open(path)):
            line = line.strip()
            if line:
                try:
                    d = json.loads(line)
                except Exception:
                    continue
                if isinstance(d, dict):
                    yield k, d.get("circuit", d)
    else:
        try:
            d = json.load(open(path))
        except Exception:
            return
        for k, it in enumerate(d if isinstance(d, list) else [d]):
            if isinstance(it, dict):
                yield k, it.get("circuit", it)


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    out = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else None
    if out in args:
        args.remove(out)
    stats = Counter(),
    stats = {"circuits": 0, "skipped": 0, "incorrect": 0, "sdr_yes": 0, "class_size_bad": 0, "empty_menu": 0,
             "typeA_sets": 0, "collisions": Counter(), "circuits_with": Counter(), "sdr_fail_examples": [],
             "other_examples": [], "cur": None}
    for p in args:
        for k, d in items(p):
            if not isinstance(d, dict) or "gates" not in d or "sets" not in d:
                continue
            stats["cur"] = f"{p}#{k}"
            try:
                check(d, stats)
            except Exception as e:
                stats["skipped"] += 1
    stats.pop("cur")
    s = json.dumps(stats, indent=1, default=dict)
    if out:
        open(out, "w").write(s + "\n")
    print(s)
