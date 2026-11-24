"""MU slack (WIDE = union of all enumerated Lean-valid classes; NARROW = research menus: D-maximal Z with atoms e_u, I0 at top_w with minterm atoms) (coord 11:55; referee 11:53): slack = |U(all)| - base, U(all) = union of all valid pure classes of all sets,
base = sum_w (|S_w| - 1). Discovery only; own code (merge run = puresdr_check.run, validated against Lean witnesses).

Options enumerated (all are Lean-valid, PureSDR.lean PureValid):
  .one / .oneAt with a COMMON A:  Z ∩ S_w = ∅, h(Z) = 0, test points {u} ∪ A, A ⊆ Z, world 1   (all Z, all A)
  .oneAt with per-atom A_u:       additionally A_u ∈ {∅, Z} independently per atom               (2^|S_w| per Z)
  .zero / .zeroAt:                any z with z ∩ S_w = ∅; m_u ⊆ z ∪ {u}, h(m_u) = 1; world 0   (minterm m_u, and
                                  the full m_u = z ∪ {u} if valid; product capped at CAP tuples per z)
Lean allows every per-atom A_u ⊆ Z ∪ {u} and every m_u; those are not all enumerated, so the U computed here is a SUBSET
of the true U(all): the reported slack is a LOWER BOUND. slack >= 0 here therefore proves MU on that circuit (on data);
slack = 0 here may be > 0 in truth.
Usage: python3 -I mu_slack.py files... [--nmax 12] [--cap 2000] [--out result.json]
"""
import itertools, json, sys
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import puresdr_check as P
from dichotomy import subsets


def union_all(c, T, CAP):
    n, Pn = c.n, 1 << c.n
    h = T[c.gates[c.p][1]]
    hv = lambda x: (h >> x) & 1
    mint = [x for x in range(Pn) if hv(x) and not any(hv(x & ~(1 << v)) for v in range(n) if (x >> v) & 1)]
    U = set()
    for S in c.sets:
        Rm = sum(1 << u for u in S)
        top = (Pn - 1) & ~Rm
        for Z in subsets(top):
            if not hv(Z):
                for A in subsets(Z):
                    U |= P.run(c, Z, {u: (1 << u) | A for u in S}, S, 1)
                for bits in itertools.product([0, 1], repeat=len(S)):
                    U |= P.run(c, Z, {u: (1 << u) | (Z if b else 0) for u, b in zip(S, bits)}, S, 1)
            # world 0 at zero point z = Z (any z avoiding S_w)
            per = []
            for u in S:
                allow = Z | (1 << u)
                opts = [m for m in mint if (m & ~allow) == 0]
                if hv(allow) and allow not in opts:
                    opts.append(allow)
                per.append(opts)
            if all(per):
                for ms in itertools.islice(itertools.product(*per), CAP):
                    U |= P.run(c, Z, {u: ms[i] | (1 << u) for i, u in enumerate(S)}, S, 0)
    return U


if __name__ == "__main__":
    args = sys.argv[1:]
    NMAX = int(args[args.index("--nmax") + 1]) if "--nmax" in args else 12
    CAP = int(args[args.index("--cap") + 1]) if "--cap" in args else 2000
    out = args[args.index("--out") + 1] if "--out" in args else None
    files = [a for i, a in enumerate(args) if not a.startswith("--") and (i == 0 or args[i - 1] not in ("--nmax", "--cap", "--out"))]
    H = Counter(); HN = Counter(); zero = []; zeroN = []; neg = []; diff = Counter(); nc = 0
    for p in files:
        for k, d in P.items(p):
            if not (isinstance(d, dict) and "gates" in d and "sets" in d):
                continue
            c = P.Circ(d)
            if not c.ok1 or c.n > NMAX or any(len(S) < 2 for S in c.sets):
                continue
            T = c.table()
            if not c.correct(T):
                continue
            nc += 1
            base = sum(len(S) - 1 for S in c.sets)
            sl = len(union_all(c, T, CAP)) - base
            narrow = set().union(*[o[3] for m in P.menus(c, T) for o in m["opts"]])
            sn = len(narrow) - base
            H[sl] += 1; HN[sn] += 1; diff[sl - sn] += 1
            if sn == 0 and len(zeroN) < 200:
                zeroN.append(f"{p}#{k}")
            if sl == 0 and len(zero) < 200:
                zero.append(f"{p}#{k}")
            if sl < 0:
                neg.append(f"{p}#{k}")
    r = {"circuits": nc, "WIDE_slack_hist": dict(sorted(H.items())), "WIDE_min": min(H) if H else None,
         "WIDE_slack0_count": H.get(0, 0), "WIDE_slack0_examples": zero, "WIDE_negative": neg[:50],
         "NARROW_slack_hist": dict(sorted(HN.items())), "NARROW_min": min(HN) if HN else None,
         "NARROW_slack0_count": HN.get(0, 0), "NARROW_slack0_examples": zeroN,
         "WIDE_minus_NARROW_hist": dict(sorted(diff.items()))}
    s = json.dumps(r, indent=1)
    if out:
        open(out, "w").write(s + "\n")
    print(s)
