"""Lower bound on the LIFTED menu union (Lean PureGP.liftMenu / MUL; coord 12:16). Discovery only.

Lift = the circuit with the NOT gate replaced by a free input y (= puresdr_check eval(x, y)). A lifted test system for set R
(output o) is a zero point z in {0,1}^(n+1) and atoms q_c (c in R): VALID iff o(z) = 0, o(q_c) = 1 for every c, and
outside z the atoms are separated (no coordinate with z = 0 is 1 in two atoms). Class = union-find merge run in the lift.
Enumerated here (a subfamily, so |U| is a LOWER BOUND on |U_lift| and slack_lift >= reported):
  every lifted z with o(z) = 0; atoms q_c = B ∪ {c} ∪ P_c with B ∈ {∅, ones(z)} common, P_c ⊆ zeros(z) \\ R obtained by
  assigning each extra zero coordinate (y included) to at most one atom (all (|R|+1)^k assignments, k <= KMAX, else none).
Usage: python3 -I lifted_union.py files... [--kmax 6]
"""
import itertools, json, sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import puresdr_check as P


def ev(c, x, y):
    return c.eval(x, y)


def run_lift(c, z, atoms, R):
    (zx, zy) = z
    wz = ev(c, zx, zy)
    at = {u: ev(c, *atoms[u]) for u in R}
    lab = {u: u for u in R}
    M = []
    for k, g in enumerate(c.gates):
        i = c.n + k
        if g[0] == "not" or wz[i]:
            continue
        tr = {lab[u] for u in R if at[u][i]}
        if len(tr) >= 2:
            M.append(i)
            r = min(tr)
            for u in R:
                if lab[u] in tr:
                    lab[u] = r
    return frozenset(M)


def lifted_union(c, KMAX=6):
    n, Pn = c.n, 1 << c.n
    U = set()
    for w, R in enumerate(c.sets):
        o = c.outs[w]
        for zx in range(Pn):
            for zy in (0, 1):
                if ev(c, zx, zy)[o]:
                    continue
                zeros = [v for v in range(n) if not (zx >> v) & 1 and v not in R] + (["y"] if zy == 0 else [])
                if len(zeros) > KMAX:
                    zeros = zeros[:KMAX]
                for Bfull in (False, True):
                    for assign in itertools.product([None] + list(R), repeat=len(zeros)):
                        atoms = {}
                        for u in R:
                            x = (zx if Bfull else 0) | (1 << u)
                            y = zy if Bfull else 0
                            for e, a in zip(zeros, assign):
                                if a == u:
                                    if e == "y":
                                        y = 1
                                    else:
                                        x |= 1 << e
                            atoms[u] = (x, y)
                        if not all(ev(c, *atoms[u])[o] for u in R):
                            continue
                        U |= run_lift(c, (zx, zy), atoms, R)
    return U


if __name__ == "__main__":
    args = sys.argv[1:]
    KMAX = int(args[args.index("--kmax") + 1]) if "--kmax" in args else 6
    files = [a for i, a in enumerate(args) if not a.startswith("--") and (i == 0 or args[i - 1] != "--kmax")]
    for p in files:
        for k, d in P.items(p):
            if isinstance(d, dict) and "gates" in d:
                c = P.Circ(d)
                base = sum(len(S) - 1 for S in c.sets)
                U = lifted_union(c, KMAX)
                print(json.dumps({"file": f"{p}#{k}", "n": c.n, "base": base, "lifted_U_lower_bound": len(U),
                                  "lifted_slack_lower_bound": len(U) - base, "gates": sorted(U)}))
