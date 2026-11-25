#!/usr/bin/env python3
"""Counterexample search for L-meta-951 on a given set system.

Question: is there a list of S gates (AND/OR of two wires, NOT of one wire, at most K NOT gates)
on n inputs whose wires include, for every set S_i, a wire equal to OR(x_v : v in S_i)
on all 2^n inputs?  SAT = a circuit smaller than sum(|S_i|-1) exists = 951 refuted.

  python3 sat951.py fano S K [timeout]
  python3 sat951.py k4 S K            (sets = edges of K4, sanity case)
"""
import itertools, sys, threading, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

FANO = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def build(n, sets, S, K):
    rows = list(itertools.product((0, 1), repeat=n))
    R = len(rows)
    top = [0]

    def nv():
        top[0] += 1
        return top[0]

    cl = []

    def amo(lits):
        enc = CardEnc.atmost(lits, 1, top_id=top[0], encoding=EncType.seqcounter)
        top[0] = max(top[0], enc.nv)
        cl.extend(enc.clauses)

    W = n + S
    val = {}
    for i in range(n):
        for r in range(R):
            val[(i, r)] = rows[r][i]  # constant 0/1
    for g in range(S):
        for r in range(R):
            val[(n + g, r)] = nv()
    isand = [nv() for _ in range(S)]
    isor = [nv() for _ in range(S)]
    isnot = [nv() for _ in range(S)]
    for g in range(S):
        cl.append([isand[g], isor[g], isnot[g]])
        amo([isand[g], isor[g], isnot[g]])
    # at most K NOT gates
    enc = CardEnc.atmost(isnot, K, top_id=top[0], encoding=EncType.seqcounter)
    top[0] = max(top[0], enc.nv)
    cl.extend(enc.clauses)

    def lit(w, r, pos):
        v = val[(w, r)]
        if w < n:
            return "T" if (v == 1) == pos else "F"
        return v if pos else -v

    def emit(c):
        out = []
        for t in c:
            if t == "T":
                return
            if t == "F":
                continue
            out.append(t)
        cl.append(out)

    sel2 = {}
    sel1 = {}
    for g in range(S):
        w = n + g
        pairs = list(itertools.combinations(range(w), 2))
        singles = list(range(w))
        p2 = [nv() for _ in pairs]
        p1 = [nv() for _ in singles]
        for (p, q), s in zip(pairs, p2):
            sel2[(g, p, q)] = s
        for p, s in zip(singles, p1):
            sel1[(g, p)] = s
        # binary op -> exactly one pair; NOT -> exactly one single
        cl.append([isnot[g]] + p2)
        cl.append([-isnot[g]] + p1)
        amo(p2)
        amo(p1)
        for s in p2:
            cl.append([-s, -isnot[g]])
        for s in p1:
            cl.append([-s, isnot[g]])
        for (p, q), s in zip(pairs, p2):
            for r in range(R):
                o = val[(w, r)]
                emit([-s, -isand[g], -o, lit(p, r, True)])
                emit([-s, -isand[g], -o, lit(q, r, True)])
                emit([-s, -isand[g], o, lit(p, r, False), lit(q, r, False)])
                emit([-s, -isor[g], o, lit(p, r, False)])
                emit([-s, -isor[g], o, lit(q, r, False)])
                emit([-s, -isor[g], -o, lit(p, r, True), lit(q, r, True)])
        for p, s in zip(singles, p1):
            for r in range(R):
                o = val[(w, r)]
                emit([-s, o, lit(p, r, True)])
                emit([-s, -o, lit(p, r, False)])
    # each set's OR appears on some gate wire
    outsel = {}
    for k, st in enumerate(sets):
        ch = [nv() for _ in range(S)]
        cl.append(ch)
        for g, c in enumerate(ch):
            outsel[(k, g)] = c
            for r in range(R):
                want = any(rows[r][v] for v in st)
                o = val[(n + g, r)]
                cl.append([-c, o] if want else [-c, -o])
    # symmetry break: every gate is read later or is an output
    for g in range(S):
        w = n + g
        users = [s for (h, p, q), s in sel2.items() if h > g and w in (p, q)]
        users += [s for (h, p), s in sel1.items() if h > g and p == w]
        users += [outsel[(k, g)] for k in range(len(sets))]
        cl.append(users)
    return cl, rows, val, isand, isor, isnot, sel2, sel1, outsel


def main():
    name, S, K = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    tmo = float(sys.argv[4]) if len(sys.argv) > 4 else 600
    sets = FANO if name == "fano" else K4
    n = 1 + max(max(s) for s in sets)
    bound = sum(len(s) - 1 for s in sets)
    cl, rows, val, isand, isor, isnot, sel2, sel1, outsel = build(n, sets, S, K)
    print(f"{name}: n={n} sets={len(sets)} sum(|S|-1)={bound}; testing S={S} gates, <= {K} NOT; "
          f"{len(cl)} clauses", flush=True)
    s = Cadical153(bootstrap_with=cl)
    t = time.time()
    timer = threading.Timer(tmo, s.interrupt)
    timer.start()
    res = s.solve_limited(expect_interrupt=True)
    timer.cancel()
    dt = time.time() - t
    if res is None:
        print(f"TIMEOUT after {dt:.0f}s", flush=True)
        return
    if not res:
        print(f"UNSAT ({dt:.1f}s): no such circuit", flush=True)
        return
    M = set(l for l in s.get_model() if l > 0)
    print(f"SAT ({dt:.1f}s): circuit found", flush=True)
    gates = []
    for g in range(S):
        if isnot[g] in M:
            p = [p for (h, p), v in sel1.items() if h == g and v in M][0]
            gates.append(("NOT", p))
        else:
            pq = [(p, q) for (h, p, q), v in sel2.items() if h == g and v in M][0]
            gates.append(("AND" if isand[g] in M else "OR",) + pq)
    for g, gt in enumerate(gates):
        print(f"  w{n + g} = {gt}")
    # independent re-check on all rows
    ok = True
    outs = {}
    for k, st in enumerate(sets):
        g = [g for g in range(S) if outsel[(k, g)] in M][0]
        outs[k] = n + g
        for x in rows:
            w = list(x)
            for gt in gates:
                if gt[0] == "NOT":
                    w.append(1 - w[gt[1]])
                elif gt[0] == "AND":
                    w.append(w[gt[1]] & w[gt[2]])
                else:
                    w.append(w[gt[1]] | w[gt[2]])
            if w[n + g] != int(any(x[v] for v in st)):
                ok = False
    print("outputs:", outs, "| independent re-check on all rows:", ok, flush=True)


if __name__ == "__main__":
    main()
