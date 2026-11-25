#!/usr/bin/env python3
"""
nb_search.py -- naive-Bayes-guided min-max upper bounds + SAT search for the
graph edge function  f_G(x) = OR_{uv in E} (x_u AND x_v).

Part 1 (upper bound, "min-max"):
  f_G = OR over parts P of ( OR(A_P) AND OR(B_P) ), where each part (A,B) is a
  biclique of G (every a in A adjacent to every b in B). A star is K_{1,d};
  a 4-cycle is K_{2,2}. Cost of a part = |A| + |B| - 1 gates, plus (#parts - 1)
  joining ORs. Stars only  => |E| + k - 1  (k = cover size; repo note 1 (d)).
  Bicliques can beat |E| + tau - 1 on graphs with 4-cycles (note 1: C4 in 3 gates).

  Decision points are scored by:
    net savings (edges newly covered - gates spent)            [primary]
    + a * NB(A u B) + (1 - a) * degree(A u B)   (z-scored)      [tie-break / guide]
  a = 0.8 by default: NB-heavy, degree as the final check. Chosen from a sweep
  over 84 graphs (star mode: a >= 0.6 with beam reached the exact vertex cover
  on every graph; a = 0.5 missed one; degree-only missed 19 stars in total).
  Beam search (width W) keeps the W best partial covers.

Part 2 (search):
  Exact-synthesis SAT: does a MONOTONE fan-in-2 AND/OR circuit with s gates
  compute f_G?  Junk gates are allowed, so "exactly s" == "at most s".
  The heuristic circuit is fed in as solver phase hints (and inputs are
  relabelled in NB order). Hints only steer the solver: they never add
  clauses, so UNSAT answers stay sound lower bounds for monotone circuits.
  Rows can be restricted to Hamming weight <= R first (UNSAT there is UNSAT
  overall); any SAT circuit is re-verified on all 2^n rows before reporting.

Usage:
  python3 nb_search.py bench                    # heuristic benchmark, all modes
  python3 nb_search.py graph q3 [--sat S] [--rows R] [--timeout T]
  python3 nb_search.py graph l701 | petersen | c4 | q4 | "edges:0-1,1-2,2-3"
"""
import argparse, itertools, math, random, sys, time, threading

# ======================= graphs =======================
def g_named(name):
    name = name.lower()
    if name == "l701":
        return 5, [(0, 1), (0, 2), (1, 2), (0, 3), (3, 4)]
    if name in ("q3", "q4", "q2"):
        d = int(name[1]); n = 1 << d
        return n, [(a, b) for a in range(n) for b in range(a + 1, n) if bin(a ^ b).count("1") == 1]
    if name == "c4":
        return 4, [(0, 1), (1, 2), (2, 3), (0, 3)]
    if name == "petersen":
        E = [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)] + \
            [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
        return 10, [tuple(sorted(e)) for e in E]
    if name == "trap":
        L = list(range(6)); E = []; nxt = 6
        for size in range(2, 7):
            for start in range(0, 6 - size + 1, size):
                for l in L[start:start + size]:
                    E.append((l, nxt))
                nxt += 1
        return nxt, E
    if name.startswith("edges:"):
        E = [tuple(sorted(map(int, e.split("-")))) for e in name[6:].split(",") if e]
        return max(max(e) for e in E) + 1, sorted(set(E))
    raise SystemExit(f"unknown graph {name}")

def g_random(n, p, seed):
    r = random.Random(seed)
    return n, [(a, b) for a in range(n) for b in range(a + 1, n) if r.random() < p]

def f_val(E, x):
    return 1 if any(x[u] and x[v] for u, v in E) else 0

# ======================= naive Bayes + degree =======================
def nb_weights(E, verts, samples=4096, seed=0):
    """log P(x_v=1 | f=1) / P(x_v=1 | f=0), Laplace smoothed, on the residual function.
    Full truth table if <= 16 live vertices, else uniform sampling."""
    verts = sorted(verts)
    if not E:
        return {v: 0.0 for v in verts}
    idx = {v: i for i, v in enumerate(verts)}; m = len(verts)
    c = [[[1, 1], [1, 1]] for _ in range(m)]
    if m <= 16:
        it = itertools.product((0, 1), repeat=m)
    else:
        rng = random.Random(seed)
        it = (tuple(rng.getrandbits(1) for _ in range(m)) for _ in range(samples))
    El = [(idx[u], idx[v]) for u, v in E]
    for x in it:
        t = 1 if any(x[u] and x[v] for u, v in El) else 0
        for i in range(m):
            c[i][t][x[i]] += 1
    return {v: math.log((c[i][1][1] / sum(c[i][1])) / (c[i][0][1] / sum(c[i][0])))
            for v, i in idx.items()}

def zscore(d):
    if not d:
        return {}
    vals = list(d.values()); mu = sum(vals) / len(vals)
    sd = math.sqrt(sum((x - mu) ** 2 for x in vals) / len(vals)) or 1.0
    return {k: (x - mu) / sd for k, x in d.items()}

def vertex_scores(E, a):
    deg = {}
    for u, v in E:
        deg[u] = deg.get(u, 0) + 1; deg[v] = deg.get(v, 0) + 1
    nb = nb_weights(E, deg.keys())
    zn, zd = zscore(nb), zscore(deg)
    return {v: a * zn[v] + (1 - a) * zd[v] for v in deg}, deg

# ======================= biclique candidates =======================
def adjacency(n, E):
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v); adj[v].add(u)
    return adj

def candidates(n, E_all, E_res, use_bicliques=True):
    """Bicliques (A, B) touching at least one residual edge.
    Stars ({v}, N(v)) and K_{2,m}: ({a,c}, common neighbours) with m >= 2.
    Neighbourhoods are taken in the FULL graph (re-covering an edge is free)."""
    adj = adjacency(n, E_all)
    res = set(E_res); out = []
    live = {u for e in E_res for u in e}
    for v in range(n):
        if v in live and adj[v]:
            out.append((frozenset([v]), frozenset(adj[v])))
    if use_bicliques:
        for a, c in itertools.combinations(range(n), 2):
            if c in adj[a]:
                continue
            B = adj[a] & adj[c]
            if len(B) >= 2:
                out.append((frozenset([a, c]), frozenset(B)))
    def covered(A, B):
        return {tuple(sorted((x, y))) for x in A for y in B} & res
    out2 = []
    for A, B in out:
        cov = covered(A, B)
        if cov:
            out2.append((A, B, cov))
    return out2

def part_cost(A, B):
    return len(A) + len(B) - 1

def trim(A, B, E_res):
    """drop B-vertices (and A-vertices for |A|>1) that cover no residual edge"""
    res = set(E_res)
    B2 = frozenset(b for b in B if any(tuple(sorted((a, b))) in res for a in A))
    if len(A) > 1:
        A2 = frozenset(a for a in A if any(tuple(sorted((a, b))) in res for b in B2))
        if len(A2) == 1:   # degenerated to a star: re-expand B to all residual nbrs
            (a,) = A2
            B2 = frozenset(y for e in res if a in e for y in e if y != a)
        A = A2
    return A, B2

def score_parts(n, E_all, E_res, a, use_bicliques):
    vs, _ = vertex_scores(E_res, a)
    scored = []
    for A, B, cov in candidates(n, E_all, E_res, use_bicliques):
        A, B = trim(A, B, E_res)
        if not A or not B:
            continue
        cov = {tuple(sorted((x, y))) for x in A for y in B} & set(E_res)
        save = len(cov) - part_cost(A, B)            # >= 0 for stars, > 0 for K_{2,m}
        # guide = NB/degree blend of the center side A (for a star: the center itself)
        guide = sum(vs.get(v, 0.0) for v in A) / len(A)
        scored.append((save, guide, A, B, cov))
    scored.sort(key=lambda t: (-t[0], -t[1], sorted(t[2]), sorted(t[3])))
    return scored

def cover_greedy(n, E, a=0.8, use_bicliques=True):
    E_res = list(E); parts = []
    while E_res:
        save, guide, A, B, cov = score_parts(n, E, E_res, a, use_bicliques)[0]
        parts.append((A, B)); E_res = [e for e in E_res if e not in cov]
    return parts

def total_cost(parts):
    return sum(part_cost(A, B) for A, B in parts) + len(parts) - 1

def matching_lb(E_res):
    used = set(); m = 0
    for u, v in E_res:
        if u not in used and v not in used:
            used.add(u); used.add(v); m += 1
    return m

def cover_beam(n, E, a=0.8, width=6, topk=4, use_bicliques=True):
    states = [((), tuple(E), 0)]
    best = None
    while states:
        nxt = []
        for parts, E_res, cost in states:
            if not E_res:
                c = cost + len(parts) - 1
                if best is None or c < best[0]:
                    best = (c, parts)
                continue
            for save, guide, A, B, cov in score_parts(n, E, E_res, a, use_bicliques)[:topk]:
                nxt.append((parts + ((A, B),), tuple(e for e in E_res if e not in cov),
                            cost + part_cost(A, B), guide))
        # rank by projected total: spent + |E_res| (star cost of the rest)
        #   + parts so far + a lower bound on parts still needed (maximal matching
        #   size <= tau of the residual graph); NB/degree guide breaks ties
        nxt.sort(key=lambda t: (t[2] + len(t[1]) + len(t[0]) + matching_lb(t[1]), -t[3]))
        seen = set(); states = []
        for p, r, c, g in nxt:
            key = (frozenset(p), r)
            if key in seen:
                continue
            seen.add(key); states.append((p, r, c))
            if len(states) >= width:
                break
    return list(best[1])

def exact_vc(n, E):
    verts = sorted({u for e in E for u in e})
    for k in range(len(verts) + 1):
        for S in itertools.combinations(verts, k):
            s = set(S)
            if all(u in s or v in s for u, v in E):
                return list(S)

# ======================= circuits =======================
def build_circuit(n, parts):
    gates = []
    def add(op, x, y):
        gates.append((op, x, y)); return n + len(gates) - 1
    def or_all(vs):
        vs = sorted(vs); w = vs[0]
        for u in vs[1:]:
            w = add("OR", w, u)
        return w
    outs = [add("AND", or_all(A), or_all(B)) for A, B in parts]
    o = outs[0]
    for w in outs[1:]:
        o = add("OR", o, w)
    return gates, o

def eval_circuit(n, gates, x):
    val = list(x)
    for op, p, q in gates:
        val.append(val[p] & val[q] if op == "AND" else val[p] | val[q])
    return val

def verify(n, E, gates, out):
    for x in itertools.product((0, 1), repeat=n):
        if eval_circuit(n, gates, x)[out] != f_val(E, x):
            return False
    return True

def pnp_weight(n, gates):
    """pequalnp L-meta-701 weight: AND=1, wide OR=1, narrow OR=2"""
    singles = [eval_circuit(n, gates, tuple(int(i == j) for i in range(n))) for j in range(n)]
    return sum(1 if op == "AND" else (1 if sum(s[n + k] for s in singles) >= 2 else 2)
               for k, (op, _, _) in enumerate(gates))

# ======================= SAT exact synthesis =======================
def critical_rows(n, E):
    """Minimal true points (the edges) and maximal false points (maximal independent sets).
    A monotone circuit computes f_G iff it is 1 on every minimal true point and 0 on every
    maximal false point, so SAT on these rows is exact in BOTH directions for monotone circuits."""
    out = []
    for x in itertools.product((0, 1), repeat=n):
        v = f_val(E, x)
        if v and all(not f_val(E, x[:i] + (0,) + x[i+1:]) for i in range(n) if x[i]):
            out.append(x)
        if not v and all(f_val(E, x[:i] + (1,) + x[i+1:]) for i in range(n) if not x[i]):
            out.append(x)
    return out

def sat_search(n, E, S, hint=None, rows_max_weight=None, timeout=300, solver_name="g4",
               all_used=False):
    """Is there a monotone circuit with exactly S gates (junk allowed => <= S)?
    rows_max_weight: None (all rows), an int R (rows of weight <= R), or 'critical'.
    all_used: every non-output gate feeds a later gate. Then the answer is about EXACTLY S
    useful gates, so test each size separately (a minimal circuit has no unused gate).
    Returns ('SAT', gates) / ('UNSAT', None) / ('TIMEOUT', None)."""
    from pysat.solvers import Solver
    from pysat.card import CardEnc, EncType
    if rows_max_weight == "critical":
        rows = critical_rows(n, E)
    else:
        rows = [x for x in itertools.product((0, 1), repeat=n)
                if rows_max_weight is None or sum(x) <= rows_max_weight]
    top = [0]
    def nv():
        top[0] += 1; return top[0]
    cl = []
    op = [nv() for _ in range(S)]                       # true = AND
    sel = {}
    val = {}
    for g in range(S):
        w = n + g
        for r in range(len(rows)):
            val[(w, r)] = nv()
    for g in range(S):
        w = n + g
        lits = []
        for p, q in itertools.combinations(range(w), 2):
            sel[(g, p, q)] = nv(); lits.append(sel[(g, p, q)])
        cl.append(lits)
        enc = CardEnc.atmost(lits, 1, top_id=top[0], encoding=EncType.seqcounter)
        top[0] = max(top[0], enc.nv); cl += enc.clauses
    def term(wire, r, positive):
        """literal for wire value; constants for inputs. returns ('T'|'F') or int"""
        if wire < n:
            bit = rows[r][wire]
            return "T" if bool(bit) == positive else "F"
        v = val[(wire, r)]
        return v if positive else -v
    def emit(c):
        out = []
        for t in c:
            if t == "T":
                return
            if t == "F":
                continue
            out.append(t)
        cl.append(out)
    for (g, p, q), s in sel.items():
        o = n + g
        for r in range(len(rows)):
            vo = val[(o, r)]
            # AND
            emit([-s, -op[g], -vo, term(p, r, True)])
            emit([-s, -op[g], -vo, term(q, r, True)])
            emit([-s, -op[g], vo, term(p, r, False), term(q, r, False)])
            # OR
            emit([-s, op[g], vo, term(p, r, False)])
            emit([-s, op[g], vo, term(q, r, False)])
            emit([-s, op[g], -vo, term(p, r, True), term(q, r, True)])
    for r, x in enumerate(rows):
        o = val[(n + S - 1, r)]
        cl.append([o] if f_val(E, x) else [-o])
    if all_used:
        for g in range(S - 1):
            w = n + g
            cl.append([s_ for (h, p, q), s_ in sel.items() if h > g and w in (p, q)])
    solver = Solver(name=solver_name, bootstrap_with=cl)
    if hint:
        # phase hints from the heuristic circuit, aligned to the END (output side)
        hg = hint[-S:] if len(hint) >= S else hint
        shift = S - len(hg)
        offset = len(hint) - len(hg)
        ph = []
        for k, (o_, p, q) in enumerate(hg):
            g = k + shift
            remap = lambda w: w if w < n else w - offset + shift
            p2, q2 = sorted((remap(p), remap(q)))
            if 0 <= p2 < q2 < n + g and (g, p2, q2) in sel:
                ph.append(sel[(g, p2, q2)])
                ph.append(op[g] if o_ == "AND" else -op[g])
        try:
            solver.set_phases(ph)
        except Exception:
            pass
    timer = threading.Timer(timeout, solver.interrupt); timer.start()
    res = solver.solve_limited(expect_interrupt=True)
    timer.cancel()
    if res is None:
        solver.delete(); return "TIMEOUT", None
    if not res:
        solver.delete(); return "UNSAT", None
    M = set(l for l in solver.get_model() if l > 0)
    gates = []
    for g in range(S):
        pq = [(p, q) for (h, p, q), s in sel.items() if h == g and s in M][0]
        gates.append(("AND" if op[g] in M else "OR", pq[0], pq[1]))
    solver.delete()
    return "SAT", gates

# ======================= NB relabelling =======================
def nb_relabel(n, E, a=0.8):
    vs, _ = vertex_scores(E, a)
    order = sorted(range(n), key=lambda v: (-vs.get(v, -99), v))
    pos = {v: i for i, v in enumerate(order)}
    return [tuple(sorted((pos[u], pos[v]))) for u, v in E], order

# ======================= CLI =======================
def best_upper(n, E, a=0.8):
    res = {}
    runs = []
    if n <= 22:   # floor: exact vertex cover stars = |E| + tau - 1 (note 1 (d))
        T = exact_vc(n, E); E_res = list(E); vc_parts = []
        for t in T:
            nbr = frozenset(y for e in E_res if t in e for y in e if y != t)
            if nbr:
                vc_parts.append((frozenset([t]), nbr))
            E_res = [e for e in E_res if t not in e]
        runs.append(("stars-exactVC", vc_parts))
    for label, parts in runs + [("stars-beam", cover_beam(n, E, a, use_bicliques=False)),
                         ("biclique-greedy", cover_greedy(n, E, a, True)),
                         ("biclique-beam", cover_beam(n, E, a, use_bicliques=True))]:
        g, o = build_circuit(n, parts)
        assert verify(n, E, g, o), label
        res[label] = (len(g), pnp_weight(n, g), parts, g)
    return res

def cmd_graph(args):
    n, E = g_named(args.graph)
    E, order = nb_relabel(n, E, args.a)
    tau = len(exact_vc(n, E)) if n <= 22 else None
    print(f"graph {args.graph}: n={n} |E|={len(E)} tau={tau} "
          f"|E|+tau-1={len(E)+tau-1 if tau is not None else '?'}  (NB order of original ids: {order})")
    res = best_upper(n, E, args.a)
    for k, (size, w, parts, _) in res.items():
        print(f"  {k:16} gates={size:3}  pnp-weight={w:3}  parts={[ (sorted(A), sorted(B)) for A,B in parts]}")
    best = min(res.values(), key=lambda t: t[0])
    if args.sat is not None:
        sizes = [args.sat] if args.sat > 0 else list(range(best[0] - 1, 0, -1))
        for S in sizes:
            t = time.time()
            st, gates = sat_search(n, E, S, hint=best[3], rows_max_weight=args.rows, timeout=args.timeout,
                                   all_used=args.all_used)
            if st == "SAT" and not verify(n, E, gates, n + S - 1):
                st = "SAT-on-restricted-rows-only (not a circuit for f_G)"
            print(f"  SAT S={S:3} rows<={args.rows}: {st}  ({time.time()-t:.1f}s)")
            if st == "SAT":
                for k, gt in enumerate(gates):
                    print(f"     w{n+k} = {gt[0]}(w{gt[1]}, w{gt[2]})")
            if st != "SAT" or args.sat > 0:
                break

def cmd_bench(args):
    random.seed(7)
    suite = [("trap", g_named("trap")), ("l701", g_named("l701")), ("q3", g_named("q3")),
             ("c4", g_named("c4")), ("petersen", g_named("petersen"))]
    for s in range(args.count):
        n = random.choice([10, 11, 12, 13, 14]); p = random.choice([.15, .2, .3, .4])
        suite.append((f"G({n},{p})#{s}", g_random(n, p, 1000 + s)))
    tot = {"|E|+tau-1": 0, "stars-exactVC": 0, "stars-beam": 0, "biclique-greedy": 0, "biclique-beam": 0}
    beat = 0
    for name, (n, E) in suite:
        if not E:
            continue
        tau = len(exact_vc(n, E)); base = len(E) + tau - 1
        res = best_upper(n, E, args.a)
        tot["|E|+tau-1"] += base
        for k in res:
            tot[k] += res[k][0]
        if min(r[0] for r in res.values()) < base:
            beat += 1
        if args.verbose:
            print(f"{name:16} n={n:2} |E|={len(E):3} base={base:3} " +
                  " ".join(f"{k}={res[k][0]}" for k in res))
    print(f"graphs={len(suite)}  total gates: " + ", ".join(f"{k}={v}" for k, v in tot.items()))
    print(f"graphs where a biclique cover beat |E|+tau-1: {beat}")

def cmd_tree(args):
    """Tree search (alternative to SAT). Each node uses the data structures that won
    ds_bench.py for this kind of job: heap+hashset to FIND a circuit, stack+hashset to
    EXHAUST (prove no circuit with S gates). Inputs are relabelled in NB order first,
    so the deterministic child order follows the NB/degree ranking."""
    from ds_bench import search, verify as tverify, DEFAULTS
    n, E = g_named(args.graph)
    E, order = nb_relabel(n, E, args.a)
    mode = args.mode
    fr, me = (args.frontier or DEFAULTS[mode][0]), (args.memo or DEFAULTS[mode][1])
    print(f"tree search {args.graph}: n={n} |E|={len(E)} S={args.S} mode={mode} "
          f"frontier={fr} memo={me}")
    st = search(n, E, args.S, fr, me, cap=args.cap, tlimit=args.timeout)
    print(f"  status={st['status']} nodes={st['nodes']} memo_hits={st['memo_hits']} "
          f"peak={st['peak']} time={st.get('time', 0):.2f}s")
    if st["status"] == "found":
        print(f"  verified on all inputs: {tverify(n, E, st['found'])}")
        for k, (op, i, j) in enumerate(st["found"]):
            print(f"     w{n+k} = {op}(w{i}, w{j})")
    elif st["status"] == "exhausted":
        print(f"  no monotone circuit with <= {args.S} gates (exhaustive, memo-deduplicated)")
    else:
        print("  inconclusive (hit node cap or time limit)")

def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    t = sub.add_parser("tree"); t.add_argument("graph"); t.add_argument("S", type=int)
    t.add_argument("--mode", choices=["find", "exhaust"], default="find")
    t.add_argument("--frontier", choices=["stack", "queue", "heap", "adaptive"], default=None)
    t.add_argument("--memo", choices=["none", "hashset", "sortedarray", "bst"], default=None)
    t.add_argument("--a", type=float, default=0.8)
    t.add_argument("--cap", type=int, default=2_000_000)
    t.add_argument("--timeout", type=float, default=600)
    g = sub.add_parser("graph"); g.add_argument("graph")
    g.add_argument("--a", type=float, default=0.8, help="NB weight in the NB/degree blend")
    g.add_argument("--sat", type=int, default=None, help="S>0: test S gates; 0: walk down from best-1")
    g.add_argument("--rows", type=lambda v: v if v == "critical" else int(v), default=None,
                   help="R: rows of Hamming weight <= R; 'critical': minterms + maximal false points (exact)")
    g.add_argument("--all-used", action="store_true",
                   help="every non-output gate is read later (test each size S separately)")
    g.add_argument("--timeout", type=float, default=300)
    b = sub.add_parser("bench"); b.add_argument("--a", type=float, default=0.8)
    b.add_argument("--count", type=int, default=60); b.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()
    {"graph": cmd_graph, "bench": cmd_bench, "tree": cmd_tree}[args.cmd](args)

if __name__ == "__main__":
    main()
