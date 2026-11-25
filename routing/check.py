"""Road routing on small maps: Dijkstra, A*, contraction hierarchies, checked exactly.

Every connected graph on 2 to MAXN vertices (one per isomorphism class), with every assignment of edge
weights from {1, 2, 3}. For each weighted graph and every pair of stops:
  (a) Dijkstra (1959) equals Floyd-Warshall.
  (b) A* (Hart, Nilsson, Raphael 1968) with two consistent heuristics returns the same distance and settles
      no more nodes than Dijkstra. Heuristics: the exact distance to the target halved; and the one-landmark
      ALT bound |d(L,t) - d(L,v)| with landmark L = vertex 0. Ties: both searches pop the target first.
  (c) Contraction hierarchies (Geisberger, Sanders, Schultes, Delling 2008): contract in a fixed order
      (0, 1, ..., n-1), and in every order for n <= 4. A shortcut u-w is added when contracting v exactly
      when no witness path u..w avoiding v is as short as u-v-w (exact witness search, no hop limit).
      The bidirectional upward query must give the exact distance for every pair.
Joins: (i) transit: exact hitting times of the random walk against hop distance on the same unweighted
graphs; (ii) the centre: programs of center/shards as a road network.
Exact integers and fractions, standard library only. Prints PASS on success.

  python3 -I routing/check.py"""
import heapq, itertools, json, os, sys, time
from fractions import Fraction as Fr

MAXN = 5
W = (1, 2, 3)
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
INF = float("inf")

def canon(n, edges):
    best = None
    for p in itertools.permutations(range(n)):
        e = tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in edges))
        if best is None or e < best: best = e
    return best

def classes():
    out = {1: {()}}
    for n in range(2, MAXN + 1):
        got = set()
        for g in out[n - 1]:
            for k in range(1, 2 ** (n - 1)):
                got.add(canon(n, list(g) + [(i, n - 1) for i in range(n - 1) if k >> i & 1]))
        out[n] = got
    return out

def floyd(n, wt):
    d = [[0 if i == j else INF for j in range(n)] for i in range(n)]
    for (a, b), x in wt.items(): d[a][b] = d[b][a] = min(d[a][b], x)
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if d[i][k] + d[k][j] < d[i][j]: d[i][j] = d[i][k] + d[k][j]
    return d

def adjacency(n, wt):
    adj = [dict() for _ in range(n)]
    for (a, b), x in wt.items(): adj[a][b] = adj[b][a] = x
    return adj

def search(adj, s, t, h):
    """A* with heuristic h (h = 0 is Dijkstra). Stops when t is popped. Returns (distance, settled count).
    Heap key (g + h, target-last-flag, vertex): on equal keys the target is popped first."""
    g = {s: 0}; done = set(); pq = [(h(s), 0 if s == t else 1, s)]
    while pq:
        k, _, v = heapq.heappop(pq)
        if v in done: continue
        done.add(v)
        if v == t: return g[v], len(done)
        for u, x in adj[v].items():
            if u not in done and g[v] + x < g.get(u, INF):
                g[u] = g[v] + x; heapq.heappush(pq, (g[u] + h(u), 0 if u == t else 1, u))
    return INF, len(done)

def dists_from(adj, s, allowed):
    g = {s: 0}; pq = [(0, s)]; done = set()
    while pq:
        d, v = heapq.heappop(pq)
        if v in done: continue
        done.add(v)
        for u, x in adj[v].items():
            if u in allowed and d + x < g.get(u, INF): g[u] = d + x; heapq.heappush(pq, (g[u], u))
    return g

def contract(n, wt, order):
    """Returns (upward adjacency, number of shortcuts added)."""
    adj = adjacency(n, wt); rank = {v: i for i, v in enumerate(order)}
    alive = set(range(n)); added = 0
    up = [dict() for _ in range(n)]
    for v in order:
        for u, x in adj[v].items():
            if u in alive and u != v: up[v][u] = x   # every remaining neighbour is higher in rank
        alive.discard(v)
        nb = [u for u in adj[v] if u in alive]
        for u, w in itertools.combinations(nb, 2):
            via = adj[v][u] + adj[v][w]
            wit = dists_from(adj, u, alive).get(w, INF)
            if wit > via:
                adj[u][w] = adj[w][u] = via; added += 1
    return up, rank, added

def ch_query(up, s, t):
    ds = dists_from(up, s, set(range(len(up)))); dt = dists_from(up, t, set(range(len(up))))
    return min((ds[v] + dt[v] for v in ds if v in dt), default=INF)

def hitting(n, edges, t):
    """Exact expected moves of a simple random walk to reach t, from every start."""
    adj = [[] for _ in range(n)]
    for a, b in edges: adj[a].append(b); adj[b].append(a)
    vs = [v for v in range(n) if v != t]; idx = {v: i for i, v in enumerate(vs)}; k = len(vs)
    M = [[Fr(0)] * k + [Fr(1)] for _ in vs]
    for v in vs:
        M[idx[v]][idx[v]] += 1
        for u in adj[v]:
            if u != t: M[idx[v]][idx[u]] -= Fr(1, len(adj[v]))
    for c in range(k):
        p = next(r for r in range(c, k) if M[r][c] != 0); M[c], M[p] = M[p], M[c]
        for r in range(k):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]; M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    h = {t: Fr(0)}
    for v in vs: h[v] = M[idx[v]][k] / M[idx[v]][idx[v]]
    return h

def centre():
    """Programs of center/shards as a road network. Two records are linked when they share an evidence
    file or a program; two programs are adjacent (weight 1) when some records of each share an evidence file."""
    d = os.path.join(ROOT, "center", "shards"); recs = []
    for f in sorted(os.listdir(d)):
        if f.endswith(".jsonl"):
            for line in open(os.path.join(d, f), encoding="utf-8"):
                if line.strip(): r = json.loads(line); recs.append((r.get("program", f[:-6]), set(r.get("evidence", []))))
    progs = sorted({p for p, _ in recs}); ev = {p: set() for p in progs}
    for p, e in recs: ev[p] |= e
    adj = {p: {q: 1 for q in progs if q != p and ev[p] & ev[q]} for p in progs}
    dist = {p: dists_from(adj, p, set(progs)) for p in progs}
    ecc = {p: max(dist[p].get(q, INF) for q in progs) for p in progs}
    return progs, adj, dist, ecc, len(recs)

def main():
    t0 = time.time(); fails = []; cls = classes()
    nw = 0; pairs = 0; settle_dij = settle_a1 = settle_a2 = 0
    ch_fixed = {}; ch_all = {}   # n -> list of shortcut counts
    worst_all = (-1, None); best_gap = (-1, None); alt_more = 0; alt_ex = None
    for n in range(2, MAXN + 1):
        for g in sorted(cls[n]):
            m = len(g)
            for ws in itertools.product(W, repeat=m):
                nw += 1; wt = dict(zip(g, ws)); D = floyd(n, wt); adj = adjacency(n, wt)
                orders = list(itertools.permutations(range(n))) if n <= 4 else [tuple(range(n))]
                chs = []
                for o in orders:
                    up, rank, added = contract(n, wt, o); chs.append(added)
                    for s in range(n):
                        for t in range(n):
                            if ch_query(up, s, t) != D[s][t]: fails.append(("ch", n, wt, o, s, t))
                ch_fixed.setdefault(n, []).append(chs[orders.index(tuple(range(n)))])
                if n <= 4:
                    ch_all.setdefault(n, []).append((min(chs), max(chs)))
                    if max(chs) > worst_all[0]: worst_all = (max(chs), (n, wt, orders[chs.index(max(chs))], min(chs), orders[chs.index(min(chs))]))
                    if max(chs) - min(chs) > best_gap[0]: best_gap = (max(chs) - min(chs), (n, wt))
                for s in range(n):
                    for t in range(n):
                        pairs += 1
                        d0, k0 = search(adj, s, t, lambda v: 0)
                        d1, k1 = search(adj, s, t, lambda v: Fr(D[v][t], 2))
                        d2, k2 = search(adj, s, t, lambda v: abs(D[0][t] - D[0][v]))
                        if not (d0 == d1 == d2 == D[s][t]): fails.append(("dist", n, wt, s, t, d0, d1, d2, D[s][t]))
                        ball = sum(1 for v in range(n) if D[s][v] <= D[s][t])
                        if k1 > k0: fails.append(("settle d/2", n, wt, s, t, k0, k1))
                        if k2 > ball: fails.append(("settle alt", n, wt, s, t, k2, ball))
                        if k2 > k0:
                            alt_more += 1
                            if alt_ex is None: alt_ex = (n, wt, s, t, k0, k2)
                        settle_dij += k0; settle_a1 += k1; settle_a2 += k2
    print(f"(a,b) {nw} weighted connected graphs on 2..{MAXN} vertices (classes x weights in {{1,2,3}}), {pairs} ordered pairs:")
    print(f"      Dijkstra = A*(d/2) = A*(ALT, landmark 0) = Floyd-Warshall on every pair")
    print(f"      nodes settled in total: Dijkstra {settle_dij}, A*(d/2) {settle_a1}, A*(ALT) {settle_a2}")
    print(f"      A*(d/2) never settles more than Dijkstra. A*(ALT) never settles more than the ball d(s,v) <= d(s,t),")
    print(f"      but settles more than Dijkstra (target popped first on ties) in {alt_more} queries; first: {alt_ex}")
    for n in sorted(ch_fixed):
        c = ch_fixed[n]; print(f"(c) n={n}: fixed order 0..n-1, shortcuts min {min(c)} max {max(c)} total {sum(c)} over {len(c)} weighted graphs; query exact")
    for n in sorted(ch_all):
        c = ch_all[n]
        print(f"(c) n={n}: every order; best order per graph: max {max(a for a, b in c)} shortcuts; worst order per graph: max {max(b for a, b in c)}")
    print(f"    worst instance (n<=4): {worst_all[0]} shortcuts, n={worst_all[1][0]} weights {worst_all[1][1]}, order {worst_all[1][2]}; best order {worst_all[1][4]} needs {worst_all[1][3]}")
    # (i) transit join
    print("(i) transit: hitting time H(s,t) of the random walk vs hop distance d(s,t), unweighted, max ratio per n:")
    tbl = {}
    for n in range(2, MAXN + 1):
        best = (Fr(0), None)
        for g in sorted(cls[n]):
            D = floyd(n, {e: 1 for e in g})
            for t in range(n):
                h = hitting(n, g, t)
                for s in range(n):
                    if s == t: continue
                    if h[s] < D[s][t]: fails.append(("hit<dist", n, g, s, t))
                    r = h[s] / D[s][t]
                    if r > best[0]: best = (r, (g, s, t, h[s], D[s][t]))
        tbl[n] = best
        print(f"    n={n}: max H/d = {best[0]} (edges {best[1][0]}, {best[1][1]}->{best[1][2]}: H={best[1][3]}, d={best[1][4]})")
    hit = [int(tbl[n][0]) for n in range(2, MAXN + 1)]
    if any(tbl[n][0] != n * n - 3 * n + 3 for n in tbl): fails.append(("H/d not n^2-3n+3", hit))
    print(f"    max H/d = n^2 - 3n + 3 = (n-1)(n-2) + 1: the clique K_(n-1) with one pendant stop, the bus at the clique")
    print(f"    (the bridge-end time k(k-1)+1 of transit/social.py with k = n-1). The planned route is 1 move.")
    sc = [max(ch_fixed[n]) for n in range(2, MAXN + 1)]
    if sc != [(n - 1) * (n - 2) // 2 for n in range(2, MAXN + 1)]: fails.append(("shortcuts not C(n-1,2)", sc))
    fp = [{"name": "routing: max over connected n-stop graphs of hitting time / hop distance, n=2..%d" % MAXN, "seq": hit, "runner": "python3 -I routing/check.py"},
          {"name": "routing: max shortcuts of contraction in order 0..n-1, weights 1..3, n=2..%d" % MAXN, "seq": sc, "runner": "python3 -I routing/check.py"}]
    if not fails:
        with open(os.path.join(ROOT, "routing", "fingerprints.json"), "w", encoding="utf-8") as f:
            f.write("[\n" + ",\n".join(" " + json.dumps(x) for x in fp) + "\n]\n")
    # (ii) centre join
    progs, adj, dist, ecc, nrec = centre()
    print(f"(ii) centre: {nrec} records, {len(progs)} programs; adjacent when sharing an evidence file")
    for p in sorted(progs, key=lambda p: (-ecc[p] if ecc[p] != INF else -10**9, p)):
        reach = sum(1 for q in progs if q in dist[p])
        print(f"    {p:16s} eccentricity {ecc[p] if ecc[p] != INF else 'inf'}  neighbours {len(adj[p])}  reaches {reach}/{len(progs)}")
    comps = []; seen = set()
    for p in progs:
        if p not in seen: c = sorted(dist[p]); seen |= set(c); comps.append(c)
    print(f"    components: {len(comps)}; " + "; ".join("{" + ", ".join(c) + "}" for c in comps if len(c) > 1) + "; the rest alone")
    for f in fails[:20]: print("FAIL", f)
    if fails: sys.exit(1)
    per_n = [len(cls[n]) for n in range(1, MAXN + 1)]
    if per_n != [1, 1, 2, 6, 21][:MAXN]: print("FAIL class counts", per_n); sys.exit(1)
    print("PASS")
    print(json.dumps({"weighted_graphs": nw, "pairs": pairs, "seconds": round(time.time() - t0, 2)}))

if __name__ == "__main__": main()
