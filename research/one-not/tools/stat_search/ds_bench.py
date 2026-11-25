#!/usr/bin/env python3
"""
ds_bench.py -- which simple data structure should a proof-search node use?

The search: find a monotone fan-in-2 AND/OR circuit with <= S gates computing
the graph edge function f_G (truth tables are n-bit-row bitmasks). Each search
NODE is a partial circuit (a set of wire truth tables). Children add one gate.

Two plug-in slots, each a plain undergrad data structure:

  FRONTIER (which node to expand next)
    stack   -- list, LIFO            => depth-first
    queue   -- collections.deque     => breadth-first
    heap    -- heapq binary min-heap => best-first, key = (h, depth)
               h = min over wires of popcount(wire XOR target)  (distance to goal)
    adaptive-- one stack + one queue + one heap; every node is TAGGED with the
               container it lives in; the search picks the container to pop from
               by epsilon-greedy on each container's "novel child rate"
               (fraction of children that were new states). Children inherit
               their parent's tag unless the bandit reassigns them.

  MEMO (have we seen this partial circuit before?)
    none        -- no memo (baseline)
    hashset     -- Python set (hash table)
    sortedarray -- list kept sorted with bisect.insort; binary search lookups
    bst         -- unbalanced binary search tree, written out by hand

Every (frontier, memo) pair runs on small graphs whose optimum S* is known
(from a SAT walk-down in nb_search.py, or hard-coded). We search with budget
S = S*, so every run must FIND a circuit; we record nodes, memo hits, peak
frontier size, and time. Found circuits are re-verified on all 2^n inputs.

Usage:
  python3 ds_bench.py                 # full table
  python3 ds_bench.py --graphs c4,p4 --cap 200000 --tlimit 30
"""
import argparse, bisect, collections, heapq, itertools, random, sys, time

# ======================= graphs + exact optima =======================
GRAPHS = {
    # name: (n, edges, optimum monotone gate count)
    "p3":       (3, [(0, 1), (1, 2)], 2),                         # x1 & (x0|x2)
    "triangle": (3, [(0, 1), (0, 2), (1, 2)], None),
    "k13":      (4, [(0, 1), (0, 2), (0, 3)], 3),
    "c4":       (4, [(0, 1), (1, 2), (2, 3), (0, 3)], 3),         # (x0|x2)&(x1|x3)
    "p4":       (4, [(0, 1), (1, 2), (2, 3)], None),
    "paw":      (4, [(0, 1), (0, 2), (1, 2), (2, 3)], None),
    "p5":       (5, [(0, 1), (1, 2), (2, 3), (3, 4)], None),
    "l701":     (5, [(0, 1), (0, 2), (1, 2), (0, 3), (3, 4)], 7),
}

def optimum(n, E):
    """exact monotone gate count via SAT walk-up (needs python-sat)."""
    from nb_search import sat_search
    for S in range(1, 3 * len(E)):
        st, _ = sat_search(n, E, S, timeout=120)
        if st == "SAT":
            return S
    raise RuntimeError("no optimum found")

def tables(n, E):
    rows = list(itertools.product((0, 1), repeat=n))
    inputs = [sum(1 << r for r, x in enumerate(rows) if x[i]) for i in range(n)]
    target = sum(1 << r for r, x in enumerate(rows) if any(x[u] and x[v] for u, v in E))
    return inputs, target, (1 << len(rows)) - 1

# ======================= MEMO structures =======================
class NoMemo:
    name = "none"
    def add_if_new(self, key):
        return True
    def __len__(self):
        return 0

class HashSetMemo:
    name = "hashset"
    def __init__(self):
        self.s = set()
    def add_if_new(self, key):
        if key in self.s:
            return False
        self.s.add(key); return True
    def __len__(self):
        return len(self.s)

class SortedArrayMemo:
    """sorted Python list; binary search to look up, insort to insert (O(n) shift)"""
    name = "sortedarray"
    def __init__(self):
        self.a = []
    def add_if_new(self, key):
        i = bisect.bisect_left(self.a, key)
        if i < len(self.a) and self.a[i] == key:
            return False
        self.a.insert(i, key); return True
    def __len__(self):
        return len(self.a)

class BSTMemo:
    """plain unbalanced binary search tree; nodes are [key, left, right]"""
    name = "bst"
    def __init__(self):
        self.root = None; self.n = 0; self.max_depth = 0
    def add_if_new(self, key):
        if self.root is None:
            self.root = [key, None, None]; self.n = 1; return True
        cur = self.root; d = 0
        while True:
            d += 1
            if key == cur[0]:
                return False
            side = 1 if key < cur[0] else 2
            if cur[side] is None:
                cur[side] = [key, None, None]; self.n += 1
                self.max_depth = max(self.max_depth, d); return True
            cur = cur[side]
    def __len__(self):
        return self.n

MEMOS = {"none": NoMemo, "hashset": HashSetMemo, "sortedarray": SortedArrayMemo, "bst": BSTMemo}

# ======================= search tree node =======================
class Node:
    """One node of the search tree = one partial circuit.
    wires : tuple of gate truth tables (inputs are implicit)
    gates : tuple of (op, i, j) wire indices, for printing / verifying
    tag   : which frontier container this node lives in (the per-node DS choice)
    """
    __slots__ = ("wires", "gates", "depth", "h", "tag")
    def __init__(self, wires, gates, depth, h, tag):
        self.wires, self.gates, self.depth, self.h, self.tag = wires, gates, depth, h, tag
    def key(self):
        return tuple(sorted(self.wires))        # canonical: gate order doesn't matter

def popcount(x):
    return bin(x).count("1")

def dist(wires_all, target):
    return min(popcount(w ^ target) for w in wires_all)

# ======================= FRONTIER structures =======================
class StackFrontier:
    name = "stack"
    def __init__(self): self.a = []
    def push(self, node): self.a.append(node)
    def pop(self): return self.a.pop()
    def __len__(self): return len(self.a)

class QueueFrontier:
    name = "queue"
    def __init__(self): self.a = collections.deque()
    def push(self, node): self.a.append(node)
    def pop(self): return self.a.popleft()
    def __len__(self): return len(self.a)

class HeapFrontier:
    name = "heap"
    def __init__(self): self.a = []; self.c = 0
    def push(self, node):
        self.c += 1; heapq.heappush(self.a, (node.h, -node.depth, self.c, node))
    def pop(self): return heapq.heappop(self.a)[3]
    def __len__(self): return len(self.a)

class AdaptiveFrontier:
    """stack + queue + heap. Each node carries a tag naming its container.
    pop(): epsilon-greedy over non-empty containers by novel-child rate.
    report(tag, novel, total): feedback from expanding a node of that tag."""
    name = "adaptive"
    def __init__(self, eps=0.15, seed=0):
        self.c = {"stack": StackFrontier(), "queue": QueueFrontier(), "heap": HeapFrontier()}
        self.novel = {k: 1.0 for k in self.c}; self.tot = {k: 2.0 for k in self.c}
        self.eps = eps; self.rng = random.Random(seed)
        self.pops = {k: 0 for k in self.c}
    def push(self, node):
        if node.tag not in self.c:
            node.tag = "heap"
        self.c[node.tag].push(node)
    def best_tag(self):
        live = [k for k in self.c if len(self.c[k])]
        return max(live, key=lambda k: self.novel[k] / self.tot[k]) if live else "heap"
    def pop(self):
        live = [k for k in self.c if len(self.c[k])]
        k = self.rng.choice(live) if self.rng.random() < self.eps else \
            max(live, key=lambda k: self.novel[k] / self.tot[k])
        self.pops[k] += 1
        return self.c[k].pop()
    def report(self, tag, novel, total):
        self.novel[tag] += novel; self.tot[tag] += total
    def __len__(self):
        return sum(len(v) for v in self.c.values())

FRONTIERS = {"stack": StackFrontier, "queue": QueueFrontier, "heap": HeapFrontier,
             "adaptive": AdaptiveFrontier}

# Winners from the benchmark (small graphs, 2026-11-23):
#  find    (budget S*):   heap + hashset  -- 159 nodes total vs 1765 queue / 3808 stack
#  exhaust (budget S*-1): stack + hashset -- memo cuts nodes 3.3x (6060 vs 19833);
#                         frontier order doesn't change the count when exhausting,
#                         but stack peak = 73 vs queue 4440 (memory); hashset fastest memo.
DEFAULTS = {"find": ("heap", "hashset"), "exhaust": ("stack", "hashset")}

# ======================= the search =======================
def search(n, E, S, frontier_name, memo_name, cap=300000, tlimit=60.0):
    inputs, target, full = tables(n, E)
    F = FRONTIERS[frontier_name](); M = MEMOS[memo_name]()
    stats = dict(nodes=0, memo_hits=0, peak=0, found=None, status="exhausted")
    start_tag = "heap" if frontier_name == "adaptive" else frontier_name
    root = Node((), (), 0, dist(inputs, target), start_tag)
    if target in inputs:
        stats.update(found=(), status="found"); return stats
    F.push(root); M.add_if_new(root.key())
    t0 = time.time()
    while len(F):
        if stats["nodes"] >= cap:
            stats["status"] = "cap"; break
        if (stats["nodes"] & 1023) == 0 and time.time() - t0 > tlimit:
            stats["status"] = "time"; break
        node = F.pop(); stats["nodes"] += 1
        if node.depth >= S:
            continue
        allw = inputs + list(node.wires)
        present = set(allw)
        novel = total = 0
        # deterministic child order; heap/adaptive reorder by h anyway
        for i in range(len(allw)):
            for j in range(i + 1, len(allw)):
                for op in ("AND", "OR"):
                    m = allw[i] & allw[j] if op == "AND" else allw[i] | allw[j]
                    if m in present or m == 0 or m == full:
                        continue
                    total += 1
                    wires = node.wires + (m,)
                    gates = node.gates + ((op, i, j),)
                    if m == target:
                        stats.update(found=gates, status="found",
                                     time=time.time() - t0, memo_size=len(M))
                        if isinstance(F, AdaptiveFrontier):
                            stats["pops"] = dict(F.pops)
                        return stats
                    if node.depth + 1 >= S:      # last gate must hit target
                        continue
                    child = Node(wires, gates, node.depth + 1,
                                 min(node.h, popcount(m ^ target)), node.tag)
                    if not M.add_if_new(child.key()):
                        stats["memo_hits"] += 1
                        continue
                    novel += 1
                    if isinstance(F, AdaptiveFrontier):
                        # per-node DS choice: child goes to the container that is
                        # currently paying off best (else stays with parent's tag)
                        r = F.rng.random()
                        if r < F.eps:
                            child.tag = F.rng.choice(("stack", "queue", "heap"))
                        elif r < 0.5:
                            child.tag = F.best_tag()
                        else:
                            child.tag = node.tag
                    F.push(child)
        if isinstance(F, AdaptiveFrontier) and total:
            F.report(node.tag, novel, total)
        stats["peak"] = max(stats["peak"], len(F))
    stats["time"] = time.time() - t0; stats["memo_size"] = len(M)
    if isinstance(F, AdaptiveFrontier):
        stats["pops"] = dict(F.pops)
    return stats

def verify(n, E, gates):
    inputs, target, _ = tables(n, E)
    w = list(inputs)
    for op, i, j in gates:
        w.append(w[i] & w[j] if op == "AND" else w[i] | w[j])
    return w[-1] == target

# ======================= benchmark =======================
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graphs", default="p3,k13,c4,triangle,p4,paw,p5,l701")
    ap.add_argument("--frontiers", default="stack,queue,heap,adaptive")
    ap.add_argument("--memos", default="none,hashset,sortedarray,bst")
    ap.add_argument("--cap", type=int, default=300000, help="max nodes per run")
    ap.add_argument("--tlimit", type=float, default=60.0, help="seconds per run")
    ap.add_argument("--mode", default="find", choices=["find", "exhaust"],
                    help="find: budget S* (must find). exhaust: budget S*-1 (must prove none "
                         "exists -- what a lower-bound proof needs)")
    args = ap.parse_args()
    results = collections.defaultdict(list)
    want = "found" if args.mode == "find" else "exhausted"
    for gname in args.graphs.split(","):
        n, E, S = GRAPHS[gname]
        if S is None:
            S = optimum(n, E)
        if args.mode == "exhaust":
            S -= 1
        print(f"\n== {gname}: n={n} |E|={len(E)} budget S={S} ({args.mode})")
        print(f"   {'frontier':9} {'memo':11} {'status':9} {'nodes':>8} {'hits':>8} "
              f"{'peak':>8} {'memo':>8} {'time':>7}")
        for fr in args.frontiers.split(","):
            for me in args.memos.split(","):
                st = search(n, E, S, fr, me, args.cap, args.tlimit)
                ok = st["status"] == "found" and verify(n, E, st["found"])
                if st["status"] == "found" and not ok:
                    st["status"] = "BADCIRC"
                results[(fr, me)].append((gname, st))
                extra = f"  pops={st['pops']}" if "pops" in st else ""
                print(f"   {fr:9} {me:11} {st['status']:9} {st['nodes']:>8} {st['memo_hits']:>8} "
                      f"{st['peak']:>8} {st.get('memo_size', 0):>8} {st.get('time', 0):>7.2f}{extra}")
    # ranking: solved count, then total time over solved, then nodes
    print(f"\n== ranking [{args.mode}] (solved, total time, total nodes, max peak frontier)")
    rank = []
    for k, lst in results.items():
        solved = [s for _, s in lst if s["status"] == want]
        rank.append((len(solved), sum(s.get("time", 0) for s in solved),
                     sum(s["nodes"] for s in solved), max((s["peak"] for s in solved), default=0), k))
    rank.sort(key=lambda r: (-r[0], r[1], r[2]))
    for solved, t, nodes, peak, (fr, me) in rank:
        print(f"   {fr:9} + {me:11} solved {solved}/{len(results[(fr, me)])}  "
              f"time {t:7.2f}s  nodes {nodes:>9}  peak {peak:>8}")

if __name__ == "__main__":
    main()
