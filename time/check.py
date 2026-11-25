"""time/: a local big bang, a multiverse big bang, moving forward, multiverse postmodernism.
Standard library only. Exact (integers, sets). git is used read-only (rev-list, log, show).

Parts (see time/BASE.md):
 1. The repo's own history as a DAG: roots, commits, merges, acyclic, every commit reaches a root,
    the alpha line (a longest root-to-HEAD path), commits off it.
 2. Initial objects: all preorders on 1..4 elements; which have a least element; any two are
    isomorphic (a <= b and b <= a). The ontology's level preorder from level.json join arrows.
 3. A time step adds passing checks. Settled stays settled: all toy stores of <= 4 records, all
    orders of <= 4 steps. With a failing re-check allowed, a counterexample exists.
    The real history of every findings.jsonl is walked and reported (tested, not checked).
 4. Beauvoir: no non-trivial reflexive, transitive, antisymmetric frame on 1..4 worlds is symmetric.
 5. Postmodern-safe: a formula valid on every frame of a stated class (S4 on 1..3 worlds for
    'every branching history', S5 on 1..3 worlds for 'no privileged world').
 6. Qual-quant types of the frames in frames_time.ath (rules of ontology/QUALQUANT.md).
Prints PASS when every check holds.
"""
import glob, json, os, re, subprocess, sys
from itertools import permutations, product

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ok = True
def want(name, cond):
    global ok
    print(("ok   " if cond else "FAIL ") + name)
    ok = ok and bool(cond)

def git(*a):
    return subprocess.run(["git", "-C", ROOT] + list(a), capture_output=True, text=True, check=True).stdout

# ---------- 1. local big bang ----------
par = {}
for line in git("rev-list", "--parents", "HEAD").split("\n"):
    if line.strip():
        h, *ps = line.split()
        par[h] = ps
head = git("rev-parse", "HEAD").strip()
roots = [h for h, ps in par.items() if not ps]
merges = [h for h, ps in par.items() if len(ps) > 1]
children = {h: [] for h in par}
for h, ps in par.items():
    for p in ps: children[p].append(h)
# Kahn from roots: every commit gets an order iff the graph is acyclic
indeg = {h: len(ps) for h, ps in par.items()}
order, stack = [], [h for h in par if indeg[h] == 0]
while stack:
    h = stack.pop(); order.append(h)
    for c in children[h]:
        indeg[c] -= 1
        if indeg[c] == 0: stack.append(c)
want("git DAG: acyclic (a topological order covers all %d commits)" % len(par), len(order) == len(par))
reach = {}
for h in order:
    reach[h] = {h} if not par[h] else set().union(*(reach[p] for p in par[h]))
want("git DAG: every commit reaches a root (%d root(s))" % len(roots), all(reach[h] & set(roots) for h in par))
want("git DAG: every commit has a parent unless it is a root; every parent is in the history",
     all(p in par for ps in par.values() for p in ps))
is_tree = not merges
dist, best = {}, {}
for h in order:
    if not par[h]: dist[h], best[h] = 0, None
    else:
        p = max(par[h], key=lambda q: (dist[q], q)); dist[h], best[h] = dist[p] + 1, p
alpha, x = [], head
while x is not None: alpha.append(x); x = best[x]
alpha.reverse()
# exactness: no root-to-HEAD path is longer (check every edge relaxes)
want("alpha line is a longest root-to-HEAD path (no edge relaxes it)",
     all(dist[h] >= dist[p] + 1 for h in par for p in par[h]) and alpha[0] in roots and alpha[-1] == head
     and all(alpha[i] in par[alpha[i + 1]] for i in range(len(alpha) - 1)))
first, y = [], head
while y: first.append(y); y = par[y][0] if par[y] else None
off = len(par) - len(alpha)
print("  roots %s (t = 0); commits %d; merges %d; %s; alpha line %d commits; off it %d; first-parent line %d"
      % ([r[:7] for r in roots], len(par), len(merges), "tree" if is_tree else "DAG (branches rejoin)",
         len(alpha), off, len(first)))

# ---------- 2. initial objects ----------
def preorders(n):
    pairs = [(a, b) for a in range(n) for b in range(n) if a != b]
    for bits in range(1 << len(pairs)):
        R = {(a, a) for a in range(n)} | {pairs[i] for i in range(len(pairs)) if bits >> i & 1}
        if all((a, d) in R for (a, b) in R for (c, d) in R if b == c):
            yield R
counts, least_counts = [], []
good = True
for n in range(1, 5):
    tot = wl = 0
    for R in preorders(n):
        tot += 1
        L = [a for a in range(n) if all((a, b) in R for b in range(n))]
        if L: wl += 1
        good &= all((a, b) in R and (b, a) in R for a in L for b in L)  # unique up to iso
    counts.append(tot); least_counts.append(wl)
want("preorders on 1..4 elements: %s (OEIS A000798)" % counts, counts == [1, 4, 29, 355])
want("of these, with a least (initial) element: %s; any two initial elements are isomorphic" % least_counts, good)
# a least element maps into every object; check the counts by a second formula:
# a preorder with least element = a top class C of size k >= 1 below everything, plus any preorder on the rest
def cnt_pre(n): return [1, 1, 4, 29, 355][n]
from math import comb
alt = [sum(comb(n, k) * cnt_pre(n - k) for k in range(1, n + 1)) for n in range(1, 5)]
want("least-element counts also equal sum_k C(n,k) * preorders(n-k): %s" % alt, alt == least_counts)

levels = {}
for f in sorted(glob.glob(os.path.join(ROOT, "*", "level.json"))):
    d = json.load(open(f)); levels[d["id"]] = [a for a in d.get("arrows", [])]
nodes = set(levels) | {a["to"] for v in levels.values() for a in v}
E = {(a, a) for a in nodes} | {(k, a["to"]) for k, v in levels.items() for a in v if a.get("status") == "join"}
changed = True
while changed:
    new = {(a, d) for (a, b) in E for (c, d) in E if b == c} - E
    E |= new; changed = bool(new)
least = sorted(a for a in nodes if all((a, b) in E for b in nodes))
need = {a: sorted(b for b in nodes if (a, b) not in E) for a in nodes}
fewest = min(len(v) for v in need.values())
print("  ontology levels %d: %s; join arrows close to %d pairs; least element: %s"
      % (len(nodes), sorted(nodes), len(E), least or "none"))
print("  fewest missing joins for a least element: %d, e.g. from %s"
      % (fewest, sorted((a, need[a]) for a in nodes if len(need[a]) == fewest)[:3]))
want("ontology level preorder computed from level.json join arrows (least element reported, not assumed)", True)

# ---------- 3. time step: settled stays settled ----------
RANK = {"refuted": 0, "open": 1, "premise": 1, "paper": 2, "tested": 2,
        "checked-finite": 3, "checked": 4, "checked-infinite": 4}
def step(store, chk):
    rec, passed = chk
    s = dict(store)
    if passed: s[rec] = True
    elif rec in s: s[rec] = False   # a failing re-check (not allowed in a forward step)
    return s
good = True; seqs = 0
for n in range(1, 5):
    for start in product([False, True], repeat=n):
        st0 = dict(enumerate(start))
        for L in range(0, 5):
            for seq in product(range(n), repeat=L):
                seqs += 1; s = st0
                for r in seq:
                    t = step(s, (r, True))
                    good &= all(t[k] for k in s if s[k]); s = t
want("forward step (only passing checks): settled stays settled; %d (store, order) cases" % seqs, good)
bad = step({0: True}, (0, False))
want("with a failing re-check allowed, a settled record is lost (counterexample {0:T} -> {0:F})", bad[0] is False)

removed = down = versions = superseded = 0; ex = []; pserv = {}
for f in sorted(glob.glob(os.path.join(ROOT, "*", "findings.jsonl"))):
    rel = os.path.relpath(f, ROOT)
    revs = git("rev-list", "--reverse", "HEAD", "--", rel).split()
    prev = None
    for r in revs:
        try: txt = git("show", "%s:%s" % (r, rel))
        except subprocess.CalledProcessError: txt = ""
        cur, serv = {}, {}
        for line in txt.splitlines():
            try:
                d = json.loads(line)
                if "word" in d: cur[d.get("id")] = d["word"]; serv[d.get("id")] = d.get("serves")
            except Exception: pass
        versions += 1
        if prev is not None:
            for k, w in prev.items():
                if k not in cur:
                    rep = [j for j in cur if serv[j] == pserv.get(k) and j not in prev and RANK.get(cur[j], 1) >= RANK.get(w, 1)]
                    if rep:
                        superseded += 1; ex.append((rel, r[:7], k, "superseded by a rerun (same serves, word not lower)"))
                    else:
                        removed += 1; ex.append((rel, r[:7], k, "removed"))
                elif RANK.get(cur[k], 1) < RANK.get(w, 1):
                    down += 1; ex.append((rel, r[:7], k, "%s -> %s" % (w, cur[k])))
        prev, pserv = cur, serv
print("  history (tested): %d versions of findings.jsonl walked; records superseded %d, removed %d, downgraded %d"
      % (versions, superseded, removed, down))
seen = {}
for rel, r, k, what in ex:
    seen.setdefault((rel, r), []).append((k, what))
for (rel, r), v in list(seen.items())[:12]:
    subj = git("log", "-1", "--format=%s", r).strip()
    print("    exception %s %s: %d record(s) %s; commit: %s" % (rel, r, len(v), v[0][1], subj[:90]))

# ---------- 4. Beauvoir: forward-only time has no reciprocity ----------
good = True; npos = 0
for n in range(1, 5):
    for R in preorders(n):
        if all(not ((a, b) in R and (b, a) in R) for a in range(n) for b in range(n) if a != b):
            npos += 1
            nontriv = any(a != b for (a, b) in R)
            sym = all((b, a) in R for (a, b) in R)
            good &= not (nontriv and sym)
want("all %d posets on 1..4 worlds: none with an edge a != b is symmetric" % npos, good and npos == 1 + 3 + 19 + 219)

# ---------- 5. postmodern-safe ----------
def parse(s):
    toks = re.findall(r"\[\]|<>|->|<->|[~&|()]|[a-zT F]", s.replace(" ", ""))
    pos = [0]
    def peek(): return toks[pos[0]] if pos[0] < len(toks) else None
    def eat(): pos[0] += 1; return toks[pos[0] - 1]
    def un():
        t = eat()
        if t in ("~", "[]", "<>"): return (t, un())
        if t == "(":
            e = imp(); eat(); return e
        return ("at", t)
    def conj():
        e = un()
        while peek() == "&": eat(); e = ("&", e, un())
        return e
    def disj():
        e = conj()
        while peek() == "|": eat(); e = ("|", e, conj())
        return e
    def imp():
        e = disj()
        if peek() == "->": eat(); return ("->", e, imp())
        return e
    return imp()
def ev(f, w, R, V, n):
    o = f[0]
    if o == "at": return True if f[1] == "T" else False if f[1] == "F" else w in V
    if o == "~": return not ev(f[1], w, R, V, n)
    if o == "&": return ev(f[1], w, R, V, n) and ev(f[2], w, R, V, n)
    if o == "|": return ev(f[1], w, R, V, n) or ev(f[2], w, R, V, n)
    if o == "->": return (not ev(f[1], w, R, V, n)) or ev(f[2], w, R, V, n)
    if o == "[]": return all(ev(f[1], v, R, V, n) for v in range(n) if (w, v) in R)
    if o == "<>": return any(ev(f[1], v, R, V, n) for v in range(n) if (w, v) in R)
def valid_on(fs, frames):
    f = parse(fs)
    for n, R in frames:
        for m in range(1 << n):
            V = {i for i in range(n) if m >> i & 1}
            if not all(ev(f, w, R, V, n) for w in range(n)): return False
    return True
S4 = [(n, R) for n in range(1, 4) for R in preorders(n)]
S5 = [(n, R) for n, R in S4 if all((b, a) in R for (a, b) in R)]
CLAIMS = [("T", "[]p -> p", True, True), ("4", "[]p -> [][]p", True, True),
          ("B (reciprocity)", "p -> []<>p", False, True), ("5", "<>p -> []<>p", False, True),
          (".2 (rejoining)", "<>[]p -> []<>p", False, True), ("D'", "[]<>T", True, True),
          ("no contradiction", "~(p & ~p)", True, True)]
good = True
for name, fs, s4, s5 in CLAIMS:
    a, b = valid_on(fs, S4), valid_on(fs, S5)
    good &= (a, b) == (s4, s5)
    print("  %-18s %-16s S4 (every branch): %-5s S5 (no privileged world): %s -> %s"
          % (name, fs, a, b, "postmodern-safe" if a and b else "S5-only (needs a frame without direction)"))
want("postmodern-safe table on %d S4 and %d S5 frames (1..3 worlds) as stated" % (len(S4), len(S5)), good)

# ---------- 6. qual-quant of frames_time.ath ----------
EFFECT = ("succeed", "fewer corrections", "cut duplicates")
CONTESTED = ("contested", "song means", "which measure", "history-of-ideas", "fixed idea", "reading")
p = os.path.join(ROOT, "frames_time.ath")
by = {"structure": [0, 0], "effect": [0, 0], "contested": [0, 0]}
if os.path.exists(p):
    for line in open(p):
        m = re.match(r'frame "(.*?)" reading "(.*?)" -> (\S+) label (\S+)', line)
        if not m: continue
        rd, cl = m.group(2).lower(), m.group(3)
        t = ("effect" if any(w in rd for w in EFFECT) else
             "contested" if cl == "none" and any(w in rd for w in CONTESTED) else "structure")
        by[t][0] += 1; by[t][1] += cl != "none"
print("  qual-quant frames_time.ath (type: frames, with a claim): %s" % by)
want("qual-quant types computed for frames_time.ath", os.path.exists(p))

print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
