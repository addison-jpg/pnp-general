"""math/language/: what can be proved of language, exactly. Standard library only. Integers and sets.

Parts (see math/language/BASE.md):
 a. Chomsky hierarchy. Every DFA with 1..3 states over {a,b}: its language up to length 8.
    No such DFA agrees with a^n b^n on all strings of length <= 8. The largest first-disagreement
    length over k-state DFAs is computed and checked <= 2k-1 (the written reduction in BASE.md).
    Two CFGs: S -> aSb | e (a^n b^n) and S -> (S)S | e (balanced parentheses). Exact counts by length,
    by the grammar and by brute force over all strings; each string has exactly one parse tree.
 b. Ambiguity counted. E -> E+E | E*E | x: parse trees of every sentence with n operators, by explicit
    enumeration of trees and by a chart count; equal to Catalan(n). The precedence grammar
    E -> E+T | T, T -> T*F | F, F -> x gives exactly 1 parse for every sentence.
 c. A Montague fragment. "Q1 N1 V Q2 N2", Q in {every, some}. Two readings (surface and inverse scope),
    evaluated on every model with domain size 1..3 and every interpretation of the predicates.
 d. Joins. Parse-tree shapes with n+1 leaves are exactly the ordered binary arbor shapes of
    biology/brain/neuron (Catalan). Ambiguity as a count: readings per sentence.
Writes math/language/fingerprints.json. Prints PASS when every check holds.
"""
import json, os, sys
from itertools import product
from math import comb

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ok = True
def want(name, cond):
    global ok
    print(("ok   " if cond else "FAIL ") + name)
    ok = ok and bool(cond)

def catalan(n): return comb(2 * n, n) // (n + 1)

# ---------- a. regular languages: every DFA with <= 3 states ----------
L = 8
strings = [""]                       # all strings over {a,b} of length <= L, in length order
for n in range(1, L + 1): strings += ["".join(p) for p in product("ab", repeat=n)]
idx = {s: i for i, s in enumerate(strings)}
parent = [None] + [idx[s[:-1]] for s in strings[1:]]
last = [None] + [0 if s[-1] == "a" else 1 for s in strings[1:]]
anbn = [s == "a" * (len(s) // 2) + "b" * (len(s) // 2) and len(s) % 2 == 0 for s in strings]

langs_upto = {}
maxfirst = {}
anbn_hits = 0
seen = set()
for k in (1, 2, 3):
    worst = -1
    for delta in product(range(k), repeat=2 * k):          # delta[2q + c]
        st = [0] * len(strings)
        for i in range(1, len(strings)): st[i] = delta[2 * st[parent[i]] + last[i]]
        for acc in range(1 << k):
            mask = 0
            first = None
            for i, q in enumerate(st):
                a = (acc >> q) & 1
                if a: mask |= 1 << i
                if first is None and bool(a) != anbn[i]: first = len(strings[i])
            seen.add(mask)
            if first is None: anbn_hits += 1
            else: worst = max(worst, first)
    langs_upto[k] = len(seen)
    maxfirst[k] = worst
print("distinct languages (restricted to length <= 8) of DFAs with <= k states, k=1..3:", [langs_upto[k] for k in (1, 2, 3)])
print("largest first-disagreement length with a^n b^n, k=1..3:", [maxfirst[k] for k in (1, 2, 3)])
want("no DFA with <= 3 states over {a,b} agrees with a^n b^n on all 511 strings of length <= 8", anbn_hits == 0)
want("every k-state DFA (k=1..3) disagrees with a^n b^n at some length <= 2k-1 (Myhill-Nerode reduction)",
     all(maxfirst[k] <= 2 * k - 1 for k in (1, 2, 3)))

# CFGs: count by the grammar (a DP over derivations) and by brute force
def lang_anbn(n):            # S -> aSb | e: strings of length n generated, with parse counts
    out = {}
    def gen(m):              # strings of length m from S, each with its number of derivations
        if m == 0: return {"": 1}
        if m < 2: return {}
        return {"a" + s + "b": c for s, c in gen(m - 2).items()}
    return gen(n)
def lang_dyck(n, memo={}):   # S -> (S)S | e
    if n in memo: return memo[n]
    if n == 0: r = {"": 1}
    else:
        r = {}
        for i in range(0, n - 1):
            for s, c in lang_dyck(i).items():
                for t, d in lang_dyck(n - 2 - i).items():
                    w = "(" + s + ")" + t; r[w] = r.get(w, 0) + c * d
    memo[n] = r; return r
def balanced(w):
    h = 0
    for ch in w:
        h += 1 if ch == "(" else -1
        if h < 0: return False
    return h == 0
NB = 16
anbn_counts = [len(lang_anbn(n)) for n in range(NB + 1)]
dyck_counts = [len(lang_dyck(n)) for n in range(NB + 1)]
want("S -> aSb | e: one string at each even length, none at odd, n=0..16, each with one parse",
     anbn_counts == [1 - n % 2 for n in range(NB + 1)] and all(c == 1 for n in range(NB + 1) for c in lang_anbn(n).values())
     and all(set(lang_anbn(n)) == {w for w in ("".join(p) for p in product("ab", repeat=n)) if w == "a" * (n // 2) + "b" * (n // 2) and n % 2 == 0} for n in range(13)))
brute = [sum(balanced("".join(p)) for p in product("()", repeat=n)) for n in range(NB + 1)]
want("S -> (S)S | e generates exactly the balanced strings, n=0..16 (brute force over all 2^n strings)",
     all(set(lang_dyck(n)) == {"".join(p) for p in product("()", repeat=n) if balanced("".join(p))} for n in range(13)) and dyck_counts == brute)
want("balanced parentheses of length 2m number Catalan(m), m=0..8; each has one parse tree (unambiguous)",
     dyck_counts[0::2] == [catalan(m) for m in range(9)] and all(c == 1 for n in range(NB + 1) for c in lang_dyck(n).values()))

# ---------- b. ambiguity counted ----------
def trees(lo, hi, toks):     # every parse tree of toks[lo..hi] under E -> E+E | E*E | x
    if lo == hi: return ["x"] if toks[lo] == "x" else []
    out = []
    for k in range(lo + 1, hi, 2):
        if toks[k] in "+*":
            for l in trees(lo, k - 1, toks):
                for r in trees(k + 1, hi, toks): out.append((toks[k], l, r))
    return out
def chart_amb(toks):
    n = len(toks); C = {}
    for i in range(0, n, 2): C[i, i] = 1
    for span in range(2, n, 2):
        for i in range(0, n - span, 2):
            j = i + span; C[i, j] = sum(C[i, k - 1] * C[k + 1, j] for k in range(i + 1, j, 2))
    return C[0, n - 1]
def chart_prec(toks):        # E -> E+T | T ; T -> T*F | F ; F -> x : number of parse trees
    n = len(toks); F = {}; T = {}; E = {}
    for span in range(0, n, 2):
        for i in range(0, n - span, 2):
            j = i + span
            F[i, j] = 1 if span == 0 and toks[i] == "x" else 0
            T[i, j] = F[i, j] + sum(T[i, k - 1] * F[k + 1, j] for k in range(i + 1, j, 2) if toks[k] == "*")
            E[i, j] = T[i, j] + sum(E[i, k - 1] * T[k + 1, j] for k in range(i + 1, j, 2) if toks[k] == "+")
    return E[0, n - 1]
NOPS = 8
amb_by_n, prec_ok, enum_ok = [], True, True
for n in range(NOPS + 1):
    counts = set()
    for ops in product("+*", repeat=n):
        toks = ["x"]
        for o in ops: toks += [o, "x"]
        c = chart_amb(toks)
        if n <= 6:
            ts = trees(0, len(toks) - 1, toks)
            enum_ok = enum_ok and len(ts) == c and len(set(ts)) == len(ts)
        counts.add(c)
        prec_ok = prec_ok and chart_prec(toks) == 1
    amb_by_n.append(sorted(counts))
want("E -> E+E | E*E | x: every sentence with n operators has Catalan(n) parse trees, n=0..8 (all 2^n sentences)",
     all(amb_by_n[n] == [catalan(n)] for n in range(NOPS + 1)))
want("the chart count equals explicit enumeration of distinct trees, n=0..6", enum_ok)
want("precedence grammar E -> E+T | T, T -> T*F | F, F -> x: exactly 1 parse for every sentence, n=0..8", prec_ok)

# ---------- c. Montague fragment ----------
def ev(q1, n1, q2, n2, M, inverse):
    D, P, R = M
    def inner(x):            # surface: Q1 x (N1 x, Q2 y (N2 y, V x y))
        ys = [y for y in D if y in P[n2]]
        return all((x, y) in R for y in ys) if q2 == "every" else any((x, y) in R for y in ys)
    if not inverse:
        xs = [x for x in D if x in P[n1]]
        return all(inner(x) for x in xs) if q1 == "every" else any(inner(x) for x in xs)
    ys = [y for y in D if y in P[n2]]
    def inner2(y):
        xs = [x for x in D if x in P[n1]]
        return all((x, y) in R for x in xs) if q1 == "every" else any((x, y) in R for x in xs)
    return all(inner2(y) for y in ys) if q2 == "every" else any(inner2(y) for y in ys)
def models(d):
    D = list(range(d)); pairs = [(x, y) for x in D for y in D]
    subs = [frozenset(x for x in D if (m >> x) & 1) for m in range(1 << d)]
    for s in subs:
        for b in subs:
            for rm in range(1 << len(pairs)):
                yield D, {"student": s, "book": b}, frozenset(p for i, p in enumerate(pairs) if (rm >> i) & 1)
nmodels = [0, 0, 0]
sent = ("every", "student", "some", "book")
differ = []; implies = True; first_cm = None; first_cm_nonempty = None
readings = {}
QS = ("every", "some")
for d in (1, 2, 3):
    for M in models(d):
        nmodels[d - 1] += 1
        s, i = ev(*sent, M, False), ev(*sent, M, True)
        if i and not s: implies = False
        if s and not i:
            if first_cm is None: first_cm = M
            if first_cm_nonempty is None and M[1]["student"] and M[1]["book"]: first_cm_nonempty = M
        for q1 in QS:
            for q2 in QS:
                a, b = ev(q1, "student", q2, "book", M, False), ev(q1, "student", q2, "book", M, True)
                readings.setdefault((q1, q2), set()).add((a, b))
def showm(M):
    D, P, R = M
    return f"domain {D}, student {sorted(P['student'])}, book {sorted(P['book'])}, reads {sorted(R)}"
print("models with domain size 1, 2, 3:", nmodels)
print("smallest model where the surface reading is true and the inverse false:", showm(first_cm))
print("smallest such model with students and books non-empty:", showm(first_cm_nonempty))
want("'every student reads some book': the two readings differ on some model of size <= 3", first_cm is not None)
want("the inverse reading (some book read by every student) implies the surface one on all 33032 models", implies and sum(nmodels) == 8 + 256 + 32768)
nread = {k: (2 if any(a != b for a, b in v) else 1) for k, v in readings.items()}
print("distinct readings per quantifier pattern (Q1, Q2):", nread)
want("same quantifiers (every..every, some..some): one reading; mixed: two", nread == {("every", "every"): 1, ("some", "some"): 1, ("every", "some"): 2, ("some", "every"): 2})
sm = all(not (a and not b) for a, b in readings[("some", "every")])   # surface ∃∀ implies inverse ∀∃
want("'some student reads every book': the surface reading implies the inverse on every model", sm)

# ---------- d. joins ----------
TIP = "t"
ordered = {1: [TIP]}
for n in range(2, 10): ordered[n] = [(l, r) for k in range(1, n) for l in ordered[k] for r in ordered[n - k]]
def shape(t): return TIP if t == "x" else (shape(t[1]), shape(t[2]))
same = True
for n in range(0, 7):
    toks = ["x"] + ["+", "x"] * n
    same = same and sorted(map(repr, (shape(t) for t in trees(0, len(toks) - 1, toks)))) == sorted(map(repr, ordered[n + 1]))
want("parse trees of x+x+...+x with n+1 leaves, operators erased, are exactly the ordered binary arbor shapes with n+1 tips (biology/brain/neuron), n=0..6", same)
brain = json.load(open(os.path.join(ROOT, "brain", "neuron", "fingerprints.json"), encoding="utf-8"))
bcat = next(e["seq"] for e in brain if "Catalan" in e["name"])
parses_by_leaves = [catalan(n) for n in range(NOPS + 1)]
want("parse-tree counts by leaves equal biology/brain/neuron's Catalan fingerprint on the common prefix", parses_by_leaves[:len(bcat)] == bcat[:len(parses_by_leaves)])

RUN = "python3 -I math/language/check.py"
fp = [
    {"name": "parse trees of x op x ... op x with n leaves under E -> E+E | E*E | x, n=1..9 (Catalan)", "seq": parses_by_leaves, "runner": RUN},
    {"name": "balanced parentheses of length 2m, m=0..8 (Catalan)", "seq": dyck_counts[0::2], "runner": RUN},
    {"name": "distinct languages up to length 8 of DFAs with <= k states over {a,b}, k=1..3", "seq": [langs_upto[k] for k in (1, 2, 3)], "runner": RUN},
    {"name": "largest first disagreement with a^n b^n over k-state DFAs, k=1..3", "seq": [maxfirst[k] for k in (1, 2, 3)], "runner": RUN},
]
with open(os.path.join(ROOT, "language", "fingerprints.json"), "w", encoding="utf-8") as f:
    f.write("[\n" + ",\n".join(" " + json.dumps(e) for e in fp) + "\n]\n")
print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
