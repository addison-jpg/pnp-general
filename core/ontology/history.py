"""History as a tree vs a DAG with rejoining, in modal logic S4. Standard library only.

Question (sync 2): which modal formulas tell a branching history (a rooted tree) from one whose
branches rejoin (a rooted partial order that is not a tree)?
Honest answer, checked on every rooted partial order on 1..4 worlds (reflexive, transitive,
antisymmetric, with a least world):
- Every such order is a p-morphic image of a finite tree: its unravelling (paths of covers from the
  root, ordered by prefix) maps onto it, and the forth and back conditions hold exactly.
- So at a world, no formula tells the DAG from its unravelled tree (bisimulation invariance;
  Blackburn, de Rijke, Venema 2001, Prop. 2.14 and Thm 3.14; cited, not re-read). Checked here for
  a list of formulas and every valuation of one atom.
- Frame validity goes one way: what is valid on the tree is valid on the DAG. A single frame can
  differ: axiom .2 "<>[]p -> []<>p" holds on the diamond and fails on its unravelling.
- But "being a tree" is not modally definable: a definable class is closed under p-morphic images
  (Goldblatt-Thomason), and the diamond is an image of a tree. Finite trees and finite rooted posets
  have the same modal logic (S4Grz; cited, not re-read).
"""
from itertools import product

ok = True
def want(name, cond):
    global ok
    print(("ok   " if cond else "FAIL ") + name); ok = ok and cond

def posets(n):
    pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
    for bits in product([0, 1], repeat=len(pairs)):
        R = {(i, i) for i in range(n)} | {p for p, b in zip(pairs, bits) if b}
        if any((j, i) in R for (i, j) in R if i != j): continue
        if any((i, k) not in R for (i, j) in R for (j2, k) in R if j == j2): continue
        if all((0, i) in R for i in range(n)): yield R   # root fixed at 0 (up to relabelling)

def is_tree(n, R):
    return all((a, b) in R or (b, a) in R for x in range(n) for a in range(n) for b in range(n)
               if (a, x) in R and (b, x) in R)

def unravel(n, R):
    cover = {(i, j) for (i, j) in R if i != j and not any((i, k) in R and (k, j) in R for k in range(n) if k not in (i, j))}
    paths, todo = [], [(0,)]
    while todo:
        p = todo.pop(); paths.append(p)
        todo += [p + (j,) for (i, j) in cover if i == p[-1]]
    T = {(a, b) for a in range(len(paths)) for b in range(len(paths)) if paths[b][:len(paths[a])] == paths[a]}
    f = [p[-1] for p in paths]
    return len(paths), T, f

def ev(fm, R, n, V):  # fm: nested tuples; returns set of worlds
    op = fm[0]
    if op == "p": return set(V)
    if op == "T": return set(range(n))
    if op == "~": return set(range(n)) - ev(fm[1], R, n, V)
    if op == "&": return ev(fm[1], R, n, V) & ev(fm[2], R, n, V)
    if op == "->": return (set(range(n)) - ev(fm[1], R, n, V)) | ev(fm[2], R, n, V)
    s = ev(fm[1], R, n, V)
    if op == "[]": return {w for w in range(n) if all(v in s for v in range(n) if (w, v) in R)}
    if op == "<>": return {w for w in range(n) if any(v in s for v in range(n) if (w, v) in R)}

p = ("p",); B = lambda x: ("[]", x); D = lambda x: ("<>", x); I = lambda a, b: ("->", a, b)
FORMS = {"T": I(B(p), p), "4": I(B(p), B(B(p))), "B": I(p, B(D(p))), "5": I(D(p), B(D(p))),
         ".2": I(D(B(p)), B(D(p))), ".3-ish <>[]p": D(B(p)), "[]<>p": B(D(p)), "Grz": I(B(I(B(I(p, B(p))), p)), p)}

count = trees = dags = 0; pmorph = local = True; oneway = True
for n in range(1, 5):
    for R in posets(n):
        count += 1
        if is_tree(n, R): trees += 1
        else: dags += 1
        m, T, f = unravel(n, R)
        forth = all((f[a], f[b]) in R for (a, b) in T)
        back = all(any((a, b) in T and f[b] == w for b in range(m)) for a in range(m) for w in range(n) if (f[a], w) in R)
        onto = set(f) == set(range(n))
        pmorph &= forth and back and onto
        for bits in product([0, 1], repeat=n):
            V = [w for w in range(n) if bits[w]]; VT = [a for a in range(m) if f[a] in V]
            for fm in FORMS.values():
                sR, sT = ev(fm, R, n, V), ev(fm, T, m, VT)
                local &= all((a in sT) == (f[a] in sR) for a in range(m))
        for fm in FORMS.values():
            vT = all(ev(fm, T, m, [a for a in range(m) if bt[a]]) == set(range(m)) for bt in product([0, 1], repeat=m))
            vR = all(ev(fm, R, n, [w for w in range(n) if bt[w]]) == set(range(n)) for bt in product([0, 1], repeat=n))
            oneway &= (not vT) or vR
want(f"{count} rooted posets on 1..4 worlds (root 0): {trees} trees, {dags} with rejoining", count == trees + dags and dags > 0)
want("each is a p-morphic image of its unravelled tree (forth, back, onto)", pmorph)
want(f"every world agrees with its unravelled copies on {len(FORMS)} formulas, every valuation", local)
want("frame validity: valid on the tree implies valid on the DAG", oneway)
dia = {(i, i) for i in range(4)} | {(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)}
m, T, f = unravel(4, dia)
v = lambda R, n: all(ev(FORMS[".2"], R, n, [w for w in range(n) if b[w]]) == set(range(n)) for b in product([0, 1], repeat=n))
want(".2 valid on the diamond, invalid on its unravelling (5 worlds)", v(dia, 4) and not v(T, m) and m == 5)
print("PASS" if ok else "FAIL")
