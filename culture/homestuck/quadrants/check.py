#!/usr/bin/env python3
"""Troll quadrants as a finite signed model (structural balance), exhaustive on small sets.

Four quadrants label each pair of trolls: matesprit (+), moirail (+), auspistice (+), kismesis (-).
Sign: kismesis is the one negative relation (hate and rivalry); the three others are positive.
A signed graph is balanced (Heider; Cartwright and Harary 1956) exactly when its vertices split into
two camps, positive inside each camp and negative across. Checked two ways on every labelling:
(a) by a parity 2-colouring of the graph, (b) by brute force over all camp splits (n <= 4).
Labels: the four quadrant names and their signs are cited (fanlore.org, pixiv), not reproduced;
the balance theorem is cited, not re-derived here. "Pale" (moirail, auspistice) and "dark" (matesprit,
kismesis) are the user's card-sort split, used only to count sorts; the split is a reading, labelled analogy.
Run: python3 -I culture/homestuck/quadrants/check.py   (last line is JSON)
"""
import itertools, json, time

QUAD = ["matesprit", "moirail", "auspistice", "kismesis"]
SIGN = {"matesprit": 1, "moirail": 1, "auspistice": 1, "kismesis": -1}
PALE = {"moirail", "auspistice"}
DARK = {"matesprit", "kismesis"}

def balanced_parity(n, lab):
    # lab: dict (i,j) -> quadrant, i < j. Balanced iff a 2-colouring c has c[i]==c[j] on positive, != on negative.
    adj = {v: [] for v in range(n)}
    for (i, j), q in lab.items():
        s = SIGN[q]; adj[i].append((j, s)); adj[j].append((i, s))
    col = {}
    for root in range(n):
        if root in col: continue
        col[root] = 0; todo = [root]
        while todo:
            v = todo.pop()
            for w, s in adj[v]:
                want = col[v] if s > 0 else 1 - col[v]
                if w not in col: col[w] = want; todo.append(w)
                elif col[w] != want: return False
    return True

def balanced_brute(n, lab):
    for camp in range(1 << n):
        ok = True
        for (i, j), q in lab.items():
            same = ((camp >> i) & 1) == ((camp >> j) & 1)
            if (SIGN[q] > 0) != same: ok = False; break
        if ok: return True
    return False

def main():
    t0 = time.time(); out = {}; states = 0
    for n in range(2, 6):
        pairs = list(itertools.combinations(range(n), 2)); bal = 0; pale_bal = 0; dark_bal = 0
        for labels in itertools.product(QUAD, repeat=len(pairs)):
            lab = dict(zip(pairs, labels)); states += 1
            b = balanced_parity(n, lab)
            if n <= 4: assert b == balanced_brute(n, lab), "parity and brute force disagree"
            if b:
                bal += 1
                # a card sort: the pale/dark split of the balanced labellings, all of whose labels fall in one split
                if all(q in PALE for q in labels): pale_bal += 1
                if all(q in DARK for q in labels): dark_bal += 1
        out[n] = {"labellings": len(QUAD) ** len(pairs), "balanced": bal, "pale_only": pale_bal, "dark_only": dark_bal}
        print(f"n={n} pairs={len(pairs)} labellings={len(QUAD)**len(pairs)} balanced={bal} pale-only={pale_bal} dark-only={dark_bal}")
    # the balance theorem on the complete graph with only positive edges: every positive labelling is balanced
    all_pos_ok = all(balanced_parity(4, dict(zip(list(itertools.combinations(range(4), 2)), labs)))
                     for labs in itertools.product(["matesprit", "moirail", "auspistice"], repeat=6))
    assert all_pos_ok, "a labelling with no kismesis was not balanced"
    print("no kismesis (all positive) on 4 trolls: always balanced, checked over 3^6 labellings")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 2), "balanced": {str(k): v["balanced"] for k, v in out.items()}}))

if __name__ == "__main__":
    main()
