#!/usr/bin/env python3
"""A joint table is not determined by its margins (Crenshaw 1989, read as a formal hook; cited from memory).

Checked-finite, every 2x2 table of nonnegative integers with total N <= 12 (nothing sampled):
  1. Group tables by their margins (row 1 total, column 1 total, N). Count each class and find the largest.
  2. Frechet bounds: in each class the corner cell takes exactly the integers max(0, r + c - N) .. min(r, c).
Reading (analogy, not checked): counting "race" and "sex" separately (the margins) does not fix who stands
at the joint (the cell). Du Bois's one-way gaze is checked elsewhere: core/ontology/asymmetry.py.
Run: python3 -I culture/race/race.py   (last line is JSON)
"""
import json, time
t0 = time.time(); classes = {}; tables = 0
for N in range(13):
    for a in range(N + 1):
        for b in range(N + 1 - a):
            for c in range(N + 1 - a - b):
                tables += 1; classes.setdefault((a + b, a + c, N), set()).add(a)
for (r, c, N), corner in classes.items():
    assert corner == set(range(max(0, r + c - N), min(r, c) + 1)), "Frechet"
size = {k: len(v) for k, v in classes.items()}; big = max(size.values())
ambiguous = sum(s > 1 for s in size.values())
assert tables == 1820 and len(classes) == 819 and big == 7 and [k for k, s in size.items() if s == big] == [(6, 6, 12)]
print(f"{tables} tables with N <= 12 fall into {len(classes)} margin classes; {ambiguous} classes hold more than one table")
print(f"largest class: {big} tables, margins (6, 6) with N = 12; the corner cell ranges over 0..6")
print("Frechet bounds max(0, r + c - N) <= a <= min(r, c) are exact in every class")
print("PASS")
print(json.dumps({"states": tables, "seconds": round(time.time() - t0, 2), "classes": len(classes), "ambiguous": ambiguous, "largest": big}))
