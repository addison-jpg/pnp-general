"""Two loops bound to each other's end (~ATH reading; source: ontology/SOURCES.md). Standard library only.

System: A halts <-> B halts, and B halts <-> A halts. Enumerate all 4 assignments exactly.
Consistent outcomes: exactly 2 fixed points, both halt or neither halts. The system alone does not
choose between them. Contrast: one loop bound to an external death d (A halts <-> d): for each
value of d exactly one outcome, fixed from outside.
Reading (not checked): the double loop is a catch-22: nothing inside it can start the ending.
"""
from itertools import product
ok = True
def want(name, cond):
    global ok
    print(("ok   " if cond else "FAIL ") + name); ok = ok and cond
two = [(a, b) for a, b in product([False, True], repeat=2) if (a == b) and (b == a)]
want("two loops bound to each other: exactly 2 consistent outcomes, both or neither", two == [(False, False), (True, True)])
one = {d: [a for a in (False, True) if a == d] for d in (False, True)}
want("one loop bound to an external death: exactly 1 outcome for each value of d", one == {False: [False], True: [True]})
# a loop bound to its own non-termination (A halts <-> not A halts) has no consistent outcome
want("a loop bound to its own negation: 0 outcomes", [a for a in (False, True) if a == (not a)] == [])
print("PASS" if ok else "FAIL")
