"""Beauvoir sync: "my freedom requires the other's" as a frame condition. Standard library only.

Checked on every relation on 1..3 worlds and every valuation of the atom set needed:
- []<>T is valid on a frame iff every world reached from any world reaches something
  (successors are serial): forall x,y (xRy -> exists z yRz).
- <>T is valid iff the frame is serial (axiom D).
- Serial implies successor-serial; not conversely (a dead-end world that reaches nothing
  makes []<>T vacuously true there while <>T fails).
Reading (not checked): whatever I can reach must itself be able to go on; freedom that ends
the other's going on is not what []<>T asks. Cited, read status: The Ethics of Ambiguity
(Pour une morale de l'ambiguite, 1947) and The Second Sex (Le Deuxieme Sexe, 1949): not
re-read for this sync; the link is analogy.
"""
from itertools import product
ok = True
def want(name, cond):
    global ok
    print(("ok   " if cond else "FAIL ") + name); ok = ok and cond
good = True; frames = 0; gap = 0
for n in range(1, 4):
    pairs = [(i, j) for i in range(n) for j in range(n)]
    for bits in product([0, 1], repeat=len(pairs)):
        R = {p for p, b in zip(pairs, bits) if b}; frames += 1
        succ = lambda w: [v for v in range(n) if (w, v) in R]
        box_dia_T = all(all(succ(v) for v in succ(w)) for w in range(n))     # truth of []<>T everywhere
        succ_serial = all(any((y, z) in R for z in range(n)) for (x, y) in R)
        dia_T = all(succ(w) for w in range(n)); serial = all(any((x, y) in R for y in range(n)) for x in range(n))
        good &= box_dia_T == succ_serial and dia_T == serial and (not serial or succ_serial)
        gap += succ_serial and not serial
want(f"[]<>T defines successor-seriality and <>T seriality on all {frames} frames on 1..3 worlds", good and frames == 2 + 16 + 512)
want(f"successor-serial but not serial: {gap} frames (the converse fails)", gap > 0)
print("PASS" if ok else "FAIL")
