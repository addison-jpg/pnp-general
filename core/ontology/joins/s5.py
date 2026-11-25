"""Join time + poetry: S5 frames (physics/time/check.py: reflexive, transitive, symmetric) on n worlds are the
equivalence relations, so they are counted by the Bell numbers, the rhyme schemes of culture/poetry. Also S4 frames
(preorders). Every relation on 1..4 worlds."""
import json, os
R = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
s4, s5 = [], []
for n in range(1, 5):
    P = [(a, b) for a in range(n) for b in range(n)]; c4 = c5 = 0
    for mask in range(1 << len(P)):
        Rl = {p for k, p in enumerate(P) if mask >> k & 1}
        if all((a, a) in Rl for a in range(n)) and all((a, c) in Rl for a, b in Rl for b2, c in Rl if b == b2):
            c4 += 1; c5 += all((b, a) in Rl for a, b in Rl)
    s4.append(c4); s5.append(c5)
rhyme = [e for e in json.load(open(os.path.join(R, "culture/poetry/fingerprints.json"))) if "rhyme schemes" in e["name"]][0]["seq"]
assert s4 == [1, 4, 29, 355] and s5 == rhyme[:4] == [1, 2, 5, 15]
assert sum(s4[:3]) == 34 and sum(s5[:3]) == 8                      # the 34 S4 and 8 S5 frames physics/time/check.py uses
print("S4 frames on 1..4 worlds:", s4, "; S5 frames:", s5, "= rhyme schemes of 1..4 lines (Bell)"); print("PASS")
