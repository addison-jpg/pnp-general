# For saved BAD circuits: does an all-type-A disjoint choice exist, or is type B needed?  python3 needsB.py FILES...
import sys, os, json
files = sys.argv[1:]; sys.argv = ['x']
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lib'))
import gapg_check as GC
def choice(c, allowB):
    m = len(c['sets']); opts = [[o for o in GC.systems(c, wi) if allowB or o[0] == 'A'] for wi in range(m)]
    if any(not o for o in opts): return None
    opts = [sorted({o[2]: o for o in os}.values(), key=lambda o: len(o[2])) for os in opts]
    def rec(i, used):
        if i == m: return []
        for o in opts[i]:
            if not (o[2] & used):
                r = rec(i + 1, used | o[2])
                if r is not None: return [o] + r
        return None
    return rec(0, frozenset())
tot = withA = withAB = none = 0; exB = []
for f in files:
    for l in open(f):
        c = json.loads(l); tot += 1
        a = choice(c, False)
        if a: withA += 1; continue
        b = choice(c, True)
        if b:
            withAB += 1
            if len(exB) < 3: exB.append((c, [(o[0], o[1], sorted(o[2])) for o in b]))
        else: none += 1; print('NO-CHOICE', json.dumps(c))
print(f'BAD circuits {tot}: all-A disjoint choice {withA}; needs type B {withAB}; no choice {none}')
for c, sol in exB: print('NEEDS-B', json.dumps(c), 'choice', sol)
