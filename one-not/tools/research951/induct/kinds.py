# Run from the repository root:  python3 one-not/tools/research951/induct/kinds.py <circuit .json files>
import sys, json
L = sys.argv[1:]
src = open('one-not/tools/research951/induct/extend.py').read(); exec(src[:src.index("st = collections.Counter()")])
tot = disj = 0; ex = []
for path in L:
    d = json.load(open(path)); n, S, G = d['n'], d['sets'], d['gates']
    if n > 13: continue
    for w, k in enumerate(kmenus(n, S, G)):
        i1 = [C for C, t in k.items() if t & {'I1', 'I1top'}]; i0 = [C for C, t in k.items() if 'I0' in t]
        if i1 and i0:
            tot += 1
            if all(not (A & B) for A in i1 for B in i0):
                disj += 1; ex.append((path.split('/')[-1], w, S[w], [sorted(A) for A in i1], [sorted(B) for B in i0]))
print('sets with both I1 and I0 classes:', tot, '| every I1 class disjoint from every I0 class:', disj)
for e in ex[:6]: print(' ', e)
