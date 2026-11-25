"""front request 11:36: extract (a) Hall-tight families with |F| >= 2 and restricted slack 1, (b) circuits whose whole
system is Hall-tight. For each: circuit, F, restricted gate count, and the pure options of the restriction that are
NOT pure options of the original. Options are compared by FUNCTION on the restricted cube (x_v = 0 for v off ∪F):
a restricted option {g'} is 'new' when no original option {g} of the same set has g's table equal to g''s table there."""
import json, sys
sys.path.insert(0, '.')
import hallgraph as HG
import pure_export as PE
from w951 import Circuit

def opt_tables(c, opts, cube):
    return [{c.table(next(iter(M))) & cube for M in o} for o in opts]

def analyse(d, F):
    c = Circuit.from_dict(d); keep = {v for w in F for v in c.sets[w]}
    cube = sum(1 << x for x in range(1 << c.n) if all(not (x >> v & 1) for v in range(c.n) if v not in keep))
    c2 = HG.restrict_to(c, F)
    if len(c2.nots) != 1:
        return dict(F=list(F), s_restr=c2.s, base_F=len(F), restricted=c2.to_dict(), restricted_nots=len(c2.nots),
                    new_options=None, note='restriction has no NOT gate (monotone): pure menus undefined')
    _, _, _, _, o1 = PE.menus(d); _, _, _, _, o2 = PE.menus(c2.to_dict())
    T1 = opt_tables(c, o1, cube); T2 = opt_tables(c2, o2, cube)
    new = []
    for j, w in enumerate(F):
        for M in o2[j]:
            g = next(iter(M))
            if (c2.table(g) & cube) not in T1[w]: new.append({'set': w, 'restricted_gate': g, 'restricted_op': c2.gates[g - c2.n]})
    return dict(F=list(F), s_restr=c2.s, base_F=len(F), restricted=c2.to_dict(),
                menu_sizes_orig=[len(o1[w]) for w in F], menu_sizes_restr=[len(o) for o in o2], new_options=new)

src = {}
import harness as H
for t, c in H.corpora():
    src.setdefault(t, c.to_dict())
R = [json.loads(l) for l in open('hall.jsonl')]; R = [r for r in R if 'err' not in r]
A, B = [], []
for r in R:
    d = src[r['tag']]
    for t in r['tight']:
        if len(t['F']) >= 2 and t['slack'] == 1: A.append(dict(tag=r['tag'], n=r['n'], s=r['s'], base=r['base'], ess=r['ess'], circuit=d, **analyse(d, t['F'])))
    if any(len(t['F']) == r['m'] for t in r['tight']):
        B.append(dict(tag=r['tag'], n=r['n'], s=r['s'], base=r['base'], ess=r['ess'], circuit=d, **analyse(d, tuple(range(r['m'])))))
json.dump(A, open('slack1_tight.json', 'w')); json.dump(B, open('whole_tight.json', 'w'))
print('slack-1 families:', len(A), 'monotone restriction:', sum(a['new_options'] is None for a in A), 'with new options:', sum(bool(a['new_options']) for a in A))
print('whole-tight circuits:', len(B), 'monotone restriction:', sum(b['new_options'] is None for b in B), 'with new options:', sum(bool(b['new_options']) for b in B))
