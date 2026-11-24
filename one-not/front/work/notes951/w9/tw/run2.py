import sys; sys.path.insert(0,'.')
from tw import *
H=Counter(); ex=[]
for f in sys.argv[1:]:
    for c in load(f):
        if max(len(s) for s in c['sets'])<3: continue
        Dc,Dr=worlds(c); dem=[len(s)-1 for s in c['sets']]; m=len(dem)
        H['n']+=1
        H['Wc']+= bmatch(Dc,dem,2)==sum(dem); H['Wr']+= bmatch(Dr,dem,2)==sum(dem)
        dc=Counter(g for D in Dc for g in D); dr=Counter(g for D in Dr for g in D)
        bad=[g for g in dc if dr[g] and dc[g]+dr[g]>2]
        H['cross_ok']+= not bad
        # cross between different sets
        xs=[(a,b,g) for a in range(m) for b in range(m) if a!=b for g in set(Dc[a])&set(Dr[b])]
        H['has_cross_ab']+= bool(xs)
        if bad and len(ex)<4: ex.append((f.split('/')[-1],bad,[(g,[w for w in range(m) if g in Dc[w]],[w for w in range(m) if g in Dr[w]]) for g in bad]))
print(dict(H))
for e in ex: print(e)
