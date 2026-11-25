import sys; sys.path.insert(0,'.')
from tw import *
H=Counter()
for f in sys.argv[1:]:
    for c in load(f):
        if max(len(s) for s in c['sets'])<3: continue
        Dc,Dr=worlds(c); ok,got,need=twoworld(c,Dc,Dr); H['n']+=1; H['tw']+=ok; H['union']+=unionhall(c,Dc,Dr)
        dem=[len(s)-1 for s in c['sets']]
        H['canonHall']+= bmatch(Dc,dem,1)==sum(dem); H['rHall']+=bmatch(Dr,dem,1)==sum(dem)
        if not ok: print('TWFAIL',f,got,need,json.dumps(c))
print(dict(H))
