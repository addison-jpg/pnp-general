import sys
sys.path.insert(0,'../fa')
from lib import load
from kill import restr
tot=bad=0
for f in sys.argv[1:]:
    for c in load(f):
        if c['n']>10: continue
        s=len(c['gates'])
        for v in range(c['n']):
            thr=[w for w in c['sets'] if v in w]
            if not thr or sum(len(w)>=3 for w in thr)>1: continue
            tot+=1
            if s-restr(c,v,0)<len(thr): bad+=1; print('R0 VIOL',f,v)
            if all(len(w)==2 for w in thr) and s-restr(c,v,1)<len(thr): bad+=1; print('R0b VIOL',f,v)
print('R0 instances',tot,'violations',bad)
