import sys
from g1lib import *
tot=bad=0
for f in sys.argv[1:]:
    for c in load(f):
        if c['n']>10: continue
        n=c['n']; T=tts(c); full=(1<<(1<<n))-1
        for v in range(n):
            R=readers(c,v)
            if deg(c,v)<2 or len(R)!=1: continue
            g=c['gates'][R[0]-n]
            if g[0]=='not' or g[1]==g[2]: continue
            cw=g[1] if g[2]==v else g[2]; tot+=1
            for S in c['sets']:
                if v not in S: continue
                o=0
                for u in S:
                    if u!=v: o|=T[u]
                if g[0]=='or' and (T[cw]&~o&full): bad+=1
                if g[0]=='and' and ((full^T[cw])&~o&full): bad+=1
            if cw<n: bad+=1
print('single-reader instances',tot,'AL violations',bad)
