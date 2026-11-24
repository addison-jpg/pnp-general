from wl import *
import time
cs=[(n,c) for n,c in allcirc() if c['n']>7]+extra()
print(len(cs))
for name,c in cs:
    if not any(g[0]=='not' for g in c['gates']): print('noNOT',name); continue
    if c['n']>12 and 'T4' not in name: print('big',name,c['n']); continue
    t=time.time(); r=run(name,c)
    print(name,c['n'],r,round(time.time()-t,1),flush=True)
