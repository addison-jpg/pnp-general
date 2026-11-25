import sys,time
from mincost import mincost
k=int(sys.argv[1]); a,b=0,1; n=2+3*k
sets=[]
for i in range(k):
    c,d,e=2+3*i,3+3*i,4+3*i
    sets+= [(a,c,d),(b,c,e)]
hf=lambda x: int(bool(x&3))
t=time.time(); r=mincost(n,sets,hf); print('k',k,'mincost',r[0],time.time()-t)
for i,o in sorted(r[1].items()): print(sets[i],bin(o[0]),o[1],[bin(y) for y,_ in o[2]])
