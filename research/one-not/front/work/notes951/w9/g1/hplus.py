import sys, json
from satgen import *
name=sys.argv[1]; nn=int(sys.argv[2]); cv=[int(x) for x in sys.argv[3].split(',')]; n,sets=SYS[name]
b=sum(len(S)-1 for S in sets)
for s in range(b,b+int(sys.argv[4])+1):
    res,out,t,ncl=solve(n,sets,s,tmax=240,readcap=1 if False else 99,nnot=nn,capvars=cv,h0=False)
    print(name,'nnot',nn,'single-reader vars',cv,'s',s,'base',b,res,'%.1fs'%t,flush=True)
    if res: print(json.dumps(out)); break
    if res is None: break
