# consistency check: a base-14 system newly covered by rule p; SAT for a one-NOT circuit of size base-1 = 13 (h0 not assumed)
import sys
from satgen import solve
sets=[[2,3,6,7],[0,3,4],[0,5,6],[1,2,4],[1,5,7],[0,1],[0,2],[1,3]]
res,out,t,ncl=solve(8,sets,13,tmax=230,h0=False)
print('system',sets,'s=13 base=14 result',res,'sec %.1f'%t,'clauses',ncl,flush=True)
if out: print(out)
