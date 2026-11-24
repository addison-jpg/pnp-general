import sys,json
sys.path.insert(0,'../g1')
import satgen
unc=[s for t,s in json.load(open('unc8.json')) if t==14]
i=int(sys.argv[1]); s=int(sys.argv[2]); cap=int(sys.argv[3])
sets=unc[i]
res,out,t,ncl=satgen.solve(8,sets,s,tmax=int(sys.argv[4]),readcap=cap)
print(i,sets,'s',s,'cap',cap,'clauses',ncl,'res',res,'sec %.0f'%t,flush=True)
if out: print(json.dumps(out))
