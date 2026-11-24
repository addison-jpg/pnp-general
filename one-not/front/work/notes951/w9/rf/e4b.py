import sys,json,ess,time
n=int(sys.argv[1]); sets=json.loads(sys.argv[2]); ex=int(sys.argv[3]); ma=None if sys.argv[4]=='-' else int(sys.argv[4]); tm=int(sys.argv[5])
base=sum(len(S)-1 for S in sets)
res,out,t=ess.solve(n,sets,base+ex,tmax=tm,clean=False,maxand=ma)
print('n',n,sets,'base',base,'s',base+ex,'maxand',ma,'res',res,'sec %.0f'%t,flush=True)
if out: print(json.dumps(out))
