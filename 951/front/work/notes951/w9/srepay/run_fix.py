import sys, json
from satfix import *
# args: prefixname k_list tmax nsol clean(0/1) outfile
name=sys.argv[1]; ks=[int(v) for v in sys.argv[2].split(',')]; tmax=int(sys.argv[3]); nsol=int(sys.argv[4]); clean=bool(int(sys.argv[5])); outf=sys.argv[6]
PFX={'P1':[[0,1],[2,3],[4,5],[6,7]], 'P2':[[0,4],[1,5],[2,6],[3,7]], 'P3':[[0,1],[4,5],[2,6],[3,7]]}
pre,hw=th2_tree(PFX[name])
sets=[[0,1,2,3],[4,5,6,7]]
fo=open(outf,'a')
for k in ks:
    st,sols,t=solve(8,sets,pre,hw,k,tmax=tmax,nsol=nsol,clean=clean,outs_pre=True,fo=fo)
    print(name,'clean',clean,'k',k,'s',len(pre)+1+k,st,len(sols),'sec %.1f'%t,flush=True)
    if st=='SAT' or st=='EXHAUSTED': break
