import pickle,itertools,sys
sys.path.insert(0,'.')
from lib import *
from sig import down
res=pickle.load(open('xplus.pkl','rb')); sigs=pickle.load(open('sigs.pkl','rb'))
for s,(X,P,ch) in res.items():
    if X: continue
    n,sets,tt,isN=s
    mint=[]
    for r in range(n+1):
        for M in itertools.combinations(range(n),r):
            x=[1 if v in M else 0 for v in range(n)]
            if tt[int(''.join(map(str,x)),2)] and not any(set(m)<=set(M) for m in mint): mint.append(M)
    c=sigs[s]; ok,c0,c1=verify(c)
    print('n',n,'sets',sets,'minterms',mint,'isN',isN,'X+',P,'| circ ok',ok,'C0w',c0,'C1w',c1,'s',len(c['gates']))
    if P:
        d=down(c); cn=[]
        for S,o in zip(sets,ch):
            Q,z1,mono,at=o
            atoms={}
            for p,hv in at:
                u=[v for v in p if v in S][0]; atoms[u]=[1 if v in p else 0 for v in range(n)]
            good,wz,B=system(c,S,zQ(n,Q),atoms)
            assert good or mono
            cnt={i for i,b in B.items() if i>=n and len(b)>=2 and not (mono and i in d)}
            cn.append(cnt)
            print('   ',S,'Q',sorted(Q),'zU1',z1,'mono',mono,'atoms',[sorted(p) for p,_ in at],'cnt',sorted(cnt))
        tot=sum(map(len,cn)); un=len(set().union(*cn))
        print('   disjoint',tot==un,'all >= d',all(len(x)>=len(S)-1 for x,S in zip(cn,sets)))
    else: print(json.dumps(c))
