# Witnesses against the F2 STEP at NON-LOCAL cubes (fable-f2-nonlocal): the NOT input h depends on >= 2 inputs at Q = empty.
# python3 -I one-not/tools/kill_tests/f2_nonlocal_build.py [outdir]     (writes the witnesses when outdir is given)
# Variants of TWIN-TREE-N (k = 3, n = 14):  OR2: h = x0 v x8;  E0: h = x1 v x8 (= output gate of P_0, both outputs use the NOT);
#   AND2: h = x8 ^ x10;  MAJ3: h = MAJ(x8,x10,x12).
# MATCH(k): A = {0..k-1, y=k}, B = {k+1..2k, y'=2k+1}, P_i = {i, k+1+i}; f_A = OR-tree of p_i = x_i v (x_y ^ x_{k+1+i}),
#   f_B likewise, h = f_A v f_B (= OR of all 2k matched points), N = NOT h, o_A = ((x_y v L) ^ N) v f_A, o_B likewise;
#   cone=True (MATCH-C): the output of P_i is p_i v p'_i (same function), so both junk leaves are in its cone.
#   leak L = f_B ('f'), x_{k+1} ('x'), or x_{k+1} with x_y v x_{k+1} the output gate of an extra set {y, k+1} ('s': MATCH-S).
import sys,os,json; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
def twin(variant,k=3):
    m=2*k+1; n=2*m; A=list(range(m)); B=list(range(m,2*m)); S=[A,B]+[[A[2*i+1],B[2*i+1]] for i in range(k)]
    G=[]
    def add(op,a,b=None):
        G.append([op,a] if b is None else [op,a,b]); return n+len(G)-1
    b0,b1,b2=B[1],B[3],B[5]; eo=None
    if variant=='OR2': h=add('or',A[0],b0); leakA=b0
    elif variant=='E0': h=eo=add('or',A[1],b0); leakA=b0
    elif variant=='AND2': h=add('and',b0,b1); leakA=h
    elif variant=='MAJ3':
        t1=add('and',b0,b1); t2=add('and',b0,b2); t3=add('and',b1,b2); h=add('or',add('or',t1,t2),t3); leakA=h
    N=add('not',h); outs=[]
    for X,Y in ((A,B),(B,A)):
        y=X[-1]; mer=[]
        for i in range(k):
            j=add('and',y,Y[2*i+1]); p=add('or',X[2*i+1],j); mer.append(add('or',X[2*i],p))
        while len(mer)>1: mer=[add('or',mer[0],mer[1])]+mer[2:]
        if X is A: outs.append(add('or',add('and',add('or',y,leakA),N),mer[0]))
        elif variant=='E0': outs.append(add('or',add('and',add('or',y,A[1]),N),mer[0]))
        else: outs.append(add('or',mer[0],y))
    for i in range(k): outs.append(eo if (i==0 and eo is not None) else add('or',A[2*i+1],B[2*i+1]))
    return dict(name='TWIN-TREE-%s k=%d'%(variant,k),n=n,sets=S,gates=G,outs=outs)
def match(k,leak='f',cone=False):
    n=2*k+2; A=list(range(k+1)); B=list(range(k+1,2*k+2)); S=[A,B]+[[i,k+1+i] for i in range(k)]
    G=[]
    def add(op,a,b=None):
        G.append([op,a] if b is None else [op,a,b]); return n+len(G)-1
    def tree(L):
        L=list(L)
        while len(L)>1: L=[add('or',L[i],L[i+1]) if i+1<len(L) else L[i] for i in range(0,len(L),2)]
        return L[0]
    f={}; pp={}
    for X,Y,nm in ((A,B,'A'),(B,A,'B')):
        pp[nm]=[add('or',X[i],add('and',X[-1],Y[i])) for i in range(k)]; f[nm]=tree(pp[nm])
    h=add('or',f['A'],f['B']); N=add('not',h)
    XA=add('or',A[-1],f['B'] if leak=='f' else B[0]); XB=add('or',B[-1],f['A'] if leak=='f' else A[0])
    oA=add('or',add('and',XA,N),f['A']); oB=add('or',add('and',XB,N),f['B'])
    outs=[oA,oB]+[add('or',pp['A'][i],pp['B'][i]) if cone else add('or',i,k+1+i) for i in range(k)]   # cone: e_i = p_i v p'_i
    if leak=='s': S+=[[A[-1],B[0]],[B[-1],A[0]]]; outs+=[XA,XB]   # leak = output gate of the extra sets {y,a_0}, {y',u_0}
    return dict(name='MATCH%s k=%d leak=%s'%('-C' if cone else '',k,leak),n=n,sets=S,gates=G,outs=outs)
if __name__=='__main__':
    from f2lib import *
    out=sys.argv[1] if len(sys.argv)>1 else None
    L=[twin(v) for v in ('OR2','E0','AND2','MAJ3')]+[match(k,l) for k in (3,4,5,6,7,8) for l in ('f','x','s')]+[match(k,'s',True) for k in (6,7,8)]
    for d in L:
        c=mk(d['name'],d['n'],d['sets'],d['gates'],d['outs'])
        if c is None: print(d['name'],'INCORRECT'); continue
        F,r=stepinfo(c,0); base=sum(len(R)-1 for R in d['sets'])
        fails=not any(g>=q for g,q in r.values())
        print(d['name'],'n',d['n'],'gates',len(d['gates']),'|F2|',len(F),'base',base,'max gain-cost',max(g-q for g,q in r.values()),'STEP at Q=0:','FAILS' if fails else 'HOLDS')
        if out and fails:
            json.dump(d,open(os.path.join(out,'nonlocal_'+d['name'].lower().replace(' ','_').replace('=','').replace('-','_')+'.json'),'w'))
