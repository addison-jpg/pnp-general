import itertools, random, sys
from pysat.solvers import Glucose4
from pysat.card import CardEnc
def build(n, sets, s, p, extra_blocks):
    rows=range(1<<n); top=[0]
    def nv(): top[0]+=1; return top[0]
    cl=[]; W={}; SEL={}
    for k in range(s):
        m=n+k
        A=[nv() for _ in range(m)]; B=[nv() for _ in range(m)]; op=nv()
        for L in (A,B):
            enc=CardEnc.equals(lits=L,bound=1,top_id=top[0]); cl+=enc.clauses; top[0]=max(top[0],enc.nv)
        SEL[k]=(A,B,op)
        if k!=p:
            for i in range(m):
                for j in range(i): cl.append([-A[i],-B[j]])
        for r in rows:
            g=nv(); W[(m,r)]=g
            for i in range(m):
                wi=(r>>i&1) if i<n else W[(i,r)]
                if k==p:   # NOT of A-selected wire
                    if i<n: cl.append([-A[i], -g if wi else g])
                    else: cl+= [[-A[i],-wi,-g],[-A[i],wi,g]]
                    continue
                for j in range(i,m):
                    wj=(r>>j&1) if j<n else W[(j,r)]
                    for opv in (1,0):
                        for va in (0,1):
                            for vb in (0,1):
                                c=[-A[i],-B[j], -op if opv else op]; skip=False
                                for w,vv,isin in ((wi,va,i<n),(wj,vb,j<n)):
                                    if isin:
                                        if w!=vv: skip=True
                                    else: c.append(-w if vv else w)
                                if skip: continue
                                out=(va and vb) if opv else (va or vb)
                                c.append(g if out else -g); cl.append(c)
    O=[]
    for S in sets:
        o=[nv() for _ in range(n+s)]; O.append(o)
        enc=CardEnc.equals(lits=o,bound=1,top_id=top[0]); cl+=enc.clauses; top[0]=max(top[0],enc.nv)
        for w in range(n,n+s):
            for r in rows:
                t=any(r>>v&1 for v in S); cl.append([-o[w], W[(w,r)] if t else -W[(w,r)]])
        for w in range(n): cl.append([-o[w]])
    # NOT must matter: its output is read by some later gate
    cl.append([SEL[k][0][n+p] for k in range(p+1,s)]+[SEL[k][1][n+p] for k in range(p+1,s)])
    cl+=extra_blocks
    return cl,SEL,O
def decode(model,n,s,p,SEL,O):
    M=set(x for x in model if x>0); gates=[]
    for k in range(s):
        A,B,op=SEL[k]; a=[i for i,v in enumerate(A) if v in M][0]
        if k==p: gates.append(('not',a,a)); continue
        b=[i for i,v in enumerate(B) if v in M][0]; gates.append(('and' if op in M else 'or',a,b))
    outs=[[w for w,v in enumerate(o) if v in M][0] for o in O]
    return gates,outs
def wires(n,gates,x):
    w=[(x>>i)&1 for i in range(n)]
    for op,a,b in gates:
        w.append(1-w[a] if op=='not' else (w[a]&w[b] if op=='and' else w[a]|w[b]))
    return w
def analyse(n,sets,gates,p):
    hw=gates[p][1]; full=(1<<n)-1
    h=lambda x: wires(n,gates,x)[hw]
    minterms=[x for x in range(1<<n) if h(x) and all(not h(x&~(1<<i)) for i in range(n) if x>>i&1)]
    Ds=[]; kinds=[]
    for S in sets:
        Z=full & ~sum(1<<v for v in S)
        if not h(Z):
            pts={u:1<<u for u in S}; kinds.append('good')
        else:
            Ms=[m for m in minterms if not any(m>>v&1 for v in S)]
            Mm=min(Ms,key=lambda m:bin(m).count('1'))
            pts={u:(1<<u)|Mm for u in S}; kinds.append('bad')
        wZ=wires(n,gates,Z); wp={u:wires(n,gates,pts[u]) for u in S}
        D=set(k for k in range(len(gates)) if wZ[n+k]==0 and sum(wp[u][n+k] for u in S)>=2)
        Ds.append(D)
    tot=sum(len(D) for D in Ds); uni=len(set().union(*Ds))
    return kinds,tot-uni,uni
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 0)
systems=[(5,[(0,1,2),(0,3,4)]),(5,[(0,1),(1,2),(0,2),(3,4)]),(5,[(0,1,2),(2,3),(3,4,0)]),(6,[(0,1,2),(0,3,4),(1,3,5)]),(5,[(0,1,2,3),(0,4)]),(6,[(0,1),(2,3),(4,5),(0,2,4)])]
for n,sets in systems:
    base=sum(len(S)-1 for S in sets)
    for s in (base,base+1):
        worst=-1; cnt=0
        for p in range(s-1):
            blocks=[]
            for it in range(40):
                cl,SEL,O=build(n,sets,s,p,blocks)
                S_=Glucose4(bootstrap_with=cl)
                if not S_.solve(): break
                gates,outs=decode(S_.get_model(),n,s,p,SEL,O); cnt+=1
                kinds,ov,uni=analyse(n,sets,gates,p)
                worst=max(worst,ov)
                if ov>=2: print('  OVERLAP',ov,'n',n,sets,'s',s,'p',p,gates,kinds,flush=True)
                # block this exact gate structure
                blocks.append([-SEL[k][0][gates[k][1]] for k in range(s)]+[-SEL[k][1][gates[k][2]] for k in range(s) if k!=p])
        print(n,sets,'size',s,'(sum',base,') circuits',cnt,'max overlap',worst,flush=True)
