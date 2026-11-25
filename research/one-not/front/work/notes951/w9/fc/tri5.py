# cxT(k): triangle of (k+2)-sets a={p,r,a_1..a_k}, b={p,q,b*}, c={q,r,c*}; h = p|q|r (heavy p,q,r; all private points light).
# o_a = P_a & Q_a,  P_a = h | OR(a*)  (rule-invisible: not <= o_a, and P_a(z_S)=1),
# Q_a = N | t | x_p | x_r,  t = OR_i (x_q a_i | x_r b_i | x_p c_i)  (shared relative merge tree: t = OR(a*)+... on {x_q=1} etc.)
import sys, json, itertools
def build(k, shareQ=True):
    n=3+3*k; G=[]; p,q,r=0,1,2; A=list(range(3,3+k)); B=list(range(3+k,3+2*k)); C=list(range(3+2*k,3+3*k))
    def g(op,a,b=None):
        G.append([op,a,b] if op!='not' else ['not',a]); return n+len(G)-1
    h=g('or',g('or',p,q),r); N=g('not',h)
    Pi=[g('or',g('or',g('and',q,A[i]),g('and',r,B[i])),g('and',p,C[i])) for i in range(k)]
    t=Pi[0]
    for x in Pi[1:]: t=g('or',t,x)
    Nt=g('or',N,t); Q1p=g('or',Nt,p); Q1r=g('or',Nt,r)
    def Pch(L):
        w=g('or',h,L[0])
        for v in L[1:]: w=g('or',w,v)
        return w
    Qa=g('or',Q1p,Q1r); Qb=g('or',Q1p,q); Qc=g('or',Q1r,q)
    oa=g('and',Pch(A),Qa); ob=g('and',Pch(B),Qb); oc=g('and',Pch(C),Qc)
    return dict(n=n,sets=[[p,r]+A,[p,q]+B,[q,r]+C],gates=G,outs=[oa,ob,oc])
# ---- bitset tools (truth tables as Python ints over 2^n inputs; input x <-> index sum x_v<<v) ----
def tabs(c, force=None):
    n,G=c['n'],c['gates']; full=(1<<(1<<n))-1; T=[]
    for v in range(n):
        blk=(1<<(1<<v))-1; m=0; per=1<<(v+1)
        pat=blk<<(1<<v); m=0
        for j in range(0,1<<n,per): m|=pat<<j
        T.append(m)
    for gt in G:
        if gt[0]=='not': T.append((full^T[gt[1]]) if force is None else (full if force else 0))
        elif gt[0]=='and': T.append(T[gt[1]]&T[gt[2]])
        else: T.append(T[gt[1]]|T[gt[2]])
    return T,full
def bverify(c):
    n,G,S,outs=c['n'],c['gates'],c['sets'],c['outs']; T,full=tabs(c); T0,_=tabs(c,0); T1,_=tabs(c,1)
    f=[0]*len(S)
    for w,s in enumerate(S):
        for u in s: f[w]|=T[u]
    hw=[g for g in G if g[0]=='not'][0][1]; nw=n+[k for k,g in enumerate(G) if g[0]=='not'][0]
    idx=lambda ones: sum(1<<v for v in ones)
    zS=lambda s: idx([v for v in range(n) if v not in s])
    read=set(j for g in G for j in g[1:])|set(outs)
    def cone(o):
        seen=set(); st=[o]
        while st:
            i=st.pop()
            if i in seen or i<n: continue
            seen.add(i); st+=G[i-n][1:]
        return seen
    return dict(correct=all(T[o]==f[w] for w,o in enumerate(outs)), C0wrong=any(T0[o]!=f[w] for w,o in enumerate(outs)),
        C1wrong=any(T1[o]!=f[w] for w,o in enumerate(outs)), clean=len(set(T))==len(T) and all(0<t<full for t in T),
        read=all(n+k in read for k in range(len(G))), h0=T[hw]&1,
        hardN=[bool(T[hw]>>zS(s)&1) and nw in cone(o) for s,o in zip(S,outs)],
        DD=[bool(T1[o]>>zS(s)&1) and any(not (T0[o]>>(1<<u)&1) for u in s) for s,o in zip(S,outs)],
        s=len(G), base=sum(len(s)-1 for s in S), n=n)
def brel(c, maxw=2):
    """relative-sandwich menus (same reading as relrule.py), bitset version. returns per set {z-ones: sorted C}"""
    n,G,S,outs=c['n'],c['gates'],c['sets'],c['outs']; T,full=tabs(c); ng=len(G)
    hw=[g for g in G if g[0]=='not'][0][1]
    val=lambda g,ones: T[g]>>sum(1<<v for v in ones)&1
    mins=[]
    for wgt in range(1,maxw+1):
        for m in itertools.combinations(range(n),wgt):
            if val(hw,m) and not any(set(y)<=set(m) for y in mins): mins.append(m)
    res=[]
    for w,R in enumerate(S):
        f=0
        for u in R: f|=T[u]
        zS=[v for v in range(n) if v not in R]
        L={g for g in range(n,n+ng) if T[g]&~f==0 and sum(val(g,[u]) for u in R)>=2}
        U={g for g in range(n,n+ng) if f&~T[g]==0 and val(g,zS)==0}
        P=L|U; menu={}
        for z in [()]+[m for m in mins if not set(m)&set(R)]:
            cube=full
            for v in z: cube&=T[v]
            cnt={g for g in range(n,n+ng) if val(g,z)==0 and sum(val(g,list(z)+[u]) for u in R)>=2}
            I={g for g in cnt if T[g]&cube&~f==0}
            menu[z]=sorted(I|(P&cnt))
        res.append(dict(P=sorted(P),menu=menu))
    return res
def sigma_cnt(c, w, z):
    n,G=c['n'],c['gates']; T,_=tabs(c); R=c['sets'][w]
    val=lambda g,ones: T[g]>>sum(1<<v for v in ones)&1
    return [g for g in range(n,n+len(G)) if val(g,z)==0 and sum(val(g,list(z)+[u]) for u in R)>=2]
if __name__=='__main__':
    from lib import fraclp, family, hbmatch
    k=int(sys.argv[1]); c=build(k); json.dump(c,open('cxT%d.json'%k,'w'))
    print('k',k,bverify(c)); print('Theorem X family (strict/permissive):',family(c),family(c,True))
    rel=brel(c); dem=[len(s)-1 for s in c['sets']]
    for s,r in zip(c['sets'],rel): print(' set',s,'P',r['P'],'menu',r['menu'])
    M=[{frozenset(C):(z,None) for z,C in r['menu'].items() if len(C)>=d} for r,d in zip(rel,dem)]
    if any(not m for m in M): print('L_rel = inf (a set has no admissible system with >= d gates)')
    else:
        print('L_rel =',fraclp(c,M=M)[0],' union of all rule-chargeable gates',len(set().union(*[set(C) for m in M for C in m])),'demand',sum(dem))
    # free choice, restricted sub-menu: Sigma(z) for z in {0, e_v (v heavy), z_S}: an upper bound for L*
    n=c['n']; M2=[]
    for w,S in enumerate(c['sets']):
        zs=[()]+[(v,) for v in (0,1,2) if v not in S]+[tuple(v for v in range(n) if v not in S)]
        M2.append({frozenset(sigma_cnt(c,w,z)):(z,None) for z in zs})
    print('free choice, sub-menu Sigma(z), z in {0,e_v,z_S}, K=all: L <=',fraclp(c,M=M2)[0],'sizes',[[len(C) for C in m] for m in M2])
    print('integer Hall with z=0 for every set:',hbmatch([sigma_cnt(c,w,()) for w in range(3)],dem),'/',sum(dem))
