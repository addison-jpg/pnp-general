# Fable-C toolkit: independent verifier + "no pairwise zero-set family" checker + wrappers.
import sys, os, json, itertools, io, contextlib
H=os.path.dirname(os.path.abspath(__file__))
for d in ('../tw','../../chk','../../w8b','../../w8','..'): sys.path.insert(0, os.path.join(H,d))
def ev(n,G,x,force=None):
    w=list(x)
    for g in G:
        if g[0]=='not': w.append((1-w[g[1]]) if force is None else force)
        elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
        else: w.append(w[g[1]]|w[g[2]])
    return w
def cone(n,G,o):
    seen,st=set(),[o]
    while st:
        i=st.pop()
        if i in seen or i<n: continue
        seen.add(i); st.extend(G[i-n][1:])
    return seen
def verify(c):
    """independent: correctness on all inputs, clean, read, C0 wrong, C1 wrong, h(0)=0, hard N-sets, DD sets"""
    n,G,S,outs=c['n'],c['gates'],c['sets'],c['outs']; ng=len(G)
    nots=[k for k,g in enumerate(G) if g[0]=='not']; assert len(nots)==1
    nw=n+nots[0]; hw=G[nots[0]][1]
    for k,g in enumerate(G): assert all(0<=j<n+k for j in g[1:]) and g[0] in('and','or','not') and len(g)==(2 if g[0]=='not' else 3)
    for a,b in itertools.combinations(S,2): assert len(set(a)&set(b))<=1
    assert all(len(s)>=2 for s in S)
    ok=c0=c1=True; tabs=[0]*(n+ng)
    for xi,x in enumerate(itertools.product([0,1],repeat=n)):
        w=ev(n,G,x); w0=ev(n,G,x,0); w1=ev(n,G,x,1)
        for i in range(n+ng):
            if w[i]: tabs[i]|=1<<xi
        for o,st in zip(outs,S):
            f=int(any(x[v] for v in st)); ok&=w[o]==f; c0&=w0[o]==f; c1&=w1[o]==f
    full=(1<<(2**n))-1
    clean=len(set(tabs))==len(tabs) and all(0<t<full for t in tabs)
    read=set(j for g in G for j in g[1:])|set(outs)
    zS=lambda Q:[0 if v in Q else 1 for v in range(n)]
    unit=lambda u:[int(v==u) for v in range(n)]
    hard=[ev(n,G,zS(s))[hw]==1 for s in S]; nset=[nw in cone(n,G,o) for o in outs]
    dd=[ev(n,G,zS(s),1)[o]==1 and any(ev(n,G,unit(u),0)[o]==0 for u in s) for s,o in zip(S,outs)]
    return dict(correct=ok,C0wrong=not c0,C1wrong=not c1,clean=clean,read=all(n+k in read for k in range(ng)),
                h0=ev(n,G,[0]*n)[hw],hardN=sum(a and b for a,b in zip(hard,nset)),hard=hard,nset=nset,DD=dd,
                s=ng,base=sum(len(s)-1 for s in S),n=n)
def goodQs(c, permissive=False):
    """minimal Good zero sets Q ⊇ S_w, cone-masked (hallcheck.canon semantics). permissive: also Good if
    NOT true at <=1 unit of S (Lean GoodT with unit atoms)."""
    n,G,S,outs=c['n'],c['gates'],c['sets'],c['outs']
    k0=[k for k,g in enumerate(G) if g[0]=='not'][0]; nw=n+k0
    unitN=[ev(n,G,[int(v==u) for v in range(n)])[nw] for u in range(n)]
    du=all(x==0 for x in unitN); res=[]
    for wi,R in enumerate(S):
        R=set(R)
        if nw not in cone(n,G,outs[wi]) or du or (permissive and sum(unitN[u] for u in R)<=1): res.append([frozenset(R)]); continue
        rest=[v for v in range(n) if v not in R]; mins=[]
        for r in range(len(rest)+1):
            for ex in itertools.combinations(rest,r):
                Q=frozenset(R|set(ex))
                if any(m<=Q for m in mins): continue
                if ev(n,G,[0 if v in Q else 1 for v in range(n)])[nw]==1: mins.append(Q)
        res.append(mins)
    return res
def family(c, permissive=False):
    """exhaustive search for Q_w (Good, ⊇S_w) with pairwise |S_a∩Q_b|<=1 or |S_b∩Q_a|<=1. Only minimal Good Q's matter
    (condition is monotone decreasing in Q). Returns a family or None."""
    S=[set(s) for s in c['sets']]; m=len(S); QQ=goodQs(c,permissive)
    order=sorted(range(m),key=lambda w:len(QQ[w])); ch={}
    def okp(a,b): return len(S[a]&ch[b])<=1 or len(S[b]&ch[a])<=1
    def rec(k):
        if k==m: return True
        w=order[k]
        for Q in QQ[w]:
            ch[w]=Q
            if all(okp(w,order[j]) for j in range(k)) and rec(k+1): return True
        ch.pop(w,None); return False
    return {w:sorted(ch[w]) for w in ch} if rec(0) else None
with contextlib.redirect_stdout(io.StringIO()):
    _a=sys.argv; sys.argv=[_a[0]]
    from hallcheck import canon, bmatch as hbmatch
    sys.argv=_a
from rstar import rstar
from mixrule import mix
from fraclp import fraclp
import allsys
def report(c, full=True, cone_too=True, intm=False):
    v=verify(c); print('verify',v)
    print('family(strict Good):',family(c),' family(permissive):',family(c,True))
    dem=[len(s)-1 for s in c['sets']]; base=sum(dem)
    Dc=canon(c); Dr=rstar(c); print('Dc',Dc,'\nDr',Dr)
    print('canonical Hall',hbmatch(Dc,dem),'/',base,' R* Hall',hbmatch(Dr,dem),'/',base)
    for a in (0.5,0.3,0.7): print(' coin a=%.1f load %.4f'%(a,mix(c,a)))
    if full:
        L,lam,M=fraclp(c,False); print('fraclp all-gate L*=%.6f'%L,'menus',[len(m) for m in M])
        if cone_too:
            L2,lam2,M2=fraclp(c,True); print('fraclp coneonly L*=%.6f'%L2,'menus',[len(m) for m in M2])
        if intm:
            best=-1
            for combo in itertools.product(*[list(m) for m in M]):
                b=allsys.bmatch([sorted(x) for x in combo],dem); best=max(best,b)
                if best==base: break
            print('integer MatchG best',best,'/',base)
        return L
