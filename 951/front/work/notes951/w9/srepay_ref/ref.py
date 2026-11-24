# independent referee checker for srepay_opus.md (does NOT import analyze.py / bt.TT)
import json, glob, sys, random, itertools, collections
F='/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/'
def norm(c):
    c['gates']=[['not',g[1]] if g[0]=='not' else list(g) for g in c['gates']]; return c
def tts(c):
    n=c['n']; P=1<<n; FULL=(1<<P)-1
    var=[sum(1<<x for x in range(P) if x>>v&1) for v in range(n)]
    W={}
    for mode in ('r',0,1):
        w=list(var)
        for g in c['gates']:
            if g[0]=='not': w.append(FULL^w[g[1]] if mode=='r' else (0 if mode==0 else FULL))
            elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
            elif g[0]=='or': w.append(w[g[1]]|w[g[2]])
            else: raise ValueError
        W[mode]=w
    o=[]
    for S in c['sets']:
        m=0
        for u in S: m|=var[u]
        o.append(m)
    return var,W,o,FULL
class UF:
    def __init__(s,xs): s.p={x:x for x in xs}
    def f(s,x):
        while s.p[x]!=x: x=s.p[x]
        return x
    def u(s,a,b):
        a,b=s.f(a),s.f(b)
        if a==b: return False
        s.p[b]=a; return True
    def nb(s): return len({s.f(x) for x in s.p})
def check(c,name='?',verbose=False):
    """returns dict of facts and list of violated claims"""
    c=norm(c); n=c['n']; G=c['gates']; S=c['sets']; outs=c['outs']
    var,W,o,FULL=tts(c)
    nots=[n+k for k,g in enumerate(G) if g[0]=='not']
    assert len(nots)<=1
    res={}; viol=[]
    res['correct']=all(W['r'][x]==t for x,t in zip(outs,o))
    res['hasnot']=bool(nots)
    res['c0ok']=all(W[0][x]==t for x,t in zip(outs,o)); res['c1ok']=all(W[1][x]==t for x,t in zip(outs,o))
    res['ess']=(not res['c0ok']) and (not res['c1ok'])
    s=len(G); base=sum(len(x)-1 for x in S)
    res['s']=s; res['base']=base
    res['linear']=all(len(set(a)&set(b))<=1 for a,b in itertools.combinations(S,2))
    Vp=sorted({u for x in S for u in x})
    hu=UF(Vp)
    for x in S:
        for u in x[1:]: hu.u(x[0],u)
    comp=hu.nb(); cyc=base-(len(Vp)-comp); res['cyc']=cyc; assert cyc>=0
    if not nots: return res,viol
    Ni=nots[0]; h=W['r'][G[Ni-n][1]]; res['h0']=h&1
    if not res['correct']: return res,viol
    if h&1: return res,viol
    W1=W[1]
    # V = gates of M vanishing at (0,1)
    inV=lambda w: w!=Ni and not (W1[w]&1)
    B=lambda w: frozenset(u for u in Vp if W1[w]>>(1<<u)&1)
    for x,Sx in zip(outs,S):
        if not inV(x): viol.append('F_w(0,1)!=0')
        if not set(Sx)<=B(x): viol.append('F_w(e_u,1)=0')
    ju=UF(Vp); su=[UF(x) for x in S]
    J=[]; M=[[] for _ in S]; Xprop=True; struct_bad=0; struct2_bad=0
    for k,g in enumerate(G):
        gid=n+k
        if g[0]=='not' or not inV(gid): continue
        Bg=B(gid)
        if g[0]=='and':
            # proof step: some child in V, B(G) inside B(child)
            ch=[x for x in g[1:] if inV(x)]
            if not ch: viol.append('AND in V without child in V')
            elif not any(Bg<=B(x) for x in ch): viol.append('AND B not inside child')
        else:
            a,b=g[1],g[2]
            if not (inV(a) and inV(b)): viol.append('OR in V with child not in V'); continue
            Ba,Bb=B(a),B(b)
            for X_ in (Ba,Bb):
                if len({ju.f(u) for u in X_})>1: viol.append('child B not in one joint block')
            jm=False
            if Ba and Bb and ju.f(next(iter(Ba)))!=ju.f(next(iter(Bb))):
                ju.u(next(iter(Ba)),next(iter(Bb))); J.append(gid); jm=True
            kk=0
            for wi,Sx in enumerate(S):
                a_=[u for u in Ba if u in Sx]; b_=[u for u in Bb if u in Sx]
                for X_ in (a_,b_):
                    if len({su[wi].f(u) for u in X_})>1: viol.append('child B_w not in one per-set block')
                if a_ and b_:
                    if su[wi].u(a_[0],b_[0]): M[wi].append(gid); kk+=1
                    if jm and False: pass
                if jm and a_ and b_ and gid not in M[wi]: viol.append('joint merge, both B_w nonempty, not per-set merge')
            if kk>=2:
                # structure claim: both children have atoms of >=2 sets
                def nsets(Bx): return sum(1 for Sx in S if any(u in Sx for u in Bx))
                if nsets(Ba)<2 or nsets(Bb)<2: struct_bad+=1
                # stronger reading: each child is itself not an input wire (mixedness created by a gate)
                if a<n or b<n: struct2_bad+=1
        if len({ju.f(u) for u in Bg})>1: viol.append('invariant: B(g) not in one joint block')
    for wi,Sx in enumerate(S):
        if len(M[wi])!=len(Sx)-1: viol.append('|M_w|!=d_w')
        # M_w inside the class cl_w = {g in V, >=2 unit atoms of S_w}
        for g in M[wi]:
            if len([u for u in Sx if u in B(g)])<2: viol.append('M_w not in cl_w')
    Jn=len(J); U=set(g for m in M for g in m); cnt=collections.Counter(g for m in M for g in m)
    coll=sum(k-1 for k in cnt.values()); X=[g for g in J if g not in U]; nonj=len(U-set(J))
    if Jn<len(Vp)-comp: viol.append('LEMMA J')
    if len(X)!=coll+nonj+(Jn-base): viol.append('CHARGE identity')
    if len(X)<coll+nonj-cyc: viol.append('CHARGE')
    sM=s-1; out=sM-len(U)
    if cyc==0:
        if not (coll<=len(X)<=out): viol.append('S-repay hyperforest')
        if s<base+1: viol.append('s<base+1 on hyperforest')
    if (sM-Jn>=base-Jn)!=(s>=base+1): viol.append('equiv')
    res.update(J=Jn,need=len(Vp)-comp,coll=coll,X=len(X),nonj=nonj,out=out,struct_bad=struct_bad,struct2_bad=struct2_bad,
               kmax=max(cnt.values()) if cnt else 0)
    return res,viol
def files():
    fs=sorted(glob.glob(F+'w8/cx*.json'))+[F+'w8b/cxr.json',F+'w9/fb/cfgI.json']+sorted(glob.glob(F+'w9/fc/*.json'))+sorted(glob.glob(F+'w9/tw/*.json'))
    fs+=sorted(glob.glob(F+'w9/g3/*.json'))+sorted(glob.glob(F+'w9/p/cx*.json'))+sorted(glob.glob(F+'w9/srepay/hand_*.json'))
    for f in fs:
        yield f.replace(F,''),json.load(open(f))
    for f in [F+'w7/badT.jsonl',F+'w7/bad.jsonl',F+'chk/c.jsonl']+sorted(glob.glob(F+'w9/srepay/*.jsonl')):
        for i,l in enumerate(open(f)):
            if l.strip(): yield f.replace(F,'')+':%d'%i,json.loads(l)
if __name__=='__main__':
    st=collections.Counter(); minsl=[]
    for name,c in files():
        if not isinstance(c,dict) or c['n']>16: st['skip']+=1; continue
        r,v=check(c,name)
        st['n']+=1
        for k in ('correct','hasnot','ess','linear'): st[k]+=bool(r.get(k))
        if not r['correct']: print('INCORRECT',name); continue
        if not r['hasnot']: continue
        if r['h0']: st['h0=1']+=1; continue
        st['checked']+=1
        if r['cyc']==0: st['forest']+=1; st['forest_coll']+=r['coll']>0
        st['coll>0']+=r['coll']>0; st['struct_bad']+=r['struct_bad']>0; st['struct2_bad']+=r['struct2_bad']>0
        st['s<=base']+= r['s']<=r['base']; st['s==base+1']+= r['s']==r['base']+1
        st['J>need']+= r['J']>r['need']
        if v: print('VIOL',name,sorted(set(v)),r)
        if 'hand' in name or 'cxP' in name or 'cxstar' in name: print(name,r)
    print(dict(st))
