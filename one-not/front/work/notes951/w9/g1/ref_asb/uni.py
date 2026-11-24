# referee harness: UNIVERSAL forms of the sub-claims of rules p/r/s/a/b, valid for every correct CLEAN LIVE one-NOT circuit
import sys, itertools
sys.path.insert(0,'..')
from g1lib import tts, _vm, varmask
def prep(c):
    n=c['n']; T=tts(c); full=(1<<(1<<n))-1
    return n,T,full
def is_clean_live(c,T=None):
    n=c['n']; T=T or tts(c); full=(1<<(1<<n))-1
    if len(set(T))!=len(T) or 0 in T or full in T: return False
    used=set(c['outs'])
    for g in c['gates']: used.update(g[1:])
    if any(n+k not in used for k in range(len(c['gates']))): return False
    if sum(g[0]=='not' for g in c['gates'])>1: return False
    return True
def is_correct(c,T):
    n=c['n']
    for S,o in zip(c['sets'],c['outs']):
        t=0
        for u in S: t|=_vm[n][u]
        if T[o]!=t or o<n: return False
    return True
def deadset(c,T,Z=(),O=()):
    """gates not needed after x_Z:=0,x_O:=1 (functional dedupe to FIRST wire, constants, cone of surviving outputs)"""
    n=c['n']; G=c['gates']; full=(1<<(1<<n))-1; vm=_vm[n]
    m=full
    for v in Z: m&=full^vm[v]
    for v in O: m&=vm[v]
    canon={0:'c0',m:'c1'}; alias={}
    for i in range(n+len(G)):
        t=T[i]&m
        if t in canon: alias[i]=canon[t]
        else: canon[t]=i; alias[i]=i
    Zs=set(Z); Os=set(O); st=[]; loss=0
    for S,o in zip(c['sets'],c['outs']):
        if Os&set(S): loss+=len(S)-1; continue
        r=[u for u in S if u not in Zs]
        loss+=len(S)-max(len(r),1)
        if len(r)>=2: st.append(alias[o])
    need=set()
    while st:
        i=st.pop()
        if not isinstance(i,int) or i<n or i in need: continue
        need.add(i); st+=[alias[j] for j in G[i-n][1:]]
    return set(range(n,n+len(G)))-need, loss, m
class An:
    def __init__(s,c):
        s.c=c; s.n,s.T,s.full=prep(c); n=s.n; G=c['gates']; s.G=G
        s.sets=[frozenset(S) for S in c['sets']]
        s.pts=sorted(set().union(*s.sets))
        s.Sv={v:[S for S in s.sets if v in S] for v in range(n)}
        s.d={v:len(s.Sv[v]) for v in range(n)}
        s.l={v:sum(len(S)>=3 for S in s.Sv[v]) for v in range(n)}
        s.P={v:frozenset(w for S in s.Sv[v] if len(S)==2 for w in S if w!=v) for v in range(n)}
        s.R={v:[n+k for k,g in enumerate(G) if v in g[1:]] for v in range(n)}
        s.rd={}   # readers of any wire
        for k,g in enumerate(G):
            for a in set(g[1:]): s.rd.setdefault(a,[]).append(n+k)
        s.pg={v:{} for v in range(n)}
        for k,g in enumerate(G):
            if g[0]=='or' and g[1]<n and g[2]<n and g[1]!=g[2]:
                a,b=g[1],g[2]
                if b in s.P[a]: s.pg[a][b]=n+k; s.pg[b][a]=n+k
        s.nonpair={v:[r for r in s.R[v] if r not in s.pg[v].values()] for v in range(n)}
        s.V1=sorted([v for v in range(n) if len(s.R[v])==1],key=lambda v:s.R[v][0])
        s.B=set(v for v in range(n) if len(s.R[v])>=2)
        s.outs=set(c['outs'])
        s._dead={}
    def gate(s,w): return s.G[w-s.n]
    def other(s,w,v):
        g=s.gate(w)
        if g[0]=='not': return None
        return g[2] if g[1]==v else g[1]
    def dead(s,Z=(),O=()):
        k=(tuple(sorted(Z)),tuple(sorted(O)))
        if k not in s._dead: s._dead[k]=deadset(s.c,s.T,Z,O)
        return s._dead[k]
    def A(s,v):   # A_j(v) for v in V1
        rv=s.R[v][0]
        return s.B|set(u for u in s.V1 if s.R[u][0]<rv)
    def Ts(s,v):
        A=s.A(v); return [(S,(S&A)-{v}) for S in s.Sv[v]]
    def Gu(s,u):
        """dict w -> lowest gate restricting to x_w under x_u:=0, for partners w WITHOUT pair-gate"""
        m=s.full^_vm[s.n][u]; out={}
        for w in s.P[u]:
            if w in s.pg[u]: continue
            t=s.T[w]&m
            for i in range(s.n,s.n+len(s.G)):
                if s.T[i]&m==t: out[w]=i; break
        return out
    def users(s,u):
        """(line users, pair-set users) of u: V1 points v, d(v)>=2, with T_S(v)={u}"""
        L=[];Pp=[]
        for v in s.V1:
            if v==u or s.d[v]<2: continue
            for S,T in s.Ts(v):
                if T=={u}: (L if len(S)>=3 else Pp).append(v)
        return L,Pp
def check(c):
    """returns list of (claim, ok, slack, info); slack=None for non-numeric"""
    a=An(c); n=a.n; T=a.T; full=a.full; vm=_vm[n]; res=[]
    def OR(S):
        t=0
        for u in S: t|=vm[u]
        return t
    for u in a.pts:
        if not a.R[u]: continue
        D,loss,m=a.dead([u])
        Gu=a.Gu(u); Ru=set(a.R[u])
        UL,UP=a.users(u)
        np_=len(a.nonpair[u]); p=len(a.P[u]); kL=len(UL)
        # eps: some c_v (v user) not a reader of x_u
        eps=0
        for v in UL+UP:
            cv=a.other(a.R[v][0],v)
            if cv is None or cv not in Ru: eps=1
        # C1 (P*, rules p and r)
        res.append(('C1_pr',len(D)>=np_+p+kL+eps,len(D)-(np_+p+kL+eps),(u,)))
        if a.l[u]>=1: res.append(('C1_nonpair>=1',np_>=1,None,(u,)))
        # C2 (S*): rule s
        if a.l[u]>=1 and (UL or UP):
            lines=[S for S in a.Sv[u] if len(S)>=3]
            freeline=any(not (S&set(UL)) for S in lines)
            if u in a.B and not freeline: pass
            else: res.append(('C2_s',len(D)>=p+kL+2,len(D)-(p+kL+2),(u,'B' if u in a.B else 'V1')))
        # C3 (T2/U2): nonpair=1, l>=1: not NOT-type; AND-type => dead0 >= p+2
        if a.l[u]>=1 and np_==1:
            h=a.nonpair[u][0]; g=a.gate(h)
            res.append(('C3_notNOT',g[0]!='not',None,(u,)))
            if g[0]=='and': res.append(('C3_andtype',len(D)>=p+2,len(D)-(p+2),(u,)))
            if g[0]=='or':
                # C5 (AL / U3): c(z)=0 for z in Q vanishing on S\u, S∩W=∅
                cw=a.other(h,u); W=set(a.pg[u]); Q=full
                for w in W: Q&=vm[w]
                ok=True
                for S in a.Sv[u]:
                    if S&W: continue
                    if T[cw]&Q&(full^OR(S-{u})): ok=False
                res.append(('C5_relAL',ok,None,(u,)))
                if a.l[u]>=2:
                    res.append(('C5_c_gate',cw>=n,None,(u,)))
                    res.append(('C5_h_not_output',h not in a.outs,None,(u,)))
                    # C7 (B*): if c|Q==0 then dead(x_W:=1) >= 2+m_W+#(w in W U-like)
                    if W and T[cw]&Q==0:
                        DW,lossW,_=a.dead([],sorted(W))
                        mW=sum(1 for S in a.sets if S&W)
                        uw=0
                        for w in W:
                            if a.l[w]>=2 and len(a.nonpair[w])==1 and a.gate(a.nonpair[w][0])[0]=='or': uw+=1
                        res.append(('C7_bcount',len(DW)>=2+mW+uw,len(DW)-(2+mW+uw),(u,tuple(W),lossW)))
        # C4 (T1): exact dead0 => readers of AND/NOT readers are g|x_w
        exact = D<=Ru|set(Gu.values())
        if exact:
            for g in a.R[u]:
                gg=a.gate(g)
                if gg[0]=='or': continue
                ok=True
                for q in a.rd.get(g,[]):
                    qq=a.gate(q)
                    want='or' if gg[0]=='and' else 'and'
                    o=a.other(q,g)
                    if not (qq[0]==want and o is not None and o<n and o in a.P[u] and o not in a.pg[u]): ok=False
                res.append(('C4_T1',ok,None,(u,g)))
                res.append(('C4_T1_hasreader',bool(a.rd.get(g)),None,(u,g)))
    # C6 (Lemma A pieces)
    for v in a.V1:
        if a.d[v]<2: continue
        r=a.R[v][0]; g=a.gate(r)
        res.append(('C3b_V1notNOT',g[0]!='not',None,(v,)))
        if g[0]!='or': continue
        cw=a.other(r,v)
        for S,Tt in a.Ts(v):
            if len(Tt)!=2: continue
            x,y=sorted(Tt)
            if a.P[x]&a.P[y]: continue
            ex={}
            for q in (x,y):
                D,_,_=a.dead([q]); ex[q]=D<=set(a.R[q])|set(a.Gu(q).values())
            Dab,loss,_=a.dead([x,y])
            res.append(('C6_c_r_die',cw in Dab and r in Dab,None,(v,x,y)))
            if ex[x] and ex[y]:
                Sx=set(a.R[x])|set(a.Gu(x).values()); Sy=set(a.R[y])|set(a.Gu(y).values())
                tau=len(set(a.R[x])&set(a.R[y]))
                res.append(('C6_disjoint',(Sx&Sy)==(set(a.R[x])&set(a.R[y])) and cw not in Sx|Sy and r not in Sx|Sy,None,(v,x,y)))
                cnt=len(Sx)+len(Sy)-tau+2
                res.append(('C6_count',len(Dab)>=cnt and (Sx|Sy)<=Dab,len(Dab)-cnt,(v,x,y)))
                andg=[k for k in set(a.R[x])&set(a.R[y]) if a.gate(k)[0]=='and']
                res.append(('C6_noAND',not andg,None,(v,x,y)))
                if x in a.V1 or y in a.V1: res.append(('C6_tau0',tau==0,None,(v,x,y)))
                if len(Dab)==cnt-tau+1 and len(Dab)==len(Sx)+len(Sy)+1:   # the minimal-CE equality case (dead = |Sx|+|Sy|+1)
                    g1=[k for k in set(a.R[x])&set(a.R[y]) if a.gate(k)[0]=='or']
                    ok=len(g1)==1 and a.rd.get(g1[0],[])==[cw] and a.gate(cw)[0]=='and' and g1[0] not in a.outs
                    res.append(('C6_A0',ok,None,(v,x,y)))
    # C8: A3' universal: not(all nonpair readers of a are x_a|x_b, b on a line with a, and a line through a without such b)
    for u in a.pts:
        if a.l[u]<1 or not a.nonpair[u]: continue
        bs=[]
        for h in a.nonpair[u]:
            g=a.gate(h); o=a.other(h,u)
            if g[0]=='or' and o is not None and o<n and o!=u: bs.append(o)
            else: bs=None; break
        if bs is None: continue
        lines=[S for S in a.Sv[u] if len(S)>=3]
        res.append(('C8_A3',all(S&set(bs) for S in lines),None,(u,)))
    # C10: Lemma N-O universal: if ALL non-pair readers of x_w are outputs o_{S_i}, every line through w is among the S_i
    for u in a.pts:
        if a.l[u]<1 or not a.nonpair[u]: continue
        if all(h in a.outs for h in a.nonpair[u]):
            Si=[S for S,o in zip(a.sets,a.c['outs']) if o in a.nonpair[u]]
            res.append(('C10_NO',all(S in Si for S in a.Sv[u] if len(S)>=3),None,(u,)))
    # C11: (P1) relative AL for a point with exactly two readers x_a|x_b (b not a partner) and x_a|c_a
    for u in a.pts:
        if len(a.R[u])!=2 or a.P[u]: continue
        gs=[a.gate(h) for h in a.R[u]]
        if any(g[0]!='or' for g in gs): continue
        os_=[a.other(h,u) for h in a.R[u]]
        for i in (0,1):
            b=os_[i]; cw=os_[1-i]
            if b<n and b!=u:
                ok=True
                for S in a.Sv[u]:
                    if b in S: continue
                    if T[cw]&vm[b]&(full^OR(S-{u})): ok=False
                res.append(('C11_P1',ok,None,(u,b)))
    # C9: bottom key claim: other input of g* is a function of key (U = B-points with nonpair=1, l>=2; V1 = single-reader points)
    Ul=[t for t in a.B if len(a.nonpair[t])==1 and a.l[t]>=2]
    cands=[(a.R[v][0],v) for v in a.V1]+[(a.nonpair[t][0],t) for t in Ul]
    if cands:
        gs,pt=min(cands); cw=a.other(gs,pt)
        if cw is not None and (pt in Ul or a.d[pt]>=2):
            res.append(('C9_c_is_gate',cw>=n,None,(pt,gs)))
            Us=set(Ul); Np=[u for u in range(n) if u not in Us and u not in a.V1]
            pgs=sorted(set(w for t in Ul for w in a.pg[t].values()))
            cls={}
            ok=True
            for x in range(1<<n):
                key=(tuple((x>>u)&1 for u in Np),tuple((T[w]>>x)&1 for w in pgs))
                val=(T[cw]>>x)&1
                if cls.setdefault(key,val)!=val: ok=False; break
            res.append(('C9_key',ok,None,(pt,gs)))
    return res
def summarize(stats,res,c=None,bad=None):
    for name,ok,slack,info in res:
        st=stats.setdefault(name,[0,0,None])
        st[0]+=1
        if not ok:
            st[1]+=1
            if bad is not None and len(bad)<20: bad.append((name,info,c))
        if slack is not None: st[2]=slack if st[2] is None else min(st[2],slack)
