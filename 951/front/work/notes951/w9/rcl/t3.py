# (i) defect form: independent check of identity s-1-base = #rest - sum_{T in SD}(m(T)-1), privacy 3.1, exact |HM_w|+sum m_w = d_w
import collections
from rl import *
st=collections.Counter(); mn=99
for name,c in files():
    if c['n']>16: continue
    Lc=L(c)
    if not(Lc.ok and Lc.correct): continue
    if Lc.h0: st['h0=1 skipped']+=1; continue
    n,N,W=Lc.n,Lc.N,Lc.W; h=W[Lc.hw]; st['circ']+=1
    HM=[];SD={}
    Om=[]
    for k,Sx in enumerate(Lc.S):
        o=0
        for u in Sx: o|=Lc.var[u]
        Om.append(o|(Lc.Y&h))
    inV=lambda w,k:(W[w]&~Om[k]&Lc.full)==0
    for k,Sx in enumerate(Lc.S):
        atoms={u:(1<<u)+(0 if (Lc.hx>>(1<<u))&1 else N) for u in Sx}
        B=lambda w:frozenset(u for u,p in atoms.items() if (W[w]>>p)&1)
        assert inV(Lc.outs[k],k) and len(B(Lc.outs[k]))==len(Sx)
        assert [i for i in Lc.inputs if inV(i,k)]==sorted(Sx)
        # privacy 3.1 for all wires
        for w in range(len(W)):
            if inV(w,k):
                for k2 in range(len(Lc.S)):
                    if k2!=k and inV(w,k2): assert B(w)<=set(Sx)&set(Lc.S[k2])
        uf=UF(Sx); hm=0; df=0
        for w in Lc.gatew:
            if not inV(w,k): continue
            a,b=Lc.ch(w)
            if Lc.op(w)=='or':
                assert inV(a,k) and inV(b,k)
                Ba,Bb=B(a),B(b)
                if Ba and Bb and uf.u(next(iter(Ba)),next(iter(Bb))): hm+=1; HM.append(w)
            elif not (inV(a,k) or inV(b,k)):
                rs=list({uf.f(u) for u in B(w)})
                if len(rs)>1:
                    for r in rs[1:]: uf.u(rs[0],r)
                    assert w not in SD; SD[w]=len(rs)-1; df+=len(rs)-1
            assert len({uf.f(u) for u in B(w)})<=1
        assert hm+df==len(Sx)-1
    assert len(HM)==len(set(HM)) and not set(HM)&set(SD)
    rest=len(Lc.gatew)-len(HM)-len(SD); exc=sum(m-1 for m in SD.values())
    assert (Lc.s-1-Lc.base)==rest-exc
    st['SD>0']+=bool(SD); st['excess>0']+=exc>0; mn=min(mn,rest-exc); st['maxexc']=max(st['maxexc'],exc)
print(dict(st),'min(rest-excess)=min(s-1-base)',mn)
