#!/usr/bin/env python3
"""Defect form of the game adversary (NOTES.md section 3).
For each one-NOT circuit: lift NOT -> input y, canonical 'honest' classes
V**_w = {wires <= Omega_w := o_w or (y and h)}, atoms (e_u, level = not h(e_u)).
Union-find over V**_w in circuit order; split AND (in V**_w, no child in V**_w) merges all
blocks met by B_w: defect m_w(T).  Checks:
 T1 (theorem)  HM_w + sum_T m_w(T) >= d_w ; honest merge sets pairwise disjoint; defect ANDs private
 D  (conjecture) sum_T (m(T)-1)^+ <= #rest  (rest = gates of M neither honest merge nor defect AND)
Usage: defect.py file.jsonl [...]"""
import sys, json, itertools
def run(c):
    n=c['n']; sets=[tuple(s) for s in c['sets']]; gates=c['gates']; outs=c['outs']
    nots=[i for i,g in enumerate(gates) if g[0]=='not']
    if len(nots)!=1: return None
    ni=nots[0]; hw=gates[ni][1]
    N=1<<n
    # truth tables as python ints over 2N points: index = x + N*y
    full=(1<<(2*N))-1
    def var(i):
        t=0
        for p in range(2*N):
            if (p>>i)&1: t|=1<<p
        return t
    W=[var(i) for i in range(n)]
    Y=var(n)
    for i,g in enumerate(gates):
        if g[0]=='not': W.append(Y)
        elif g[0]=='and': W.append(W[g[1]]&W[g[2]])
        else: W.append(W[g[1]]|W[g[2]])
    h=W[hw]
    lo=(1<<N)-1
    if (h&lo)!=(h>>N): return None  # h must be y-free
    hx=h&lo
    # real value: at x use level y = not h(x)
    def real(t):
        r=0
        for x in range(N):
            lvl=0 if (hx>>x)&1 else 1
            if (t>>(x+N*lvl))&1: r|=1<<x
        return r
    res={'s':len(gates),'base':sum(len(S)-1 for S in sets)}
    HMall=[]; SD={}; ok=True
    for S,o in zip(sets,outs):
        ow=0
        for u in S: ow|=W[u]
        if real(W[o])!=(ow&lo): return {'bad':'incorrect'}
        Om=ow|(Y&h)
        inV=lambda t: (t&~Om&full)==0
        if inV(Y): return {'bad':'y in V**'}
        atoms=[(1<<u)+(0 if (hx>>(1<<u))&1 else N) for u in S]
        B=lambda t: frozenset(k for k,a in enumerate(atoms) if (t>>a)&1)
        par=list(range(len(S)))
        def f(a):
            while par[a]!=a: a=par[a]
            return a
        HM=0
        for i,g in enumerate(gates):
            w=n+i
            if g[0]=='not' or not inV(W[w]): continue
            if g[0]=='or':
                b1,b2=B(W[g[1]]),B(W[g[2]])
                r1={f(a) for a in b1}; r2={f(a) for a in b2}
                assert len(r1)<=1 and len(r2)<=1
                if r1 and r2 and r1!=r2:
                    par[r1.pop()]=r2.pop(); HM+=1; HMall.append(w)
            else:
                if inV(W[g[1]]) or inV(W[g[2]]):
                    assert len({f(a) for a in B(W[w])})<=1
                else:
                    rs=list({f(a) for a in B(W[w])})
                    if len(rs)>1:
                        for r in rs[1:]: par[r]=rs[0]
                        assert w not in SD
                        SD[w]=len(rs)-1
        assert len({f(a) for a in range(len(S))})==1
    assert len(HMall)==len(set(HMall))
    hm=len(HMall); sd=len(SD); defect=sum(SD.values())
    rest=(len(gates)-1)-hm-sd
    assert hm+defect>=res['base']
    res.update(hm=hm,sd=sd,defect=defect,rest=rest,excess=sum(m-1 for m in SD.values()),
               slack=hm+defect-res['base'])
    return res
if __name__=='__main__':
    tot=0;bad={};viol=0;st={'sd>0':0,'excess>0':0}; minmargin=None; worst=None
    for fn in sys.argv[1:]:
        for line in open(fn):
            c=json.loads(line); r=run(c)
            if r is None: bad['skip']=bad.get('skip',0)+1; continue
            if 'bad' in r: bad[r['bad']]=bad.get(r['bad'],0)+1; continue
            tot+=1
            if r['sd']: st['sd>0']+=1
            if r['excess']: st['excess>0']+=1
            mg=r['rest']-r['excess']
            if minmargin is None or mg<minmargin: minmargin=mg; worst=(r,c)
            if mg<0: viol+=1
    print('circuits',tot,'skipped',bad,'stats',st,'D violations',viol,'min(rest-excess)',minmargin)
    print('worst',worst[0]); print(json.dumps(worst[1]))
