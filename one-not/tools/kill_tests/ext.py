# Extended interval options (after the referee's strengthening of W1):
#  I1: world 1 for EVERY set: zero point Z maximal in D = {h = 0} among points avoiding S_w, atoms e_u, tables of C_1
#  I0: world 0 for sets with h(top_w) = 1: zero point top_w, atoms m_u ∪ {u} with m_u a minterm of h, m_u ∩ S_w ⊆ {u},
#      chosen per atom (so a heavy point u may use m_u = {u}), tables of C_0
import sys, json, itertools, collections, functools
ROOT=sys.argv[1] if len(sys.argv)>1 else 'one-not'
sys.argv=['x',ROOT,'10']
import os
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
st=collections.Counter(); bad=collections.defaultdict(list)
for name,n,S,G,outs in circuits():
    if n>10 or sum(1 for g in G if g[0]=='not')!=1 or len(S)<2: continue
    Wr=tables(n,G,'real'); W0=tables(n,G,0); W1=tables(n,G,1); P_=1<<n
    if any(Wr[o]!=functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for o,R in zip(outs,S)): continue
    if any(len(set(a)&set(b))>1 for a,b in itertools.combinations(S,2)) or any(len(R)<2 for R in S): continue
    st['circuits']+=1
    ni=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; h=Wr[G[ni-n][1]]; hb=lambda x:(h>>x)&1
    mint=[x for x in range(P_) if hb(x) and not any(hb(x&~(1<<v)) for v in range(n) if x>>v&1)]
    mint.sort(key=lambda x:(bin(x).count('1'),x))
    top=[(P_-1)&~sum(1<<u for u in R) for R in S]; d=[len(R)-1 for R in S]
    typ=[];I0=[];I1=[];OP=[];E1=[]
    for w,R in enumerate(S):
        Rm=sum(1<<u for u in R); heavy=[u for u in R if hb(1<<u)]; rest=[v for v in range(n) if v not in R]
        t='A' if hb(top[w]) else ('B' if not heavy else 'S'); typ.append(t)
        zs=[sum(1<<v for v in zz) for r in range(len(rest)+1) for zz in itertools.combinations(rest,r)]
        i1=[]
        for z in zs:
            if hb(z) or not all(hb(z|1<<v) for v in rest if not z>>v&1): continue
            M=merges(W1,n,G,R,z,{u:1<<u for u in R})
            if len(M)!=d[w]: bad['I1 size'].append((name,w,z))
            i1.append(M)
        i0=[]
        if t=='A':
            per=[[m for m in mint if (m&Rm)&~(1<<u)==0] for u in R]
            combos=itertools.islice(itertools.product(*per),4000)
            for ms in combos:
                M=merges(W0,n,G,R,top[w],{u:ms[i]|1<<u for i,u in enumerate(R)})
                if len(M)!=d[w]: bad['I0 size'].append((name,w,ms))
                i0.append(M)
        op=[merges(Wr,n,G,R,z,{u:z|1<<u for u in R}) for z in zs]
        I0.append(list(dict.fromkeys(i0))); I1.append(list(dict.fromkeys(i1))); OP.append(list(dict.fromkeys(op)))
        if t=='A': E1.append(list(dict.fromkeys(merges(W0,n,G,R,top[w],{u:m|1<<u for u in R}) for m in mint if not m&Rm)))
        elif t=='B': E1.append([merges(W1,n,G,R,top[w],{u:1<<u for u in R})])
        else: E1.append(list(dict.fromkeys(op+[merges(W1,n,G,R,top[w],{u:1<<u for u in R})])))
    fams={'E1 canonical start + W1 class for split sets':E1,
          'E2 interval classes only (I0 per atom + I1 everywhere)':[list(dict.fromkeys(I0[w]+I1[w])) for w in range(len(S))],
          'E3 E2 + plain points for sets through a heavy point with h(top)=1':[list(dict.fromkeys(I0[w]+I1[w]+(OP[w] if (typ[w]=='A' and any(hb(1<<u) for u in S[w])) else []))) for w in range(len(S))],
          'E5 world 1 only (I1 everywhere)':I1,
          'E6 I0 for sets with h(top)=1, I1 for the others':[I0[w] if typ[w]=='A' else I1[w] for w in range(len(S))],
          'E4 E2 + plain points for split sets only':[list(dict.fromkeys(I0[w]+I1[w]+(OP[w] if typ[w]=='S' else []))) for w in range(len(S))]}
    if name.split('/')[-1].split(':')[0] in ('cxe3.json','cxT2.json'):
        lab={}
        for w in range(len(S)):
            for M in I0[w]: lab.setdefault((w,M),'W0')
            for M in I1[w]: lab[(w,M)]=lab.get((w,M),'')+('/' if (w,M) in lab else '')+'W1'
        opts=fams['E2 interval classes only (I0 per atom + I1 everywhere)']; sols=[]
        def rec(i,used,pick):
            if len(sols)>=3000: return
            if i==len(S): sols.append(tuple(lab[(w,M)] for w,M in enumerate(pick))); return
            for M in opts[i]:
                if not (M&used): pick.append(M); rec(i+1,used|M,pick); pick.pop()
        rec(0,frozenset(),[])
        c=collections.Counter(sols)
        print('PROBE',name.split('/')[-1],'sets',S,'heavy',[u for u in range(n) if hb(1<<u)],'#interval SDRs',len(sols),'| options per set',[len(o) for o in opts])
        for k,v in c.most_common(6): print('     worlds per set',k,'x',v)
    for fn,opts in fams.items():
        ok=all(opts) and sdr(opts); st[fn+': SDR']+=bool(ok)
        if not ok: bad[fn].append(name.split('/')[-1]+'['+''.join(typ)+']')
for k,v in sorted(st.items()): print('%-70s %d'%(k,v))
for k,v in bad.items(): print('FAIL',k,len(v),v[:14])
