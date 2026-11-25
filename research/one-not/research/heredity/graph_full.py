# Graph systems: full Lean pureMenu (I1: any Z avoiding S_w with h(Z)=0; I0: zero point top_w, ANY m_u with h(m_u)=1,
# m_u ∩ S_w ⊆ {u}) vs restricted I0 (zero point V \ S_w, m_u inside V). Smallest witnesses first.
import sys, json, itertools, collections, functools
sys.argv=['x','.','10']
src=open('research/tools/kill_tests/canon.py').read(); exec(src[:src.index("st=collections.Counter()")])
st=collections.Counter(); wit=[]
for name,n,S,G,outs in circuits():
    if n>8 or sum(1 for g in G if g[0]=='not')!=1 or not all(len(R)==2 for R in S): continue
    Wr=tables(n,G,'real'); W0=tables(n,G,0); W1=tables(n,G,1); FULLPT=(1<<n)-1
    if any(Wr[o]!=functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for o,R in zip(outs,S)): continue
    p=[k for k,g in enumerate(G) if g[0]=='not'][0]; h=Wr[G[p][1]]; hb=lambda x:(h>>x)&1
    def menu(R):
        Rm=sum(1<<u for u in R); top=FULLPT&~Rm; M=set()
        for z in range(1<<n):
            if z&Rm==0 and not hb(z): M|=merges(W1,n,G,R,z,{u:1<<u for u in R})
        per=[[x for x in range(1<<n) if hb(x) and (x&Rm)&~(1<<u)==0] for u in R]
        for ms in itertools.product(*per):
            M|=merges(W0,n,G,R,top,{u:ms[i]|1<<u for i,u in enumerate(R)})
        return M
    MEN=[menu(R) for R in S]; st['circuits']+=1
    m=len(S)
    for k in range(1,m):
        for F in itertools.combinations(range(m),k):
            Vm=0
            for w in F:
                for u in S[w]: Vm|=1<<u
            if Vm==FULLPT: continue
            for w in F:
                R=S[w]; Rm=sum(1<<u for u in R); z=Vm&~Rm
                per=[[x for x in range(1<<n) if hb(x) and x&~Vm==0 and (x&Rm)&~(1<<u)==0] for u in R]
                for ms in itertools.product(*per):
                    Mr=merges(W0,n,G,R,z,{u:ms[i]|1<<u for i,u in enumerate(R)})
                    st['restricted I0']+=1
                    if Mr-MEN[w]:
                        st['FAIL']+=1
                        wit.append((n,len(G),name,F,w,S[w],[v for v in range(n) if Vm>>v&1],[[v for v in range(n) if x>>v&1] for x in ms],sorted(Mr),sorted(MEN[w]),S,G,outs))
print(dict(st))
wit.sort(key=lambda t:(t[0],t[1],len(t[3])))
seen=set()
for t in wit:
    if t[2] in seen: continue
    seen.add(t[2]); print(t[:10])
    if len(seen)>=4: break
json.dump([dict(name=t[2],n=t[0],sets=t[10],gates=t[11],outs=t[12],F=list(t[3]),w=t[4],V=t[6],m=t[7],cls=t[8],menu=t[9]) for t in wit[:1]],open('research/heredity/witness.json','w'))
