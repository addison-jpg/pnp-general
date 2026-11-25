# Kill test: "private" classes that are disjoint with no choice at all.
#   P(w) = {OR gates g : real g <= o_w  and  real g(e_u) = 1 for at least two u in S_w}
# P(w), P(w') are disjoint for w != w' (two atoms of w would lie in S_w'). On graph systems P(w) contains the
# output gate, which is the trivial proof of the bound there. Question: is |P(w)| >= d_w in general?
import sys, os, json, itertools, collections, functools
ROOT=sys.argv[1] if len(sys.argv)>1 else 'research/one-not'
sys.argv=['x',ROOT,'10']
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
st=collections.Counter(); bad=[]
for name,n,S,G,outs in circuits():
    if n>10 or sum(1 for g in G if g[0]=='not')!=1 or len(S)<2: continue
    Wr=tables(n,G,'real'); P_=1<<n
    osum=[functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for R in S]
    if any(Wr[o]!=t for o,t in zip(outs,osum)): continue
    if any(len(set(a)&set(b))>1 for a,b in itertools.combinations(S,2)) or any(len(R)<2 for R in S): continue
    st['circuits']+=1; graph=all(len(R)==2 for R in S); st['graph systems']+=graph
    tot=0; ok=True
    for w,R in enumerate(S):
        Pw=[n+k for k,g in enumerate(G) if g[0]=='or' and (Wr[n+k]&~osum[w])==0 and sum((Wr[n+k]>>(1<<u))&1 for u in R)>=2]
        st['sets']+=1; tot+=len(Pw)
        if len(Pw)>=len(R)-1: st['sets with |P(w)| >= d_w']+=1
        else: ok=False; bad.append((name.split('/')[-1],R,len(Pw),len(R)-1))
    st['circuits where every set has enough private gates']+=ok
    st['circuits with sum |P(w)| >= base']+=(tot>=sum(len(R)-1 for R in S))
for k,v in sorted(st.items()): print('%-52s %d'%(k,v))
print('FAIL examples',bad[:10])
