# Configuration (I) inside the hard case: cx1 with set a recomputed as o_a = A | x3, A = P & Q (AND gate, 3 units, A == OR{0,1,2}).
import json, sys
sys.path.insert(0,'../../w8'); sys.path.insert(0,'..')
from verify import verify
c=json.load(open('../../w8/cx1.json')); n=c['n']; G=[list(g) for g in c['gates']]; outs=list(c['outs'])
H=13; N=14  # h = OR(x1..x6), N = not h   (cx1 wires)
def add(op,a,b): G.append([op,a,b]); return n+len(G)-1
p=add('or',0,n+G.index(['and',7,13])); p=add('or',p,1); P=add('or',p,2)
q=add('or',n+G.index(['or',0,14]),1); Q=add('or',q,2)
A=add('and',P,Q); oa=add('or',A,3)
outs[0]=oa
# drop gates only used by the old o_a (unread): iterate
c2={'n':n,'sets':c['sets'],'gates':G,'outs':outs}
def prune(c):
    n,G,outs=c['n'],c['gates'],c['outs']
    while True:
        read=set(j for g in G for j in g[1:])|set(outs)
        dead=[k for k in range(len(G)) if n+k not in read]
        if not dead: return c
        k=dead[-1]; mp=lambda j: j if j<n+k else j-1
        G=[[g[0]]+[mp(j) for j in g[1:]] for i,g in enumerate(G) if i!=k]; outs=[mp(o) for o in outs]
        c={'n':n,'sets':c['sets'],'gates':G,'outs':outs}
c2=prune(c2); print(verify(c2)); json.dump(c2,open('cfgI.json','w')); print(json.dumps(c2))
