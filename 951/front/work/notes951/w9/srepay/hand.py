# hand constructions for T2x4 (A={0..3}, B={4..7}), h = Th_2 on all 8 inputs; written to hand_*.json
import json, sys
sys.path.insert(0,'/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/w9/srepay')
from satfix import th2_tree
n=8; SETS=[[0,1,2,3],[4,5,6,7]]
class C:
    def __init__(s,pairs):
        s.G,s.h=th2_tree(pairs); s.wires={}
        # record named prefix wires: leaf ORs/ANDs
        s.N=s.add('not',s.h)
    def add(s,op,a,b=None):
        s.G.append([op,a] if op=='not' else [op,min(a,b),max(a,b)]); return n+len(s.G)-1
    def OR(s,*ws):
        cur=ws[0]
        for w in ws[1:]: cur=s.add('or',cur,w)
        return cur
    def find(s,op,a,b):
        a,b=min(a,b),max(a,b)
        for i,g in enumerate(s.G):
            if g[0]==op and g[1]==a and g[2]==b: return n+i
        return s.add(op,a,b)
    def dump(s,name,outs):
        c=dict(n=n,sets=SETS,gates=s.G,outs=outs); json.dump(c,open(name,'w')); return c
P1=[[0,1],[2,3],[4,5],[6,7]]; P2=[[0,4],[1,5],[2,6],[3,7]]
def essential_b(c,o456):
    # o_b = OR(456) ∨ (x7∧h) ∨ (N∧(x7∨h)) : C0 wrong at e7, C1 wrong on A-pairs
    t1=c.add('and',7,c.h); t2=c.add('or',7,c.h); t3=c.add('and',c.N,t2)
    return c.add('or',c.add('or',o456,t1),t3)
def essential_a(c,o012):
    t1=c.add('and',3,c.h); t2=c.add('or',3,c.h); t3=c.add('and',c.N,t2)
    return c.add('or',c.add('or',o012,t1),t3)
# H1: cross-pair Th2 tree, o_a monotone OR tree, o_b essential
c=C(P2); oa=c.OR(0,1,2,3); ob=essential_b(c,c.OR(4,5,6)); c.dump('hand_H1.json',[oa,ob])
# H1s: both outputs essential (symmetric)
c=C(P2); oa=essential_a(c,c.OR(0,1,2)); ob=essential_b(c,c.OR(4,5,6)); c.dump('hand_H1s.json',[oa,ob])
# H2: A/B Th2 tree (contains x0|x1, x2|x3, OR(A) ...), outputs essential reusing leaf ORs
c=C(P1); oa=essential_a(c,c.find('or',c.find('or',0,1),2)); ob=essential_b(c,c.find('or',c.find('or',4,5),6)); c.dump('hand_H2.json',[oa,ob])
# H3: selector-heavy: S1=(x0|x1)|(N&(x4|x5)), S2=(x2|x3)|(N&(x6|x7)), GA=S1|S2 (=OR(A) on U1, OR(all) on U0); mirror for B
#     o_a = (GA & h) | (N & OR(A)),  o_b = (GB & h) | (N & OR(B))
c=C(P1)
o01=c.find('or',0,1); o23=c.find('or',2,3); o45=c.find('or',4,5); o67=c.find('or',6,7)
oA=c.find('or',o01,o23); oB=c.find('or',o45,o67)
S1=c.add('or',o01,c.add('and',c.N,o45)); S2=c.add('or',o23,c.add('and',c.N,o67))
S3=c.add('or',o45,c.add('and',c.N,o01)); S4=c.add('or',o67,c.add('and',c.N,o23))
GA=c.add('or',S1,S2); GB=c.add('or',S3,S4)
oa=c.add('or',c.add('and',GA,c.h),c.add('and',c.N,oA)); ob=c.add('or',c.add('and',GB,c.h),c.add('and',c.N,oB))
c.dump('hand_H3.json',[oa,ob])
# H4: selectors shared: Q1 = (x0|x1) | (N&(x4|x5)) feeds o_a in world 0 and o_b in world 1 via masks
#     world-1 mask for b: m_b = N & OR(B) kills A-units on U0;  o_b = (Q & m_b) | (OR(B) & h)  [Q = Q1|Q2]
c=C(P1)
o01=c.find('or',0,1); o23=c.find('or',2,3); o45=c.find('or',4,5); o67=c.find('or',6,7)
oA=c.find('or',o01,o23); oB=c.find('or',o45,o67)
Q1=c.add('or',o01,c.add('and',c.N,o45)); Q2=c.add('or',o23,c.add('and',c.N,o67)); Q=c.add('or',Q1,Q2)
oa=c.add('or',c.add('and',Q,c.h),c.add('and',c.N,oA))
ob=c.add('or',c.add('and',Q,c.add('and',c.N,oB)),c.add('and',oB,c.h))
c.dump('hand_H4.json',[oa,ob])
# H5: cross-pair tree + selectors on cross ORs: the y-free cross ORs (x0|x4),(x1|x5),... are world-1 double merges
c=C(P2)
c04=c.find('or',0,4); c15=c.find('or',1,5); c26=c.find('or',2,6); c37=c.find('or',3,7)
U=c.find('or',c04,c15); V=c.find('or',c26,c37)   # OR{0,1,4,5}, OR{2,3,6,7}
ALL=c.add('or',U,V)
oA=c.OR(0,1,2,3); oB=c.OR(4,5,6,7)
oa=c.add('or',c.add('and',c.add('and',ALL,c.N),c.add('or',oA,c.h)),c.add('and',oA,c.h))   # = OR(A) on both worlds
ob=c.add('or',c.add('and',c.add('and',ALL,c.N),c.add('or',oB,c.h)),c.add('and',oB,c.h))
c.dump('hand_H5.json',[oa,ob])
print('ok')
