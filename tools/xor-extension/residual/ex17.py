# Machine check of the 17-gate residual-shape example (inputs y0..y3 = wires 0..3, x = wire 4)
import itertools
N=5
gates=[]
def add(op,*ins): gates.append((op,)+ins); return N+len(gates)-1
ny1=add('NOT',1); h1=add('OR',ny1,2)
u2=add('OR',0,1)
ny0=add('NOT',0); h2=add('AND',ny0,2)
u1=0; g=3
G1=add('AND',4,h1); H1=add('OR',G1,u1)
G2=add('OR',4,h2); H2=add('AND',G2,u2)
def xor(a,b):
    o=add('OR',a,b); n=add('AND',a,b); nn=add('NOT',n); return add('AND',o,nn)
X1=xor(g,H1); OUT=xor(X1,H2)
print('gates',len(gates))
def run(inp):
    w=list(inp)
    for gt in gates:
        if gt[0]=='NOT': w.append(1-w[gt[1]])
        elif gt[0]=='AND': w.append(w[gt[1]]&w[gt[2]])
        else: w.append(w[gt[1]]|w[gt[2]])
    return w
f=lambda y:y[3]^y[0]^((1-y[0])&y[1]&y[2])
ok=True; sens=set()
tab={0:[],1:[]}
for y in itertools.product((0,1),repeat=4):
    w0=run(list(y)+[0]); w1=run(list(y)+[1])
    if w0[OUT]!=f(y) or w1[OUT]!=1-f(y): ok=False
    sens.add((w0[H1]!=w1[H1], w0[H2]!=w1[H2]))
    tab[0].append(w0); tab[1].append(w1)
print('computes x XOR f:',ok,'| (H1 sensitive, H2 sensitive) patterns over y:',sens)
names={G1:'G1',H1:'H1',G2:'G2',H2:'H2'}
for c,drop in ((0,{G1,H1,G2}),(1,{G1,G2,H2})):
    cols={}
    wires=[i for i in range(N+len(gates)) if i!=4 and i not in drop]
    bad=[]
    for i in wires:
        col=tuple(r[i] for r in tab[c])
        if len(set(col))==1: bad.append(('const',i))
        elif col in cols: bad.append(('dup',cols[col],i))
        else: cols[col]=i
        comp=tuple(1-v for v in col)
    print('side',c,'kept gates',len([i for i in wires if i>=N]),'constant/duplicate wires:',bad)
ft=sum(f(y)<<sum(y[i]<<i for i in range(4)) for y in itertools.product((0,1),repeat=4))
print('f truth table int',ft)
import os
p=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','sizes4.txt')
if os.path.exists(p):
    sz=dict(tuple(map(int,l.split())) for l in open(p)); print('C(f)',sz[ft],'C(not f)',sz[65535^ft],'(-1 = more than 8)')
