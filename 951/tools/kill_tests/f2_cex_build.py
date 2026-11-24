# Builds the TWIN-TREE circuit (fable-f2-step): candidate counterexample to the F2 STEP at Q = ∅. Monotone except for one unread NOT.
# python3 -I 951/tools/kill_tests/f2_cex_build.py [out.json]
import sys,os,json; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
def build(pairs_of_leaves=3, read_not=False):
    k=pairs_of_leaves; m=2*k+1          # set size: k plain leaves, k junk leaves, one enabler
    n=2*m; A=list(range(m)); B=list(range(m,2*m))
    S=[A,B]+[[A[2*i+1],B[2*i+1]] for i in range(k)]
    G=[]; 
    def add(op,a,b=None):
        G.append([op,a] if b is None else [op,a,b]); return n+len(G)-1
    N=add('not',0 if not read_not else B[1])   # read_not: h = x_{B[1]}, the partner of A's first junk leaf
    outs=[]
    for X,Y in ((A,B),(B,A)):
        y=X[-1]; mer=[]
        for i in range(k):
            j=add('and',y,Y[2*i+1]); p=add('or',X[2*i+1],j); mer.append(add('or',X[2*i],p))
        while len(mer)>1: mer=[add('or',mer[0],mer[1])]+mer[2:]
        if read_not and X is A:
            # o_A = ((x_y OR x_b) AND NOT x_b) OR gf :  gf = o_A where x_b = 1 (junk term x_y x_b), and x_y OR gf = o_A where x_b = 0
            outs.append(add('or',add('and',add('or',y,B[1]),N),mer[0]))
        else: outs.append(add('or',mer[0],y))
    for i in range(k): outs.append(add('or',A[2*i+1],B[2*i+1]))
    return dict(name='TWIN-TREE%s k=%d'%('-N' if read_not else '',k),n=n,sets=S,gates=G,outs=outs)
if __name__=='__main__':
    from f2lib import *
    for k,rn in ((1,0),(2,0),(3,0),(3,1),(4,0)):
        d=build(k,rn); c=mk(d['name'],d['n'],d['sets'],d['gates'],d['outs'])
        if c is None: print(k,'INCORRECT'); continue
        F,r=stepinfo(c,0); base=sum(len(R)-1 for R in d['sets'])
        print(d['name'],'n',d['n'],'gates',len(d['gates']),'|F2|',len(F),'base',base,'gain,cost:',r,'STEP at Q=0:', 'HOLDS' if any(g>=q for g,q in r.values()) else 'FAILS')
        if k==3 and len(sys.argv)>1+rn: json.dump(d,open(sys.argv[1+rn],'w'))
