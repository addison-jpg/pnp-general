import sys, time
import networkx as nx
import base_exact as B
import fast_synth as F
which=sys.argv[1]; mode=sys.argv[2]; kmax=int(sys.argv[3])
S3=(7,[(0,1),(0,2),(0,3),(1,4),(2,5),(3,6)])
S2=(5,[(0,1),(0,2),(1,3),(2,4)])
C6=(6,[(i,(i+1)%6) for i in range(6)])
C7=(7,[(i,(i+1)%7) for i in range(7)])
Gs={'S3':S3,'S2':S2,'C6':C6,'C7':C7}
n,E=Gs[which]
G=nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E)
t0=time.time()
if mode=='base':
    r=B.min_size(G,1,kmax)
else:
    r=F.min_size(n,E,kmax)[0]
print(which,mode,'min=',r,'total %.1fs'%(time.time()-t0),flush=True)
