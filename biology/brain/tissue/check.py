"""Cells join into sheets: epithelia as trivalent polygon tilings.
Run from repo root: python3 -I biology/brain/tissue/check.py
Standard library only. Exact Fraction arithmetic except the simulation (tested)."""
import json, random, time
from fractions import Fraction as Fr
from math import comb

T0 = time.time()
STATES = 0

# ---------- dual triangulation as a rotation system ----------
# vertex of the triangulation = cell; degree = number of sides of the cell.
def octahedron():
    pts = {0:(1,0,0),1:(-1,0,0),2:(0,1,0),3:(0,-1,0),4:(0,0,1),5:(0,0,-1)}
    tris = []
    for a in (0,1):
        for b in (2,3):
            for c in (4,5):
                p,q,r = pts[a],pts[b],pts[c]
                u=[q[i]-p[i] for i in range(3)]; v=[r[i]-p[i] for i in range(3)]
                n=(u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0])
                s=sum(n[i]*(p[i]+q[i]+r[i]) for i in range(3))
                tris.append((a,b,c) if s>0 else (a,c,b))
    return rot_from_tris(tris)

def rot_from_tris(tris):
    nxt = {}  # at vertex y: z -> x  for ccw triangle (x,y,z)
    for (x,y,z) in tris:
        for (a,b,c) in ((x,y,z),(y,z,x),(z,x,y)):
            nxt.setdefault(b,{})
            assert c not in nxt[b]
            nxt[b][c]=a
    rot={}
    for b,m in nxt.items():
        start=next(iter(m)); L=[start]; c=m[start]
        while c!=start: L.append(c); c=m[c]
        assert len(L)==len(m)
        rot[b]=L
    return rot

def tris_from_rot(rot):
    T=set()
    for y,L in rot.items():
        d=len(L)
        for k in range(d):
            z,x=L[k],L[(k+1)%d]
            t=(x,y,z); m=min(range(3),key=lambda i:t[i]); T.add(t[m:]+t[:m])
    return T

def euler_ok(rot):
    V=len(rot); E2=sum(len(L) for L in rot.values()); T=tris_from_rot(rot)
    assert E2%2==0 and 3*len(T)==E2
    # consistency: rebuild rotation from triangles gives same cyclic lists
    R2=rot_from_tris(list(T))
    for v,L in rot.items():
        M=R2[v]; i=M.index(L[0]); assert M[i:]+M[:i]==L
    chi = V - E2//2 + len(T)       # V,E,F of triangulation = F,E,V of the cell tiling
    return chi, V, E2//2, len(T)

def divide(rot, v, i, j, new):
    """Cell v divides; the division line cuts the walls to neighbours L[i], L[j] (i<j, non-adjacent)."""
    L=rot[v]; d=len(L); v1,v2=new,new+1
    A=L[i:j+1]; B=L[j:]+L[:i+1]
    rot[v1]=A+[v2]; rot[v2]=B+[v1]; del rot[v]
    for k,n in enumerate(L):
        R=rot[n]; p=R.index(v)
        if k==i: R[p:p+1]=[v1,v2]
        elif k==j: R[p:p+1]=[v2,v1]
        elif i<k<j: R[p]=v1
        else: R[p]=v2
    return v1,v2

def flip(rot, a, b):
    """T1 transition = edge flip of the dual triangulation on edge ab. Returns (c,d) or None."""
    T=tris_from_rot(rot)
    def find(x,y):
        for t in T:
            for r in (t,t[1:]+t[:1],t[2:]+t[:2]):
                if r[0]==x and r[1]==y: return r
    t1=find(a,b); t2=find(b,a); c=t1[2]; d=t2[2]
    if c==d or d in rot[c] or len(rot[a])<4 or len(rot[b])<4: return None
    def norm(t): m=min(range(3),key=lambda i:t[i]); return t[m:]+t[:m]
    T.discard(norm(t1)); T.discard(norm(t2)); T.add(norm((a,d,c))); T.add(norm((d,b,c)))
    rot.clear(); rot.update(rot_from_tris(list(T)))
    return c,d

# ---------- 1. Euler: sum (6 - sides) = 12, mean = 6 - 12/F ----------
def check_euler(rot):
    chi,F,E,V=euler_ok(rot)
    assert chi==2 and 2*E==3*V              # trivalent cell tiling of a sphere
    s=[len(L) for L in rot.values()]
    assert sum(6-x for x in s)==12
    assert Fr(sum(s),F)==6-Fr(12,F)
    return F

# prisms: n-gon prism, cells = 2 n-gons + n squares (dual: bipyramid)
for n in range(3,41):
    tris=[]
    for k in range(n):
        a,b=k,(k+1)%n
        tris.append((a,b,n)); tris.append((b,a,n+1))
    rot=rot_from_tris(tris); assert check_euler(rot)==n+2; STATES+=1
print("1a. n-prism tilings n=3..40: sum(6-s)=12 and mean = 6-12/F exactly; PASS")

# ---------- 2. Gibson et al. 2006 Markov chain, exact ----------
def gibson_row(s):
    """s-sided cell -> daughter with 4+Bin(s-4,1/2) sides, then +1 side from neighbour divisions."""
    m=s-4
    return {5+k: Fr(comb(m,k),2**m) for k in range(m+1)}

for s in range(4,30):
    r=gibson_row(s); assert sum(r.values())==1
    # mean daughter = s/2 + 2: two daughters have s+4 sides in all
    assert sum((j-1)*p for j,p in r.items())==Fr(s,2)+2

def stationary(N):
    S=list(range(4,N+1)); n=len(S)
    P=[[Fr(0)]*n for _ in S]
    for a,s in enumerate(S):
        for j,p in gibson_row(s).items():
            P[a][min(j,N)-4]+=p
    # solve pi (P - I) = 0, sum pi = 1 : rows of A = columns of (P-I)^T
    A=[[P[a][b]-(1 if a==b else 0) for a in range(n)] for b in range(n)]
    A[-1]=[Fr(1)]*n; rhs=[Fr(0)]*(n-1)+[Fr(1)]
    M=[A[i]+[rhs[i]] for i in range(n)]
    for c in range(n):
        p=next(r for r in range(c,n) if M[r][c]!=0); M[c],M[p]=M[p],M[c]
        iv=1/M[c][c]; M[c]=[x*iv for x in M[c]]
        for r in range(n):
            if r!=c and M[r][c]!=0:
                f=M[r][c]; M[r]=[x-f*y for x,y in zip(M[r],M[c])]
    pi=[M[i][n] for i in range(n)]
    for b in range(n): assert sum(pi[a]*P[a][b] for a in range(n))==pi[b]
    return pi

pi16=stationary(16); pi24=stationary(24); STATES+=2
assert pi16[0]==0
for k in range(1,8): assert abs(pi16[k]-pi24[k])<Fr(1,10**12)
pct=[f"{float(100*x):.2f}" for x in pi24[1:7]]
assert pct==['28.88','46.40','20.85','3.59','0.27','0.01'], pct
mean=sum((4+a)*x for a,x in enumerate(pi24))
assert abs(mean-6)<Fr(1,10**12)
print("2. Gibson chain stationary (exact eigenvector, truncation N=24; N=16 agrees to 1e-12):")
print("   sides 5..10 percent:", pct, "; 4-sided: 0 ; mean sides = 6 to 1e-12; PASS")

# ---------- 3. simulation (tested) ----------
def simulate(seed, gens, binom=False):
    global STATES
    rng=random.Random(seed); rot=octahedron(); nxt=6
    for g in range(gens):
        cells=list(rot); rng.shuffle(cells)
        for v in cells:
            d=len(rot[v])
            pairs=[(i,j) for i in range(d) for j in range(i+2,d) if not (i==0 and j==d-1)]
            if binom:   # daughter gets 4+Bin(d-4,1/2) sides, as in the chain
                w=[comb(d-4,j-i-2) for (i,j) in pairs]
                i,j=rng.choices(pairs,weights=w)[0]
            else:
                i,j=rng.choice(pairs)
            divide(rot,v,i,j,nxt); nxt+=2; STATES+=1
    return rot

def dist(binom):
    agg={}; tot=0
    for seed in (1,2,3):
        rot=simulate(seed,10,binom)
        F=check_euler(rot); assert F==6*2**10
        for L in rot.values(): agg[len(L)]=agg.get(len(L),0)+1; tot+=1
    assert sum(agg.values())==tot==3*6144
    return [f"{100*agg.get(k,0)/tot:.1f}" for k in range(4,11)]
du=dist(False); db=dist(True)
assert du==['26.2','27.1','18.0','11.2','6.5','4.1','2.5'], du
assert db==['17.4','27.2','23.5','15.3','8.7','4.4','2.0'], db
print("3. simulation, 3 seeds x 6144 cells, percent with 4..10 sides:")
print("   uniform non-adjacent cut pair :", du)
print("   binomial cut (chain's rule)   :", db)
print("   final maps: trivalent sphere, chi=2, sum(6-s)=12 exact; distributions tested")
# ---------- 4. T1 = edge flip ----------
rng=random.Random(7); rot=simulate(5,4); done=0
while done<200:
    a=rng.choice(list(rot)); b=rng.choice(rot[a])
    before={x:len(rot[x]) for x in rot}
    r=flip(rot,a,b)
    if r is None: continue
    c,d=r; after={x:len(rot[x]) for x in rot}
    for x in rot:
        delta=after[x]-before[x]
        assert delta==(-1 if x in (a,b) else 1 if x in (c,d) else 0)
    check_euler(rot); done+=1; STATES+=1
print("4. 200 random T1 transitions as dual edge flips: sides a,b -1, c,d +1, others 0; chi=2 kept; PASS")

# ---------- 6. neural tube: Euler characteristic of square-grid complexes ----------
def chi_grid(m,n,glue):
    """m x n square cells. glue=False: flat sheet (disk). glue=True: column 0 and column m identified (tube)."""
    def vid(i,j): return ((i%m) if glue else i, j)
    V={vid(i,j) for i in range(m+1) for j in range(n+1)}
    E=set()
    for i in range(m+1):
        for j in range(n+1):
            if i<m: E.add(frozenset((vid(i,j),vid(i+1,j))))
            if j<n: E.add((vid(i,j),vid(i,j+1)))
    return len(V)-len(E)+m*n
for m in range(3,9):
    for n in range(1,9):
        assert chi_grid(m,n,False)==1 and chi_grid(m,n,True)==0; STATES+=2
# closing both ends (neuropores): build the capped complex explicitly.
# Faces: the m*n squares plus one m-gon cap on ring j=0 and one on ring j=n.
def chi_capped(m,n):
    V={(i,j) for i in range(m) for j in range(n+1)}
    E=set(); F=[]
    for i in range(m):
        for j in range(n+1):
            E.add(frozenset(((i,j),((i+1)%m,j))))
            if j<n: E.add(frozenset(((i,j),(i,j+1))))
    for i in range(m):
        for j in range(n):
            F.append([(i,j),((i+1)%m,j),((i+1)%m,j+1),(i,j+1)])
    F.append([(i,0) for i in range(m)]); F.append([(i,n) for i in range(m)])
    # every face boundary is a cycle of existing edges; every edge lies on exactly 2 faces (closed surface)
    cnt={e:0 for e in E}
    for f in F:
        for k in range(len(f)):
            e=frozenset((f[k],f[(k+1)%len(f)])); assert e in E; cnt[e]+=1
    assert all(c==2 for c in cnt.values())
    return len(V)-len(E)+len(F)
for m in range(3,9):
    for n in range(1,9):
        assert chi_capped(m,n)==2; STATES+=1
print("6. sheet m x n (m=3..8,n=1..8): chi=1; rolled and fused into tube: chi=0; tube + 2 end caps: chi=2; PASS")

secs=round(time.time()-T0,2)
print("PASS")
print(json.dumps({"states":STATES,"seconds":secs}))
