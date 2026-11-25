import sys,os,itertools,random; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from n1sat import solve
def monotone_hs(n):
    P=list(range(1<<n)); res=[]
    def is_up(f): return all(f[A|1<<u]>=f[A] for A in P for u in range(n))
    for bits in range(1<<(1<<n)):
        f=[bits>>A&1 for A in P]
        if is_up(f): res.append(f)
    return res
def C_ok(n,sets,f,trip):
    U=0
    for i in trip: U|=sum(1<<u for u in sets[i])
    comp=[A for A in range(1<<n) if A&U==0]
    for b in comp:
        good=True
        for j in trip:
            Sj=sum(1<<u for u in sets[j]); Xj=b|(U&~Sj)
            if f[Xj]==0: continue
            if all(f[b|1<<u] for u in range(n) if (U&~Sj)>>u&1): continue
            good=False;break
        if good: return True
    return False
def run(name,n,sets,hs):
    tot=sat=0; ex=None
    for f in hs:
        if all(C_ok(n,sets,f,t) for t in itertools.combinations(range(len(sets)),3)):
            tot+=1
            r=solve(n,sets,lambda A:f[A],3)
            if r: sat+=1; ex=ex or f
    print(f"{name}: h satisfying C on all triples: {tot}; N1(k=3) SAT on {sat}", "example h-upset size %d"%sum(ex) if ex else "")
H4=monotone_hs(4); print("monotone h on n=4:",len(H4))
run("C4 of 2-sets {01,12,23,30}",4,[(0,1),(1,2),(2,3),(3,0)],H4)
run("4 edges of K4 {01,02,03,12}",4,[(0,1),(0,2),(0,3),(1,2)],H4)
run("star4 {01,02,03} + {12}",4,[(0,1),(0,2),(0,3),(1,2)],H4)
run("K4 triangle+pendant {01,12,02,03}",4,[(0,1),(1,2),(0,2),(0,3)],H4)
random.seed(1); n=6; P=range(64)
def rand_up():
    gens=random.sample(range(1,64),random.randint(1,4))
    return [int(any(A&g==g for g in gens)) for A in P]
hs=[rand_up() for _ in range(300)]+[[0]*64]
run("Pasch {012,034,135,245} (300 random h + monotone)",6,[(0,1,2),(0,3,4),(1,3,5),(2,4,5)],hs)
