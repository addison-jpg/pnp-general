import random, itertools, sys
from cover import *
random.seed(1)
def core(sets):
    sets=norm(sets)
    while True:
        d=degs(sets); ch=False
        for v in d:
            if sum(1 for S in sets if v in S and len(S)>=3)<=1:
                sets=delete(sets,v); ch=True; break
        if not ch: return sets
def rnd(n,k4,tries=60):
    sets=[]
    for t in range(tries):
        k=4 if len([S for S in sets if len(S)==4])<k4 else random.choice([3,3,3,4])
        S=frozenset(random.sample(range(n),k))
        if all(len(S&T)<=1 for T in sets): sets.append(S)
    return sets
stat={}; unc={}
for it in range(int(sys.argv[1])):
    n=random.randint(7,11)
    c=core(rnd(n,random.randint(1,3),random.randint(8,60)))
    if not c or all(len(S)<=3 for S in c): continue
    d=degs(c); key=(len(d),sum(len(S)-1 for S in c))
    cv=covered(c)
    stat[cv]=stat.get(cv,0)+1
    if not cv:
        sig=(len(d),tuple(sorted(d.values())),tuple(sorted(len(S) for S in c)))
        if sig not in unc: unc[sig]=c
print(stat)
for sig in sorted(unc)[:12]:
    c=unc[sig]; print(sig,[sorted(S) for S in c],'scen',feasible(c,True)[:3], 'alldel covered',all(covered(delete(c,v)) for v in degs(c)))
