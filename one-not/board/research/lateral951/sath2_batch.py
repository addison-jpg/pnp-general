#!/usr/bin/env python3
"""Batch H2 hunt: random (1,1)-disjoint systems on n<=8 points with a=0,b=1, pi>=2; for each, SAT at
G=base-2 (951 refuted if SAT), G=base-1 (H2 violated if SAT), G=base (s=base+1). Appends to sath2_log.jsonl."""
import random, sys, json, time, itertools, multiprocessing as mp
import sath2
def gen(rng,nmax):
    n=rng.randint(6,nmax); pts=list(range(2,n)); sets=[]
    ok=lambda S: all(len(set(S)&set(T))<=1 for T in sets) and S not in sets
    for _ in range(40):
        typ=rng.choice('AAABBBNX'); k=rng.randint(1,3)
        if typ=='N': S=sorted(rng.sample(pts,min(len(pts),k+1)))
        elif typ=='X': S=[0,1]+sorted(rng.sample(pts,rng.randint(0,2)))
        else: S=[0 if typ=='A' else 1]+sorted(rng.sample(pts,k))
        if ok(S): sets.append(S)
        if sum(len(S)-1 for S in sets)>=rng.choice([7,8,9,10,11]): break
    A=[S for S in sets if 0 in S and 1 not in S]; B=[S for S in sets if 1 in S and 0 not in S]
    pi=sum(1 for p in pts if any(p in S for S in A) and any(p in S for S in B))
    used=sorted(set(u for S in sets for u in S))
    if pi<2 or used!=list(range(len(used))) : return None
    return len(used),sets,pi
def job(arg):
    n,sets,pi,G=arg
    def run(q): q.put(sath2.search(n,sets,G))
    q=mp.Queue(); p=mp.Process(target=run,args=(q,)); p.start(); p.join(TO)
    if p.is_alive(): p.terminate(); return dict(n=n,sets=sets,pi=pi,G=G,res='TIMEOUT')
    sol,t=q.get()
    return dict(n=n,sets=sets,pi=pi,G=G,res='SAT' if sol else 'UNSAT',t=round(t,1),sol=sath2.to_real(sol) if sol else None)
if __name__=='__main__':
    seed=int(sys.argv[1]); cnt=int(sys.argv[2]); TO=int(sys.argv[3]); nmax=int(sys.argv[4]) if len(sys.argv)>4 else 8
    rng=random.Random(seed); seen=set(); jobs=[]
    while len(seen)<cnt:
        g=gen(rng,nmax)
        if not g: continue
        key=json.dumps(g[1])
        if key in seen: continue
        seen.add(key); base=sum(len(S)-1 for S in g[1])
        for G in (base-2,base-1,base): jobs.append((g[0],g[1],g[2],G))
    with open('sath2_log.jsonl','a') as f:
        for a in jobs:
            r=job(a); r['base']=sum(len(S)-1 for S in r['sets']); f.write(json.dumps(r)+'\n'); f.flush()
