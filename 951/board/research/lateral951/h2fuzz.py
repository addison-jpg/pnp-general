#!/usr/bin/env python3
"""Mutation fuzz for the H2 proof checker: start from hor2.build circuits, apply random rewiring / op flips /
gate insertions, keep mutants that still satisfy the lifted spec (gate 0 = x0|x1 untouched), run
h2proof.analyse (all proof steps as asserts) on every accepted mutant."""
import sys, random, hor2, h2proof
rng=random.Random(int(sys.argv[1])); T=int(sys.argv[2])
acc=0; withK=0; maxK=0; tight=0; hist={}
while acc<T:
    c=hor2.build(rng)
    if not c: continue
    n,sets,gates,outs=c; gates=list(gates); outs=list(outs)
    if len(sets)>6 or n>9: continue
    for step in range(40):
        g2=list(gates); o2=list(outs)
        r=rng.random()
        k=rng.randrange(1,len(g2))
        op,i,j=g2[k]
        if r<.35:
            x=rng.randrange(0,n+1+k)
            g2[k]=(op,x,j) if rng.random()<.5 else (op,i,x)
        elif r<.5:
            g2[k]=('and' if op=='or' else 'or',i,j)
        elif r<.9:
            # insert new gate at position k (wires >= n+1+k shift by one), then redirect one later input to it
            sh=lambda w: w+1 if w>=n+1+k else w
            a=rng.randrange(0,n+1+k); b=rng.randrange(0,n+1+k)
            new=(rng.choice(['or','and']),a,b)
            g2=g2[:k]+[new]+[(o,sh(x),sh(y)) for o,x,y in g2[k:]]
            o2=[sh(w) for w in o2]
            kk=rng.randrange(k+1,len(g2)); o,x,y=g2[kk]
            g2[kk]=(o,n+1+k,y) if rng.random()<.5 else (o,x,n+1+k)
        else:
            w=rng.randrange(len(o2)); o2[w]=n+1+rng.randrange(1,len(g2))
        if len(g2)>40: continue
        res=h2proof.analyse(n,sets,g2,o2)
        if res is None: continue
        gates,outs=g2,o2; acc+=1
        withK+=res['K']>0; maxK=max(maxK,res['K']); tight+=res['outside']==res['K']
        d=res['G']-res['base']; hist[d]=hist.get(d,0)+1
print('accepted mutants',acc,'with collisions',withK,'max K',maxK,'outside==K',tight,'min G-base',min(hist),'all asserts passed')
