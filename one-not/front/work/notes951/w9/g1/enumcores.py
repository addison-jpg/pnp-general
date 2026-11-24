# level-wise enumeration (isomorph rejection) of partial linear spaces on n points with all lines of size >=3;
# output "skeleton cores": every point on >=2 lines, some line of size >=4.
import sys, itertools, pickle
def refine(n,sets,col):
    while True:
        sc=[tuple(sorted(col[v] for v in S)) for S in sets]
        new=[(col[v],tuple(sorted(sc[i] for i,S in enumerate(sets) if v in S))) for v in range(n)]
        m={k:i for i,k in enumerate(sorted(set(new)))}
        nc=[m[x] for x in new]
        if len(set(nc))==len(set(col)): return nc
        col=nc
def canon(n,sets):
    best=[None]
    mem=[frozenset(i for i,S in enumerate(sets) if v in S) for v in range(n)]
    def rec(col):
        col=refine(n,sets,col)
        cells={}
        for v,c in enumerate(col): cells.setdefault(c,[]).append(v)
        tgt=None
        for c in sorted(cells):
            if len(cells[c])>1: tgt=c; break
        if tgt is None:
            form=tuple(sorted(tuple(sorted(col[v] for v in S)) for S in sets))
            if best[0] is None or form<best[0]: best[0]=form
            return
        seen_tw=set()
        for v in cells[tgt]:
            tw=mem[v]
            if tw in seen_tw: continue
            seen_tw.add(tw)
            c2=[2*c+1 for c in col]; c2[v]-=1
            rec(c2)
    rec([0]*n)
    return best[0]
def gen(n,maxk=None):
    maxk=maxk or n
    allsets=[frozenset(c) for k in range(3,maxk+1) for c in itertools.combinations(range(n),k)]
    level={():[]}  # canon -> sets
    res={}
    tot=0
    while level:
        nxt={}
        for form,sets in level.items():
            tot+=1
            deg=[0]*n
            for S in sets:
                for v in S: deg[v]+=1
            if sets and min(deg)>=2 and max(len(S) for S in sets)>=4: res[form]=sets
            for S in allsets:
                if all(len(S&T)<=1 for T in sets):
                    ns=sets+[S]; f=canon(n,ns)
                    if f not in nxt: nxt[f]=ns
        level=nxt
        print('level size',len(level),'cores so far',len(res),flush=True)
    return list(res.values())
if __name__=='__main__':
    n=int(sys.argv[1]); R=gen(n)
    pickle.dump([[sorted(S) for S in sets] for sets in R],open(f'cores{n}.pkl','wb'))
    print('n',n,'skeleton cores',len(R))
