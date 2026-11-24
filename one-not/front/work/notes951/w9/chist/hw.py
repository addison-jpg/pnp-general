# h-adapted universal weightings on the B3 menu: z uniform on U0-part / U1-part of {z avoiding S_w}; p=0 (unit system)
from cxU3 import *
def rules(c):
    T=TT(c)
    if not T.correct(): return None
    n=T.n; W=T.w['real']; gates=range(n,T.W); dem=[len(s)-1 for s in c['sets']]
    nb=max(1,(1<<n)//8); tb={g:W[g].to_bytes(nb,'little') for g in gates}
    bit=lambda g,z: (tb[g][z>>3]>>(z&7))&1
    E={k:[] for k in ('zero','U0','U1','mix','min1','max0')}
    for wi,R in enumerate(c['sets']):
        rest=[v for v in range(n) if v not in R]; a0=collections.Counter(); a1=collections.Counter(); zs=[]
        for r in range(len(rest)+1):
            for zz in itertools.combinations(rest,r):
                z=sum(1<<v for v in zz)
                cl=frozenset(g for g in gates if not bit(g,z) and sum(bit(g,z|1<<u) for u in R)>=2)
                hz=(T.h>>z)&1; (a1 if hz else a0)[cl]+=1; zs.append((z,hz,cl))
                if z==0: E['zero'].append((wi,cl,1.0))
        s0=sum(a0.values()); s1=sum(a1.values())
        # minimal points of U1 / maximal points of U0 (within avoid S_w)
        mn=[(z,cl) for z,hz,cl in zs if hz and not any(h2 and z2!=z and (z2&z)==z2 for z2,h2,_ in zs)]
        mx=[(z,cl) for z,hz,cl in zs if not hz and not any((not h2) and z2!=z and (z2&z)==z for z2,h2,_ in zs)]
        for key,src,tot in (('U0',a0,s0),('U1',a1,s1)):
            if tot==0: src,tot=(a1,s1) if key=='U0' else (a0,s0)
            for cl,k in src.items(): E[key].append((wi,cl,k/tot))
        for cl,k in a0.items(): E['mix'].append((wi,cl,(0.5 if s1 else 1.0)*k/s0))
        for cl,k in a1.items(): E['mix'].append((wi,cl,(0.5 if s0 else 1.0)*k/s1))
        if not mn: mn=mx
        if not mx: mx=mn
        for z,cl in mn: E['min1'].append((wi,cl,1.0/len(mn)))
        for z,cl in mx: E['max0'].append((wi,cl,1.0/len(mx)))
    return {k:maxload(dem,v) for k,v in E.items()}
if __name__=='__main__':
    lo,hi=int(sys.argv[1]),int(sys.argv[2])
    cs=[(n,c) for n,c in allcirc()+extra() if lo<=c['n']<=hi and any(g[0]=='not' for g in c['gates'])]
    for k in (4,6):
        cs.append(('cxrb%d'%k,cxrb(k)))
    st=collections.Counter(); nboth=0
    for name,c in cs:
        if not (lo<=c['n']<=hi): continue
        r=rules(c)
        if r is None: continue
        for k,v in r.items():
            if v>1+1e-7: st[k]+=1
        if min(r['U0'],r['U1'])>1+1e-7: st['bestU0U1']+=1
        if min(r.values())>1+1e-7: st['all']+=1
        if hi>7 or max(r.values())>1+1e-7 and c['n']>=7: print(name,c['n'],{k:round(v,3) for k,v in r.items()},flush=True)
    print('failures (>1) per rule:',st,'of',len(cs))
