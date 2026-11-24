# heavy-point restriction test: for heavy v (h(e_v)=1, v in a set), count gates removable after x_v:=0
# removable = syntactic const/copy propagation + function-level duplicates (const or equal to an earlier wire) + unread
import json, sys
def load(paths):
    for p in paths:
        if p.endswith('.jsonl'):
            for i,l in enumerate(open(p)):
                l=l.strip()
                if l: yield f"{p.split('/')[-1]}:{i}", json.loads(l)
        else:
            yield p.split('/')[-1], json.load(open(p))
def tts(n, gates, fix=None):
    N=1<<n; full=(1<<N)-1
    var=[]
    for i in range(n):
        t=0
        for x in range(N):
            if (x>>i)&1: t|=1<<x
        var.append(t)
    w=list(var)
    if fix is not None:
        v,b=fix; w[v]= full if b else 0
    for g in gates:
        if g[0]=='or': w.append(w[g[1]]|w[g[2]])
        elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
        elif g[0]=='not': w.append(full^w[g[1]])
    return w, full
def analyse(c):
    n=c['n']; gates=c['gates']; sets=c['sets']; outs=c['outs']; s=len(gates)
    base=sum(len(S)-1 for S in sets)
    w,full=tts(n,gates)
    nots=[i for i,g in enumerate(gates) if g[0]=='not']
    if len(nots)!=1: return None
    hwire=gates[nots[0]][1]; h=w[hwire]
    pts=set(u for S in sets for u in S)
    heavy=[v for v in sorted(pts) if (h>>(1<<v))&1]
    res=[]
    for v in sorted(pts):
        wr,_=tts(n,gates,(v,0))
        # restricted functions live on the half cube x_v=0; mask
        mask=0
        for x in range(1<<n):
            if not (x>>v)&1: mask|=1<<x
        f=[t&mask for t in wr]
        seen={}
        for i in range(n): seen.setdefault(f[i],i)
        seen.setdefault(0,-1); seen.setdefault(mask,-2)
        rem=set()
        for j in range(s):
            k=n+j
            if f[k] in seen: rem.add(k)
            else: seen[f[k]]=k
        # outputs: map each output to its representative; compute live (read) gates from outputs through non-removed gates
        rep={}
        for i in range(n): rep[i]=i
        # representative wire for each wire
        first={}
        for k in range(n+s):
            first.setdefault(f[k],k)
        live=set(); stack=[first[f[o]] for o in outs]
        while stack:
            k=stack.pop()
            if k<n or k in live: continue
            live.add(k)
            g=gates[k-n]
            for a in g[1:]: stack.append(first[f[a]])
        # NOT's input changes under restriction; live NOT ok.
        removed=s-len(live)
        deg=sum(1 for S in sets if v in S)
        newsets=[[u for u in S if u!=v] for S in sets]
        base2=sum(max(len(S)-1,0) for S in newsets)
        res.append(dict(v=v,heavy=v in heavy,deg=deg,removed=removed,delta=removed-(base-base2)))
    C0wrong=False; C1wrong=False
    return dict(s=s,base=base,heavy=heavy,res=res)
if __name__=='__main__':
    tot=0; nh=0; worst={}
    for name,c in load(sys.argv[1:]):
        if c['n']>14: continue
        r=analyse(c)
        if r is None: continue
        tot+=1
        hv=[x for x in r['res'] if x['heavy']]
        if hv: nh+=1
        for x in r['res']:
            key='heavy' if x['heavy'] else 'light'
            d=x['delta']
            if key not in worst or d<worst[key][0]: worst[key]=(d,name,x,r['s']-r['base'])
            if x['heavy'] and d<0: print('HEAVY delta<0',name,x,'excess',r['s']-r['base'])
    print('circuits',tot,'with heavy point in a set',nh)
    for k,v in worst.items(): print(k,'min delta',v)
