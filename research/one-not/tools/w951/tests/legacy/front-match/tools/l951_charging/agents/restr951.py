import sys,time,collections
sys.argv=['x']
src=open('research/tools/l951_charging/merge951b.py').read().split('t0=time.time()')[0]
exec(src)
def restrict_count(n,gates,outs,p,Mset,keep):
    # constant-propagate x_v=1 for v in Mset; N (gate p) -> const 0 ; return #live gates for outputs in keep
    val={}  # wire -> ('c',0/1) or ('w',id) alias
    for v in Mset: val[v]=('c',1)
    alias={}
    def res(w):
        while w in alias: w=alias[w]
        return val.get(w,('w',w))
    for k,(op,a,b) in enumerate(gates):
        w=n+k
        if k==p: val[w]=('c',0); continue
        ra,rb=res(a),res(b)
        if ra[0]=='c' or rb[0]=='c':
            if ra[0]=='c' and rb[0]=='c':
                val[w]=('c',(ra[1]&rb[1]) if op=='and' else (ra[1]|rb[1]))
            else:
                c,o=(ra,rb) if ra[0]=='c' else (rb,ra)
                if op=='and': 
                    if c[1]==0: val[w]=('c',0)
                    else: alias[w]=o[1]
                else:
                    if c[1]==1: val[w]=('c',1)
                    else: alias[w]=o[1]
    live=set()
    def mark(w):
        r=res(w)
        if r[0]=='c': return
        w=r[1]
        if w<n or w in live: return
        live.add(w); op,a,b=gates[w-n]; mark(a); mark(b)
    for o in keep: mark(outs[o])
    return len(live)
t0=time.time()
systems=[(5,[(0,1,2),(0,3,4)]),(5,[(0,1,2),(2,3),(3,4,0)]),(6,[(0,1),(2,3),(4,5),(0,2,4)]),(6,[(0,1,2),(3,4,5),(0,3)]),(6,[(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)])]
for n,sets in systems:
    base=sum(len(S)-1 for S in sets); worst=None; cnt=0; hist=collections.Counter()
    for s in (base+2,base+3):
        for p in range(s-1):
            blocks=[]
            for it in range(15):
                if time.time()-t0>250: break
                cl,SEL,O=build(n,sets,s,p,blocks); S_=Glucose4(bootstrap_with=cl)
                if not S_.solve(): break
                gates,outs=decode(S_.get_model(),n,s,p,SEL,O); cnt+=1
                blocks.append([-SEL[k][0][gates[k][1]] for k in range(s)]+[-SEL[k][1][gates[k][2]] for k in range(s) if k!=p])
                hw=gates[p][1]
                h=lambda x: wires(n,gates,x)[hw]
                mins=[x for x in range(1<<n) if h(x) and all(not h(x&~(1<<i)) for i in range(n) if x>>i&1)]
                for m in mins:
                    Mset=[v for v in range(n) if m>>v&1]
                    keep=[i for i,S in enumerate(sets) if not (set(S)&set(Mset))]
                    hit=[i for i in range(len(sets)) if i not in keep]
                    lv=restrict_count(n,gates,outs,p,Mset,keep)
                    # monotone bound needs lv >= sum unhit; slack:
                    hist[('lv-unhit',lv-sum(len(sets[i])-1 for i in keep))]+=1
                    hist[('removed-hit', (s-lv)-sum(len(sets[i])-1 for i in hit)-0)]+=1
    print(sets,'circuits',cnt,sorted(hist.items()),flush=True)
