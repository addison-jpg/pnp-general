# bitset truth-table toolkit for one-NOT circuits
import json, glob, itertools
F='/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/'
def norm(c):
    c['gates']=[['not',g[1]] if g[0]=='not' else list(g) for g in c['gates']]; return c
def load(f):
    if f.endswith('.json'): return [norm(json.load(open(F+f)))]
    return [norm(json.loads(l)) for l in open(F+f) if l.strip()]
def allcirc(big=True,jsonl=True):
    out=[]
    fs=sorted(glob.glob(F+'w8/cx*.json'))+[F+'w8b/cxr.json',F+'w9/fb/cfgI.json']+sorted(glob.glob(F+'w9/fc/*.json'))+sorted(glob.glob(F+'w9/tw/*.json'))
    for f in fs: out.append((f.replace(F,''),norm(json.load(open(f)))))
    if jsonl:
        for f in ['w7/badT.jsonl','w7/bad.jsonl','chk/c.jsonl']:
            for i,l in enumerate(open(F+f)):
                if l.strip(): out.append((f+':%d'%i,norm(json.loads(l))))
    return out
class TT:
    def __init__(s,c):
        s.c=c; n=s.n=c['n']; P=s.P=1<<n; s.FULL=(1<<P)-1
        var=[]
        for v in range(n):
            m=0
            for x in range(P):
                if x>>v&1: m|=1<<x
            var.append(m)
        s.var=var
        G=c['gates']; s.G=G
        s.Ni=[n+k for k,g in enumerate(G) if g[0]=='not']
        s.Ni=s.Ni[0] if s.Ni else None
        s.w={}
        for mode in ('real',0,1):
            w=list(var)
            for g in G:
                if g[0]=='not': w.append((s.FULL^w[g[1]]) if mode=='real' else (0 if mode==0 else s.FULL))
                elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
                else: w.append(w[g[1]]|w[g[2]])
            s.w[mode]=w
        s.h = s.w['real'][G[s.Ni-n][1]] if s.Ni is not None else 0
        s.U1=s.h; s.U0=s.FULL^s.h
        s.o=[]
        for S in c['sets']:
            m=0
            for u in S: m|=var[u]
            s.o.append(m)
        s.W=len(s.w['real'])
    def correct(s):
        return all(s.w['real'][o]==t for o,t in zip(s.c['outs'],s.o))
    def pt(s,bits):
        x=0
        for v in bits: x|=1<<v
        return x
