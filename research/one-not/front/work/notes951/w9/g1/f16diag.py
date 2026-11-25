# diag: for failing (t,W) of class-vector, show bad-set summary (forced coordinates) and counts
import json, cover2, itertools, sys
from cover import norm
J=json.load(open('uncovered_after_round7.json'))
orig=cover2.bottom_rule
def diag(sets,d,pts,Sv,l,P,sigma,Bs,explain=None,cls=None):
    ex=[]; r=orig(sets,d,pts,Sv,l,P,sigma,Bs,ex,cls)
    if r: return r
    Bl=sorted(Bs); idx={u:i for i,u in enumerate(Bl)}
    Us=set(u for u in Bs if cls[u] in 'US')
    pairs0=[tuple(sorted(S)) for S in sets if len(S)==2 and S<=Bs and (S&Us)]
    Np=sorted(Bs-Us)
    X=list(itertools.product((0,1),repeat=len(Bl)))
    e=ex[0]
    if e[0]=='U':
        t,W=e[1],e[2]
        prs=[p for p in pairs0 if not (t in p and (p[0] if p[1]==t else p[1]) not in W)]
        zsets=[(S&Bs)-{t} for S in Sv[t] if not (S&set(W))]
    elif e[0]=='V1':
        t,W=e[1],(); prs=pairs0; zsets=[(S&Bs)-{t} for S in Sv[t]]
    else: print('     PP',e); return r
    keyf=lambda x:(tuple(x[idx[u]] for u in Np),tuple(x[idx[a]]|x[idx[b]] for a,b in prs))
    Q=[x for x in X if all(x[idx[w]] for w in W)]
    good=set(keyf(x) for x in Q if any(all(x[idx[u]]==0 for u in Z) for Z in zsets))
    bad=[x for x in Q if keyf(x) not in good]
    meet=[S for S in sets if S&set(W)]
    forced=''.join((str(u)+'=1 ' if all(x[idx[u]] for x in bad) else str(u)+'=0 ' if not any(x[idx[u]] for x in bad) else '') for u in Bl) if bad else ''
    print('     B',''.join(map(str,Bl)),''.join(cls[u] for u in Bl),e,'nbad',len(bad),'/',len(Q),'forced:',forced,'| loss',sum(len(S)-1 for S in meet),'m',len(meet),'cls W',[cls[w] for w in W],'pairs',prs)
    return r
cover2.bottom_rule=diag
for r in J['systems']:
    if r['base']>16: break
    S=norm(r['sets']); print(r['rank'],r['sets']); cover2.feasible(S,True)
