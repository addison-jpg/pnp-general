import sys; sys.path.insert(0,'.'); sys.path.insert(0,'../tw')
from lib import *
import tw
F='/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/'
for f in ['w9/tw/cxtw3c.json','w9/tw/cxtw4c.json','w8/cx1.json','w8/cx2.json','w8/cx3.json','w8b/cxr.json']:
    c=load(F+f)[0]; n=c['n']
    print(f,'n',n,'s',len(c['gates']),'verify(ok,C0wrong,C1wrong)',verify(c) if n<=10 else '')
    h=hw(c)
    print('  heavy units',[u for u in range(n) if ev(n,c['gates'],unit(n,u))[h]],'hard',[ev(n,c['gates'],zQ(n,S))[h] for S in c['sets']])
    cq=tw.canonQ(c)
    for wi,S in enumerate(c['sets']):
        Q=cq[wi][0]
        g,wz,B=system(c,S,zQ(n,Q),{u:unit(n,u) for u in S}); Mc,cc=merges(c,S,B)
        z=zQ(n,S); g2,wz,B=system(c,S,z,{u:plus(z,u) for u in S}); Mr,cr=merges(c,S,B)
        print('  set',S,'Q',sorted(Q),'good',g,'Mc',Mc,'cntc',cc,'| R* good',g2,'Mr',Mr,'cntr',cr)
