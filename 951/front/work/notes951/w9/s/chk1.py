from sl import *
import sys
cs=allcirc()
print(len(cs))
st=dict(sets=0,easy=0,hard=0,shortE=0,short0=0,short1=0,n0=0,n1=0,confEE=0,conf=0)
for name,c in cs:
    if c['n']>12: continue
    T,res=classes(c)
    if not T.correct(): print('INCORRECT',name); continue
    for wi,opt in enumerate(res):
        d=len(c['sets'][wi])-1; st['sets']+=1
        for k,cl in opt.items():
            if k[0]=='E':
                st['easy']+=1
                if len(cl)<d: st['shortE']+=1; print('shortE',name,wi)
            elif k[0]=='0':
                st['n0']+=1
                if len(cl)<d: st['short0']+=1; print('short0',name,wi,k)
            else:
                st['n1']+=1
                if len(cl[0])<cl[1]-1: st['short1']+=1; print('short1',name,wi,k)
print(st)
