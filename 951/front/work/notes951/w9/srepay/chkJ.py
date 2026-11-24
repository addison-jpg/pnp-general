# check Lemma J (joint merges >= |V'|-c) and the charging inequality |X| >= coll + nonjoint - cyc on all data
import sys, collections, json
sys.argv=['x']
from analyze import *
from bt import allcirc
st=collections.Counter(); worst=[]
for name,c in allcirc():
    c=norm(c); T=info(c)
    if not T.correct(): st['incorrect']+=1; continue
    h0=(T.h&1)
    w=world1_merges(T)
    S=c['sets']; Vp={u for s_ in S for u in s_}; base=sum(len(s_)-1 for s_ in S)
    need=base-w['cyc']
    st['n']+=1
    if h0: st['h0=1']+=1; continue
    if len(w['J'])<need: st['J_VIOL']+=1; print('J VIOL',name)
    if not all(w['Mfull']): st['M_notfull']+=1
    lhs=len(w['X']); rhs=w['coll']+w['nonjoint']-w['cyc']
    if lhs<rhs: st['CHARGE_VIOL']+=1; print('CHARGE VIOL',name)
    if w['coll']>0: st['has_coll']+=1
    if w['cyc']>0: st['cyclic']+=1
    sM=len(T.GL); nonJ=sM-len(w['J'])
    worst.append((nonJ-(base-len(w['J'])), name, w['cyc'], sM-base))
print(dict(st))
worst.sort(); print('min over data of [#non-joint-merge gates - (base-|J|)] = s-1-base:',worst[:5])
