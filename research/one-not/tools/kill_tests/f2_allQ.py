# For one circuit file: at every Q with an alive set, MU (|F2(Q)| >= base(Q)) and the F2 STEP (some v with gain >= cost).
# python3 -I research/one-not/tools/kill_tests/f2_allQ.py FILE.json
import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from f2lib import *
d=json.load(open(sys.argv[1])); c=mk(d.get('name','x'),d['n'],d['sets'],d['gates'],d['outs'])
st=collections.Counter(); n=c['n']; memo={}
def f(Q):
    if Q not in memo: memo[Q]=F2(c,Q)
    return memo[Q]
worst=None
for Q in range(1<<n):
    al=aliveW(c,Q)
    if not al: continue
    st['Q with an alive set']+=1; F=f(Q); base=sum(len(c['S'][w])-1 for w in al)
    if len(F)<base: st['MU FAILS']+=1
    if not any(len(F-f(Q|1<<v))>=cost(c,Q,v) for v in apts(c,Q)):
        st['STEP FAILS']+=1
        if worst is None or bin(Q).count('1')>bin(worst).count('1'): worst=Q
    st['min slack']=min(st.get('min slack',99),len(F)-base)
print(c['name'],dict(st),'largest failing Q',[v for v in range(n) if worst is not None and worst>>v&1])
