# Count and STEP (families F1, F2, F4, F5) on every correct one-NOT circuit JSON under ROOT with n <= NMAX, at every cube,
# split by locality of the NOT input h on the cube (see f2_nonlocal_check.py).
# python3 -I one-not/tools/kill_tests/f2_nonlocal_suite.py [ROOT=951] [NMAX=9] [essential_only=0]
import sys, os, glob, json, itertools, collections
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from f2_nonlocal_check import analyse
ROOT=sys.argv[1] if len(sys.argv)>1 else 'one-not'; NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 9
tot=collections.Counter(); seen=set(); bad=[]; ncirc=0
for f in sorted(glob.glob(ROOT+'/**/*.json',recursive=True))+sorted(glob.glob(ROOT+'/**/*.jsonl',recursive=True)):
    try:
        if f.endswith('.jsonl'): items=[json.loads(l) for l in open(f) if l.strip()]
        else:
            d=json.load(open(f)); items=d if isinstance(d,list) else [d]
    except Exception: continue
    for i,c in enumerate(items):
        if not (isinstance(c,dict) and all(k in c for k in ('n','sets','gates','outs'))): continue
        try:
            G=[[g[0]]+[int(x) for x in g[1:]] for g in c['gates']]; S=[list(s) for s in c['sets']]; key=json.dumps([c['n'],S,G,c['outs']])
        except Exception: continue
        if key in seen or c['n']>NMAX or sum(g[0]=='not' for g in G)!=1 or len(G)==0: continue
        seen.add(key)
        if not all(g[0] in ('not','and','or') for g in G): continue
        if not (all(len(R)>=2 for R in S) and all(len(set(a)&set(b))<=1 for a,b in itertools.combinations(S,2))): continue
        try: r=analyse(dict(name=f,n=c['n'],sets=S,gates=G,outs=list(c['outs'])),verbose=False)
        except AssertionError: continue
        ncirc+=1
        for fam,x in r.items():
            for k in ('cubes','nonlocal_cubes','count_fail','step_fail','step_fail_nonlocal'): tot[(fam,k)]+=x[k]
            if x['step_fail_nonlocal'] or x['count_fail']: bad.append((fam,f,i,x['step_fail_nonlocal'],x['count_fail'],x['fail_Q'][:3]))
print('circuits',ncirc)
for fam in ('F1','F2','F4','F5'): print(fam,{k:tot[(fam,k)] for k in ('cubes','nonlocal_cubes','count_fail','step_fail','step_fail_nonlocal')})
for b in bad[:40]: print('  ',b)
