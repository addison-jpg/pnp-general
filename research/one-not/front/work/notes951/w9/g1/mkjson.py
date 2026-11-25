# mkjson.py: merge frontier_{RULES}_*.pkl into uncovered_after_pairs.json (sorted by base, n, #pairs) + comparison summary.
import pickle, glob, json, collections
from cover import norm
from cover2 import feasible, info
def merged(rules):
    M={}
    for f in sorted(glob.glob(f'frontier_{rules}_*.pkl')):
        for k,v in pickle.load(open(f,'rb')).items():
            if k in M:
                if v['source'] not in M[k]['source']: M[k]['source']+=','+v['source']
            else: M[k]=dict(v)
    return M
RULES='245pqr'
new=merged(RULES); old=merged('245'); mid=merged('245pq')
L=sorted(new.items(),key=lambda kv:(kv[1]['base'],kv[1]['n'],kv[1]['npairs'],kv[1]['sets']))
recs=[]
for i,(k,x) in enumerate(L):
    S=norm(x['sets']); d,pts,Sv,l,P=info(S)
    sc=feasible(S,True,RULES)
    recs.append(dict(rank=i,base=x['base'],n=x['n'],npairs=x['npairs'],nlines=len(x['sets'])-x['npairs'],
        sets=x['sets'],deg=[d[v] for v in pts],lines_per_point=[l[v] for v in pts],
        surviving_scenarios=[dict(sigma=s,B=list(B)) for s,B in sc[:6]],n_scenarios=len(sc),
        complete_at_this_n=(x['n']==8),sources=x['source'],
        also_frontier_under_round2_rules=(k in old)))
cnt=lambda M: dict(sorted(collections.Counter((v['base']) for v in M.values()).items()))
out=dict(
  description=("Frontier of the g1 coverage checker after the round-4 pair rules (cover2.py rules '"+RULES+"', pure DFS): "
    "systems that are NOT covered, are not small3, have no R0 point, and all of whose point deletions ARE covered. "
    "A SAT proof of s >= base (one NOT) for such a system makes it covered. Sorted by base, then n, then #pairs. "
    "n=8 entries are COMPLETE (all 8-point cores with any pair-sets; no cores on <= 7 points); n>=9 entries come only from the "
    "data sets explored (skeleton cores n=9,10 and their deletions; n=9 pair-core random sample of paircores.py)."),
  rules=RULES, count=len(recs),
  count_by_base=cnt(new), count_by_base_round2_rules_245=cnt(old), count_by_base_rules_245pq=cnt(mid),
  systems=recs)
json.dump(out,open('uncovered_after_pairs.json','w'),indent=None,separators=(',',':'))
print('frontier',RULES,len(new),cnt(new)); print('frontier 245pq',len(mid),cnt(mid)); print('frontier 245',len(old),cnt(old))
print('n=8 frontier by base (new):',dict(sorted(collections.Counter(v['base'] for v in new.values() if v['n']==8).items())))
print('n=8 frontier by base (old):',dict(sorted(collections.Counter(v['base'] for v in old.values() if v['n']==8).items())))
gone=[v for k,v in old.items() if k not in new and v['base']<=15]
print('round-2 frontier systems with base<=15 that are now covered:',len(gone))
for v in sorted(gone,key=lambda v:(v['base'],v['npairs']))[:6]: print('  ',v['base'],v['n'],v['sets'])
for r in recs[:10]: print(r['rank'],r['base'],r['n'],r['npairs'],r['sets'],r['n_scenarios'],r['surviving_scenarios'][:2])
