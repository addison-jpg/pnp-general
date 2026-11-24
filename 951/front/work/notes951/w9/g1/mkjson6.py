# mkjson5.py: merge frontier_245pqrasb_*.pkl into uncovered_after_round6.json (sorted by base, n, #pairs). Round 5 = rules a, s, b.
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
RULES='245pqrasbn'
new=merged(RULES); old=merged('245pqrasb')
L=sorted(new.items(),key=lambda kv:(kv[1]['base'],kv[1]['n'],kv[1]['npairs'],kv[1]['sets']))
recs=[]
for i,(k,x) in enumerate(L):
    S=norm(x['sets']); d,pts,Sv,l,P=info(S)
    sc=feasible(S,True,RULES)
    recs.append(dict(rank=i,base=x['base'],n=x['n'],npairs=x['npairs'],nlines=len(x['sets'])-x['npairs'],
        sets=x['sets'],deg=[d[v] for v in pts],lines_per_point=[l[v] for v in pts],
        surviving_scenarios=[dict(sigma=s,B=list(B)) for s,B in sc[:6]],n_scenarios=len(sc),
        complete_at_this_n=(x['n']==8),sources=x['source'],also_frontier_under_245pqrasb=(k in old)))
cnt=lambda M: dict(sorted(collections.Counter((v['base']) for v in M.values()).items()))
out=dict(description=("Frontier of the g1 coverage checker after round 5 (cover2.py rules '"+RULES+"', pure DFS; rules a, s, b, n of "
    "frontier15_log.md): systems that are NOT covered, not small3, without R0 point, all of whose point deletions ARE covered. "
    "Sorted by base, n, #pairs. n=8 entries are COMPLETE; n>=9 entries come only from the data sets explored."),
  rules=RULES,count=len(recs),count_by_base=cnt(new),count_by_base_rules_245pqrasb=cnt(old),systems=recs)
json.dump(out,open('uncovered_after_round6.json','w'),indent=None,separators=(',',':'))
print('frontier',RULES,len(new),cnt(new)); print('frontier 245pqr',len(old),cnt(old))
print('n=8 by base new:',dict(sorted(collections.Counter(v['base'] for v in new.values() if v['n']==8).items())))
print('max sigma over surviving scenarios:',max(s['sigma'] for r in recs for s in r['surviving_scenarios']))
for r in recs[:14]: print(r['rank'],r['base'],r['n'],r['npairs'],r['sets'],r['n_scenarios'],[tuple(s['B']) for s in r['surviving_scenarios']])
