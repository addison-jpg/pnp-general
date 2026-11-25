#!/usr/bin/env python3
"""FJ form for h = x0 OR x1 (h NOT forced to be a gate, cost not counted): SAT at G = base-1 for every
distinct system in sath2_log.jsonl. FJ predicts UNSAT. Appends to satfj_log.jsonl."""
import json, sys, sath2, multiprocessing as mp
TO=int(sys.argv[1]); seen=set(); res={}
def run(q,n,sets,G): q.put(sath2.search(n,sets,G,force_h=False)[0] is not None)
for line in open('sath2_log.jsonl'):
    r=json.loads(line); key=json.dumps(r['sets'])
    if key in seen: continue
    seen.add(key)
    q=mp.Queue(); p=mp.Process(target=run,args=(q,r['n'],r['sets'],r['base']-1)); p.start(); p.join(TO)
    if p.is_alive(): p.terminate(); out='TIMEOUT'
    else: out='SAT' if q.get() else 'UNSAT'
    res[out]=res.get(out,0)+1
    open('satfj_log.jsonl','a').write(json.dumps(dict(n=r['n'],sets=r['sets'],base=r['base'],G=r['base']-1,res=out))+'\n')
    if out=='SAT': print('FJ VIOLATION',r['sets'])
print(res)
