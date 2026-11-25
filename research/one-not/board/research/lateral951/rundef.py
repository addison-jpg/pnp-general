import sys, json, defect
def load(fn):
    t=open(fn).read().strip()
    try:
        j=json.loads(t); js=j if isinstance(j,list) else [j]
    except Exception:
        js=[json.loads(l) for l in t.splitlines() if l.strip()]
    out=[]
    for c in js:
        if isinstance(c,dict) and 'gates' in c and 'sets' in c and 'outs' in c: out.append(c)
        elif isinstance(c,dict):
            for v in c.values():
                if isinstance(v,dict) and 'gates' in v and 'outs' in v: out.append(v)
    return out
tot=0; viol=0; mn=None
for fn in sys.argv[1:]:
    for c in load(fn):
        if c['n']>13: print(fn.split('/')[-1],'skip n=',c['n']); continue
        try: r=defect.run(c)
        except AssertionError as e:
            print(fn,'ASSERT FAIL'); raise
        if r is None or 'bad' in r: print(fn.split('/')[-1],'skipped',r); continue
        tot+=1; mg=r['rest']-r['excess']; viol+=mg<0
        if mn is None or mg<mn: mn=mg
        if len(sys.argv)<60: print(fn.split('/')[-1],r)
print('total',tot,'D violations',viol,'min margin',mn)
