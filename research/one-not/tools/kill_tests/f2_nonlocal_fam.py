# Second method for F1/F2/F4/F5 at Q = empty: the bit-table definitions of family_table.py (its `build`, imported by text),
# gains and costs at every point.  python3 -I research/one-not/tools/kill_tests/f2_nonlocal_fam.py FILE.json [more files]
import sys, os, json
files=sys.argv[1:]; here=os.path.dirname(os.path.abspath(__file__))
src=open(os.path.join(here,'family_table.py')).read(); sys.argv=['x','research/one-not']
exec(src[:src.index("wit=sorted")])
for f in files:
    (name,n,S,G,outs),=load([f]); c=build(name,n,S,G,outs); assert c is not None, 'incorrect'
    base=sum(len(R)-1 for R in S); print(name,'n',n,'gates',len(G),'base',base)
    for fam in ('F1','F2','F4','F5'):
        def F(Q):
            cb=cube(c,Q); return {g for g,L in c['pw'][fam].items() if any(not any(Q>>u&1 for u in S[w]) and M&cb for w,M in L)}
        F0=F(0); r={v:(len(F0-F(1<<v)),sum(len(R)-1 for R in S if v in R)) for v in range(n)}
        print('  ',fam,'|F|',len(F0),'best gain-cost',max(g-q for g,q in r.values()),'STEP at Q=0:','HOLDS' if any(g>=q for g,q in r.values()) else 'FAILS',r if fam=='F5' else '')
