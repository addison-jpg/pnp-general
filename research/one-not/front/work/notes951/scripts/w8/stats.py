import sys, json, os, glob
from collections import Counter
sys.path.insert(0,'../chk'); files=sys.argv[1:]; sys.argv=sys.argv[:1]
src=open('../chk/hallcheck.py').read().split('H=Counter()')[0]; os.chdir('../chk'); exec(src)
H=Counter()
for f in files:
    for l in open(f):
        c=conedbl.norm(json.loads(l)); Ds=canon(c); S=c['sets']; H['n']+=1
        big=[i for i,s in enumerate(S) if len(s)>=3]
        H['has set>=3']+=bool(big)
        sh=False; sh3=False; sh33=False
        for i in range(len(S)):
            for j in range(i+1,len(S)):
                if set(Ds[i])&set(Ds[j]):
                    sh=True
                    if len(S[i])>=3 or len(S[j])>=3: sh3=True
                    if len(S[i])>=3 and len(S[j])>=3: sh33=True
        H['shared']+=sh; H['shared involving set>=3']+=sh3; H['shared between two sets>=3']+=sh33
        # how often does the output-privacy alone already give the matching: demand minus 1 per set from non-output gates
print(files, dict(H))
