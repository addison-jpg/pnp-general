import sys, json, itertools
sys.path.insert(0,'../../w8')
from verify import verify
from top2 import top2
from collections import Counter
for f in sys.argv[1:]:
    cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
    H=Counter()
    for c in cs:
        if not any(len(s)>=3 for s in c['sets']): continue
        c['gates']=[['not',g[1]] if g[0]=='not' else list(g) for g in c['gates']]
        v=verify(c)
        if not v['correct']: H['incorrect']+=1; continue
        r=top2(c); H[('clean' if v['clean'] else 'unclean',r[0])]+=1
    print(f.split('/')[-1],dict(H))
