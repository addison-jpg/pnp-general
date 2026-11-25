import sys, json, glob
sys.path.insert(0,'..')
from g1lib import load, tts
from uni import *
stats={}; bad=[]; tot=use=0
for f in sys.argv[1:]:
    try: L=load(f)
    except Exception as e: print('skip',f,e); continue
    for c in L:
        if 'gates' not in c or 'sets' not in c or 'outs' not in c or c['n']>9: continue
        tot+=1
        T=tts(c)
        if not is_correct(c,T) or not is_clean_live(c,T): continue
        use+=1
        summarize(stats,check(c),c,bad)
print('circuits',tot,'correct+clean+live',use)
for k in sorted(stats): print(' %-18s instances %7d violations %4d min slack %s'%(k,*stats[k]))
for b in bad[:5]: print('BAD',b[0],b[1],json.dumps(b[2]))
