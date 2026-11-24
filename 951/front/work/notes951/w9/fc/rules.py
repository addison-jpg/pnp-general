import sys, time, signal
from lib import *
from compat import famsearch, hf_of_circuit
from collections import Counter
def ev_rules(c):
    dem=[len(s)-1 for s in c['sets']]; base=sum(dem)
    can=hbmatch(canon(c),dem)==base; rs=hbmatch(rstar(c),dem)==base
    try:
        signal.alarm(20); fam,sz=famsearch(c['n'],c['sets'],hf_of_circuit(c)); signal.alarm(0); sep=fam is not None
    except TimeoutError: sep=None
    return dict(sep=sep,can=can,rstar=rs,thmX=family(c) is not None)
def _h(*a): raise TimeoutError
signal.signal(signal.SIGALRM,_h)
if __name__=='__main__':
    t0=time.time()
    for f in sys.argv[1:]:
        cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
        H=Counter()
        for i,c in enumerate(cs):
            if time.time()-t0>250: break
            for g in c['gates']:
                if g[0]=='not': del g[2:]
            if len(cs)>300 and i%(len(cs)//300): continue
            r=ev_rules(c); H[tuple(sorted(r.items()))]+=1
            H['RULE sep|can|rstar ok']+= bool(r['sep'] or r['can'] or r['rstar']); H['n']+=1
        print(f.split('/')[-1]); [print('   ',k,v) for k,v in H.items()]
