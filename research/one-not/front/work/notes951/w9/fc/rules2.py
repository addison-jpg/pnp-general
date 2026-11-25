import sys, time, signal
from lib import *
from compat import famsearch, hf_of_circuit
from pool import mergesets, slack
from collections import Counter
def _h(*a): raise TimeoutError
signal.signal(signal.SIGALRM,_h)
t0=time.time()
for f in sys.argv[1:]:
    cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
    H=Counter(); step=max(1,len(cs)//150)
    for i,c in enumerate(cs):
        if time.time()-t0>260: break
        if i%step: continue
        for g in c['gates']:
            if g[0]=='not': del g[2:]
        big=[s for s in c['sets'] if len(s)>=3]
        if len(big)<2: H['<2 big sets']+=1; continue
        dem=[len(s)-1 for s in c['sets']]; base=sum(dem)
        try:
            signal.alarm(15); fam,sz=famsearch(c['n'],big,hf_of_circuit(c)); signal.alarm(0); sep=fam is not None
        except TimeoutError: sep='timeout'
        can=hbmatch(canon(c),dem)==base; rs=hbmatch(rstar(c),dem)==base
        H[('sep3',sep,'can',can,'rstar',rs)]+=1; H['n']+=1
        H['RULE(sep3 -> can -> rstar) ok']+= bool(sep is True or can or rs)
    print(f.split('/')[-1]); [print('   ',k,v) for k,v in H.items()]
