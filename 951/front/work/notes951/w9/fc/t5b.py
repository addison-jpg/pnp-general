import sys, json, time
from lib import *
c=json.load(open(sys.argv[1])); dem=[len(s)-1 for s in c['sets']]; base=sum(dem)
Dc=canon(c); Dr=rstar(c); print('canonical Hall',hbmatch(Dc,dem),'/',base,' R* Hall',hbmatch(Dr,dem),'/',base, 'coin .5:',mix(c,0.5))
if len(sys.argv)>2:
    t0=time.time(); L,lam,M=fraclp(c,False); print('FULL fraclp all-gate L*=%.4f'%L,[len(m) for m in M],round(time.time()-t0))
    t0=time.time(); L,lam,M=fraclp(c,True); print('FULL fraclp coneonly L*=%.4f'%L,[len(m) for m in M],round(time.time()-t0))
