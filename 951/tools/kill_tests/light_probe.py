# Probes for LIGHT-COUNT (opus-light-count.md). Reuses mu_light.py up to the corpus build.
# Run: python3 -I 951/tools/kill_tests/light_probe.py 951 9
import sys, os, collections
_here=os.path.dirname(os.path.abspath(__file__))
_src=open(os.path.join(_here,'mu_light.py')).read(); exec(_src[:_src.index("for c in (FANO,JUNK):")])
def instances(kinds=('light',)):
    random.seed(1)
    for c in CS:
        n=c['n']; pairs=[(D,Q) for Q in range(1<<n) for D in range(1<<n) if not D&Q]
        if len(pairs)>2500: pairs=[(0,0)]+random.sample(pairs,2500)
        for D,Q in pairs:
            P=apts(c,D,Q)
            if not P: continue
            cb=cube(c,D,Q); hh=c['h']&cb
            kind='h const' if hh in (0,cb) else ('heavy' if any((c['h']>>(Q|1<<v))&1 for v in P) else 'light')
            if kind in kinds: yield c,D,Q,P
def light_instances(): return instances(('light',))
