"""FC' (function-level dichotomy max(C0(h),C1(h)) >= base-1) is false: n=6, sets w0={a,b,c,d}, {a,p1},{a,p2},{b,p1},{b,p2}, h = x_a ∨ x_b."""
from worlds import *
import time
a,b,c,d,p1,p2 = range(6)
n=6; sets=[[a,b,c,d],[a,p1],[a,p2],[b,p1],[b,p2]]
h=[1 if (x>>a&1 or x>>b&1) else 0 for x in range(1<<n)]
print('base', base(sets))
t=time.time(); r0=opt(n,specs0(n,sets,h)); print('C0',r0, time.time()-t)
t=time.time(); r1=opt(n,specs1(n,sets,h)); print('C1',r1, time.time()-t)
t=time.time(); rL=opt(n+1,specsL(n,sets,h),lo=5); print('L',rL, time.time()-t)
