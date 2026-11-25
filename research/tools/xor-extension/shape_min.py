import time
from synth import synth, xor_ext
sz = {}
for l in open('sizes3.txt'):
    u, w = l.split(); sz[int(u)] = int(w)
# 2-variable f embedded in 3 vars, and a few 3-var ones
for f in [8, 6, 2, 14, 143, 46, 60]:
    m = min(sz[f], sz[255 ^ f]); M = max(sz[f], sz[255 ^ f])
    for r in range(m + 3, m + 8):
        t = time.time(); c = synth(4, xor_ext(3, f), r, True)
        if c:
            print('f', f, '(C,Cnot)=', (sz[f], sz[255 ^ f]), 'least shape size', r, '= min+%d' % (r - m), c, flush=True); break
        if time.time() - t > 300: print('f', f, 'slow at', r); break
    else: print('f', f, 'no shape circuit up to min+7', flush=True)
