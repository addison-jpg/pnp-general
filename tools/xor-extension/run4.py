import sys, time
from synth import synth, xor_ext
c = [tuple(map(int, l.split())) for l in open('cand4.txt')]
k, K = int(sys.argv[1]), int(sys.argv[2])
for idx, (f, m) in enumerate(c):
    if idx % K != k: continue
    t = time.time(); r = synth(5, xor_ext(4, f), m + 3)
    print('f', f, 'm', m, 'r', m + 3, 'SAT' if r else 'UNSAT', round(time.time() - t, 1), r, flush=True)
