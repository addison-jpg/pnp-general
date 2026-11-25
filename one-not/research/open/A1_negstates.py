"""Seat A1: mixed states of negative slack and where the mixed step fails. Run from the repo root:
   python3 -I one-not/research/open/A1_negstates.py FILE.json ...  (F2 = OR gates only, and any gate type)"""
import sys, os, json
sys.path.insert(0, 'one-not/tools/search')
import numpy as np
import continuous as C, core
def analyze(f, any_gate):
    c = C.load(f); n = c['n']
    assert C.is_correct(c)
    tab = {R: C.slack_table(c, R, any_gate=any_gate, parts=True) for R in range(1 << n)}
    neg = 0; negfail = 0; posfail = 0; pos = 0; mn = 0; ex = None
    for R in range(1 << n):
        cnt, base = tab[R]; sl = cnt - base; fr = C.free_points(n, R)
        for j in range(len(sl)):
            if base[j] == 0: continue
            pos += 1
            ok = False
            for i, v in enumerate(fr):
                if j >> i & 1: continue
                a = j | (1 << i)
                if base[a] < base[j] and sl[a] <= sl[j]: ok = True; break
                c2, b2 = tab[R | 1 << v]; jj = (j & ((1 << i) - 1)) | ((j >> (i + 1)) << i)
                if b2[jj] < base[j] and c2[jj] - b2[jj] <= sl[j]: ok = True; break
            if sl[j] < 0:
                neg += 1; mn = min(mn, int(sl[j]))
                if not ok: negfail += 1; ex = ex or (R, [fr[i] for i in range(len(fr)) if j >> i & 1], int(sl[j]))
            elif not ok: posfail += 1
    print(os.path.basename(f), 'any_gate' if any_gate else 'OR-only(F2)', 'nots', core.nots(c), 'gates', len(c['gates']),
          'slack(0,0)=', int(tab[0][0][0] - tab[0][1][0]), 'states base>0', pos, 'negative', neg, 'min', mn,
          'neg w/o step', negfail, 'pos w/o step', posfail, 'example (R,Q,slack)', ex)
for f in sys.argv[1:]:
    for ag in (False, True): analyze(f, ag)
