import sys
import plane2
for q in (3,5,7):
    for T in range(1,q+1):
        try:
            C, lines, out, st = plane2.build(q, 2, T)
        except AssertionError as e:
            print(q,T,'assert',e); continue
        bad = plane2.verify_w2(C, lines, out) if q<7 else plane2.sample_w(C,lines,out,2,20000)[0]
        print(q, T, st, 'bad', bad, 'saving', st['base']-st['size'], flush=True)
