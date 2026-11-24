# Run from the repository root:  ls <circuit .json files> | python3 951/tools/research951/induct/outpeel.py
"""Output-peel test: is the output wire o_w in EVERY pure class of w?  in SOME?  in a class of another set v?
If o_w ∈ every class of w and in no class of v != w, PureSDR for (S, d) reduces to PureSDR for the classes minus outputs
(d_w - 1 gates each), i.e. an induction on d that bottoms out in the graph case (s >= #outputs)."""
import sys, json, collections
import os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'mtest.py')).read(); exec(src[:src.index("tot = {")])
st = collections.Counter(); ex = []
for path in sys.stdin.read().split():
    d = json.load(open(path)); n, S, G, outs = d['n'], d['sets'], d['gates'], d['outs']
    if n > 13: continue
    st['circuits'] += 1
    Me = menus_of(n, S, G)
    for w in range(len(S)):
        st['sets'] += 1
        inall = all(outs[w] in C for C in Me[w]); insome = any(outs[w] in C for C in Me[w])
        st['o_w in EVERY class of w'] += inall; st['o_w in SOME class of w'] += insome
        oth = [v for v in range(len(S)) if v != w and any(outs[w] in C for C in Me[v])]
        st['o_w in a class of another set'] += bool(oth)
        if not inall and len(ex) < 6: ex.append((path.split('/')[-1], w, S[w], outs[w], [sorted(C) for C in Me[w]]))
for k, v in st.items(): print('%-40s %d' % (k, v))
for e in ex: print('NOT-IN-ALL', e)
