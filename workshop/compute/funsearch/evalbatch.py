"""Batched exact scoring of one-NOT circuits on the tensor backend (one-not/tools/tensor: backend.py, bits.py; called, not edited).
A batch of B circuits on the same n inputs is ONE array program: wire tables [3B, n + G, W] (bit-sliced over all 2^n inputs,
bits.Ctx layout), one step per gate position, the gate kind selected by word masks, so there is no Python loop over inputs or over
circuits.  The three copies of each circuit are: as written, NOT forced to 0, NOT forced to 1 (the essential-NOT test).
On a GPU the backend is torch/cuda (auto-detected by backend.get_backend) and the proposer model sits on the same device.
Semantics = core.correct / bits.correct; every circuit found correct here is checked again with bits.correct (assert)."""
import os, sys
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'one-not', 'tools', 'tensor'))
import bits                                                           # noqa: E402

MAXN = 22
BUDGET = int(os.environ.get('FUNSEARCH_EVAL_BYTES', 768 << 20))

def structure(c, maxgates):
    """None if c is a well-formed circuit dict (binary and/or, unary not, wires in order), else the reason."""
    try:
        n, G, outs, sets = c['n'], c['gates'], c['outs'], c['sets']
        if not isinstance(G, list) or len(G) > maxgates: return 'too many gates'
        if not isinstance(outs, list) or len(outs) != len(sets): return 'need one output per set'
        for k, g in enumerate(G):
            if not isinstance(g, list) or not g or g[0] not in ('and', 'or', 'not'): return 'bad gate %d' % k
            if len(g) != (2 if g[0] == 'not' else 3): return 'bad arity at gate %d' % k
            if any(type(a) is not int or not 0 <= a < n + k for a in g[1:]): return 'bad wire at gate %d' % k
        if any(type(o) is not int or not 0 <= o < n + len(G) for o in outs): return 'bad output wire'
    except Exception as e: return 'malformed: %r' % (e,)
    return None

def normalise(c):
    """Merge structurally identical gates, drop gates no output reads.  The result is evaluated like any other circuit."""
    n = c['n']; memo = {}; G = []; m = list(range(n))
    for g in c['gates']:
        a = tuple(m[x] for x in g[1:]); key = (g[0],) + (tuple(sorted(a)) if g[0] != 'not' else a)
        if key not in memo: G.append([g[0]] + list(a)); memo[key] = n + len(G) - 1
        m.append(memo[key])
    outs = [m[o] for o in c['outs']]; keep = set(); st = [o for o in outs if o >= n]
    while st:
        x = st.pop()
        if x in keep: continue
        keep.add(x); st += [a for a in G[x - n][1:] if a >= n]
    order = sorted(keep); pos = {x: n + i for i, x in enumerate(order)}; f = lambda a: a if a < n else pos[a]
    return {'n': n, 'sets': c['sets'], 'gates': [[G[x - n][0]] + [f(a) for a in G[x - n][1:]] for x in order], 'outs': [f(o) for o in outs]}

def _idx(be, a):
    return be.t.from_numpy(np.ascontiguousarray(a)).to(be.dev) if be.name == 'torch' else a

def _tables(n, sets, be):
    cx = bits.ctx(n, be); X = cx.be.to_numpy(cx.X)[:n]
    tgt = np.stack([np.bitwise_or.reduce(X[list(S)], axis=0) for S in sets])
    return cx, X, tgt

def _run(cs, cx, X, tgt, be):
    """cs: normalised circuits, same n and sets.  -> (wrong outputs [3, B], wrong bit fraction [3, B])."""
    n = cs[0]['n']; B = len(cs); G = max(1, max(len(c['gates']) for c in cs)); m = len(tgt); W = cx.W
    op = np.full((3, B, G), 3, np.int64); ia = np.zeros((3, B, G), np.int64); ib = np.zeros((3, B, G), np.int64)
    out = np.zeros((3, B, m), np.int64)
    for b, c in enumerate(cs):
        for k, g in enumerate(c['gates']):
            code = {'and': 0, 'or': 1, 'not': 2}[g[0]]
            op[:, b, k] = code; ia[:, b, k] = g[1]; ib[:, b, k] = g[2] if code < 2 else g[1]
            if code == 2: op[1, b, k] = 4; op[2, b, k] = 5                     # forced to 0 / forced to 1
        out[:, b] = c['outs']
    op = op.reshape(3 * B, G); ia = ia.reshape(3 * B, G); ib = ib.reshape(3 * B, G); out = out.reshape(3 * B, m)
    ones = np.uint64(0xFFFFFFFFFFFFFFFF); VMn = np.uint64((1 << cx.nb) - 1)
    T0 = np.zeros((3 * B, n + G, W), np.uint64); T0[:, :n] = X[None]
    T = be.from_numpy(T0); ar = _idx(be, np.arange(3 * B)); VM = cx.VM
    for k in range(G):
        mk = lambda code: be.from_numpy(np.where(op[:, k] == code, ones, np.uint64(0))[:, None])
        a = T[ar, _idx(be, ia[:, k])]; b = T[ar, _idx(be, ib[:, k])]
        T[:, n + k] = ((a & b) & mk(0)) | ((a | b) & mk(1)) | ((~a & VM) & mk(2)) | (VM & mk(5))
    O = T[ar[:, None], _idx(be, out)]                                          # [3B, m, W]
    diff = be.to_numpy(O) ^ tgt[None]
    wrong = (diff != 0).any(axis=2).sum(axis=1).reshape(3, B)
    frac = (np.bitwise_count(diff & VMn).sum(axis=(1, 2)) / float(m * (1 << n))).reshape(3, B)
    return wrong, frac

def score(cands, n, sets, be=None, penalty=8):
    """cands: list of circuit dicts or None (the program failed).  -> list of result dicts
       {verdict: ok | VIOLATION-CANDIDATE | wrong | invalid, score, rank, gates, nots, essential, base, circuit}.
    score = base - gates for a correct circuit with at most one NOT gate (gates = all gates of the normalised circuit, NOT included,
    the measure of L_meta_951: gates.length).  A positive score is a candidate counterexample.
    rank orders the program database: a circuit whose NOT is not essential (forcing it to a constant keeps every output correct)
    cannot beat base (constant propagation leaves a monotone circuit, and those need base gates), so it ranks `penalty` lower."""
    assert n <= MAXN, 'n too large for exact truth tables here'
    be = be or bits._BE[0]
    if be.name == 'jax': be = bits.get_backend('numpy')                          # in-place wire assignment: numpy or torch only
    base = sum(len(S) - 1 for S in sets); res = [None] * len(cands); todo = []
    for i, c in enumerate(cands):
        why = 'program failed' if c is None else structure(dict(c, n=n, sets=sets), 4 * base + 64)
        if why: res[i] = {'verdict': 'invalid', 'why': why, 'score': -3.0 * base - 2, 'rank': -3.0 * base - 2 - penalty, 'base': base}; continue
        cn = normalise(dict(c, n=n, sets=sets)); k = sum(g[0] == 'not' for g in cn['gates'])
        if k > 1: res[i] = {'verdict': 'invalid', 'why': '%d NOT gates' % k, 'score': -3.0 * base - 1, 'rank': -3.0 * base - 1 - penalty, 'base': base}; continue
        todo.append((i, cn, k))
    if todo:
        cx, X, tgt = _tables(n, sets, be)
        todo.sort(key=lambda t: len(t[1]['gates'])); j = 0
        while j < len(todo):
            G = len(todo[j][1]['gates']); B = 1
            while j + B < len(todo) and 3 * (B + 1) * (n + len(todo[j + B][1]['gates'])) * cx.W * 8 <= BUDGET: B += 1
            chunk = todo[j:j + B]; j += B
            wrong, frac = _run([t[1] for t in chunk], cx, X, tgt, be)
            for b, (i, cn, k) in enumerate(chunk):
                g = len(cn['gates'])
                if wrong[0, b]:
                    s = -base - 1 - int(wrong[0, b]) - float(frac[0, b])
                    res[i] = {'verdict': 'wrong', 'score': s, 'rank': s - penalty, 'gates': g, 'nots': k, 'base': base, 'wrong_outputs': int(wrong[0, b])}
                    continue
                assert bits.correct(cn, be), 'batched evaluator and bits.correct disagree'
                ess = bool(k == 1 and wrong[1, b] and wrong[2, b]); s = base - g
                res[i] = {'verdict': 'VIOLATION-CANDIDATE' if s > 0 else 'ok', 'score': s, 'rank': s - (0 if ess else penalty), 'gates': g, 'nots': k,
                          'essential': ess, 'base': base, 'circuit': {'n': n, 'sets': [list(S) for S in sets], 'gates': cn['gates'], 'outs': cn['outs']}}
    return res
