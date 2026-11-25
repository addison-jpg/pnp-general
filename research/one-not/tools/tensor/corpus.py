"""The stored corpus: every circuit dict in research/one-not/data (json / jsonl, including the witnesses and the general_count_below_base t4/t5/t6),
plus the f2lib corpus and random circuits when importable (the sources of A5_transfer_t1.py).  Deduplicated by content."""
import os, json, glob
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..'))

def _add(seen, name, d):
    if not (isinstance(d, dict) and all(k in d for k in ('n', 'sets', 'gates', 'outs'))): return
    if any(g[0] not in ('not', 'and', 'or', 'const') for g in d['gates']): return
    c = {'n': d['n'], 'sets': [list(s) for s in d['sets']], 'gates': [list(g) for g in d['gates']], 'outs': list(d['outs']), 'name': name}
    seen.setdefault(json.dumps([c['n'], c['sets'], c['gates'], c['outs']]), c)

def collect(maxn=12, data=True, f2lib=False):
    seen = {}; base = os.path.join(ROOT, 'one-not')
    if data:
        for f in sorted(glob.glob(os.path.join(base, 'data', '**', '*.json'), recursive=True)):
            try: d = json.load(open(f, encoding='utf-8'))
            except Exception: continue
            for i, x in enumerate(d if isinstance(d, list) else [d]):
                if isinstance(x, dict): _add(seen, '%s:%d' % (os.path.relpath(f, base), i), x.get('circuit', x))
        for f in sorted(glob.glob(os.path.join(base, 'research', 'open', '*.jsonl'))):
            for i, line in enumerate(open(f, encoding='utf-8')):
                try: d = json.loads(line)
                except Exception: continue
                if isinstance(d, dict): _add(seen, '%s:%d' % (os.path.basename(f), i), d.get('c', d.get('circuit', d)))
    if f2lib:
        import sys; sys.path.insert(0, os.path.join(base, 'tools', 'kill_tests'))
        try:
            import f2lib as L
            for c in L.corpus(9) + L.randgen(1, 3000): _add(seen, 'f2lib:' + c['name'], {'n': c['n'], 'sets': c['S'], 'gates': c['G'], 'outs': c['outs']})
        except Exception as e: print('f2lib not loaded:', e)
    return [c for c in seen.values() if c['n'] <= maxn]
