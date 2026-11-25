"""Shard job: slack at all 2^7 cubes for every circuit of the Fano corpus (80,198 circuits, any-gate slack as core.slack), tensor backend.
The corpus is rebuilt deterministically by research/one-not/tools/fano/fano_corpus.py (fixed seeds; it is not stored), or read with --corpus FILE.jsonl.
Circuit j belongs to shard j % N.  One JSON line per circuit: slack min / argmin / count of negative cubes / sum / crc32 of the int32 slack array.
    python3 -I research/one-not/tools/tensor/shard_fano.py --shard 0 --of 20 --out out.jsonl [--corpus FILE] [--limit K] [--verify M]
--verify M re-checks M random (circuit, cube) pairs against the slow core.slack and exits 1 on a mismatch."""
import os, sys, json, zlib, random, argparse
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, 'one-not', 'tools', 'search')); sys.path.insert(0, os.path.join(ROOT, 'one-not', 'tools', 'fano'))
import bits

def load(path):
    if path: return [json.loads(l) for l in open(path, encoding='utf-8')]
    import fano_corpus as F
    allc = [('FANO-FORMULA', F.fano_formula())]; sd = F.seeds(); allc += [('seed%d' % i, c) for i, c in enumerate(sd)]
    for r in (1, 2): allc += F.walk(sd, r)
    seen, out = set(), []
    for src, c in allc:
        key = json.dumps([c['gates'], c['outs']])
        if key in seen: continue
        seen.add(key); out.append({'src': src, 'ess': F.essential(c), **c})
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--shard', type=int, required=True); ap.add_argument('--of', type=int, required=True); ap.add_argument('--out', required=True)
    ap.add_argument('--corpus'); ap.add_argument('--limit', type=int); ap.add_argument('--verify', type=int, default=0)
    a = ap.parse_args(); assert 0 <= a.shard < a.of
    corp = load(a.corpus); print('corpus', len(corp), flush=True)
    if a.limit: corp = corp[:a.limit]
    mine = [(j, c) for j, c in enumerate(corp) if j % a.of == a.shard]
    rng = random.Random(a.shard); bad = 0; checks = []
    with open(a.out, 'w') as f:
        for j, c in mine:
            s = bits.slack_cubes(c, any_gate=True)
            f.write(json.dumps({'j': j, 'src': c['src'], 'ess': c['ess'], 'gates': len(c['gates']), 'min': int(s.min()), 'argmin': int(s.argmin()),
                                'neg': int((s < 0).sum()), 'sum': int(s.sum()), 'crc': zlib.crc32(s.astype('<i4').tobytes())}, separators=(',', ':')) + '\n')
            if a.verify and len(checks) < a.verify and rng.random() < 0.5: checks.append((c, int(rng.randrange(1 << c['n'])), s))
    if checks:
        import core
        for c, Q, s in checks:
            if core.slack(c, Q) != int(s[Q]): bad += 1; print('MISMATCH', c['src'], Q, core.slack(c, Q), int(s[Q]))
        print('verified', len(checks), 'samples,', bad, 'mismatches')
    print('shard', a.shard, 'of', a.of, ':', len(mine), 'circuits', flush=True)
    sys.exit(1 if bad else 0)
main()
