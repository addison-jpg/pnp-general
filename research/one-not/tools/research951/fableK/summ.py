import json,collections,sys
for name in sys.argv[1:]:
    R=[json.loads(l) for l in open(f'sweep_{name}.jsonl')]
    c=collections.Counter((r['C0'],r['C1'],r['L']) for r in R)
    print(name, len(R), 'min L', min(r['L'] for r in R), 'min max(C0,C1)', min(max(r['C0'],r['C1']) for r in R), 'max L-max(C0,C1)', max(r['L']-max(r['C0'],r['C1']) for r in R))
    print(sorted(c.items()))
    print(' W0 violations (C0h < base_hard):', [r for r in R if r['C0h'] < r['bh']][:5])
    print(' coupling violations (L < base_easy + C0h):', [r for r in R if r['L'] < r['be'] + r['C0h']][:5])
    print(' min L - (be + C0h):', min(r['L'] - r['be'] - r['C0h'] for r in R), ' #L<base+1:', sum(r['L']<=sum(r['bh'] for _ in [0])+r['be'] for r in R))
