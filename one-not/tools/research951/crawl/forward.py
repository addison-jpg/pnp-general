"""Forward-citation crawl in OpenAlex: all works citing any seed; score by #seeds cited + keywords."""
import json, sys, time, urllib.request, re
from collections import defaultdict

SEEDS = {
 'W1501812634': 'Mehlhorn79 BoolSums', 'W2056094722': 'Pippenger80 BoolMatrix', 'W2007805020': 'Wegener80 BoolSums',
 'W1495932320': 'Tarjan78', 'W2125793194': 'Blum09 Negations', 'W2024435371': 'AmanoMaruoka05', 'W1571026820': 'AmanoMaruoka98',
 'W2022093588': 'AMT02 merging', 'W2053969720': 'SungTanaka02', 'W4281619035': 'JuknaLingas22', 'W2934762734': 'JuknaLingas19',
 'W2054417980': 'Wegener85 slices', 'W2001924771': 'Wegener86 slices', 'W2614435365': 'IMT07 parity', 'W1588568034': 'IMT06 parity',
 'W2077017336': 'Morizumi09', 'W74032123': 'GMO15 crypto', 'W1755464633': 'BCO14 learning', 'W2595009776': 'BCO15 learning',
 'W1967668295': 'JuknaSergeev13', 'W2585022148': 'GrinchukSergeev17', 'W2069191912': 'BNT98', 'W2044799855': 'TanakaNishino94',
 'W205871068': 'Fischer75 survey', 'W2025576605': 'Tsukiji96 BoolSums', 'W2033239368': 'Weiss83', 'W4230950430': 'Wegener82',
 'W2002850049': 'MorizumiSuzuki10',
}
KW = re.compile(r'negation|not gate|inverter|boolean sum|or-circuit|rectifier|monotone|slice|set circuit|inversion|'
                r'disjunction|semi-disjoint|single negation|one negation|partial', re.I)


def get(url):
    req = urllib.request.Request(url, headers={"User-Agent": "research-crawler/0.1"})
    for i in range(5):
        try:
            return json.load(urllib.request.urlopen(req, timeout=60))
        except Exception as e:
            time.sleep(2 * (i + 1)); err = e
    raise err


def abstract(inv):
    if not inv: return ''
    pos = {}
    for w, ps in inv.items():
        for p in ps: pos[p] = w
    return ' '.join(pos[i] for i in sorted(pos))


if __name__ == '__main__':
    works = {}; citers = defaultdict(set)
    for sid, name in SEEDS.items():
        cursor = '*'; n = 0
        while cursor:
            d = get(f"https://api.openalex.org/works?filter=cites:{sid}&per-page=200&cursor={cursor}"
                    "&select=id,display_name,publication_year,cited_by_count,authorships,abstract_inverted_index,primary_location,doi")
            for r in d['results']:
                w = r['id'].split('/')[-1]; citers[w].add(name); n += 1
                if w not in works:
                    src = ((r.get('primary_location') or {}).get('source') or {}).get('display_name')
                    works[w] = {'id': w, 'title': r['display_name'], 'year': r['publication_year'], 'cites': r['cited_by_count'],
                                'authors': [a['author']['display_name'] for a in r['authorships']][:4], 'venue': src,
                                'doi': r.get('doi'), 'abstract': abstract(r.get('abstract_inverted_index'))}
            cursor = d['meta'].get('next_cursor')
            time.sleep(0.2)
        print(f'{name}: {n} citing works', file=sys.stderr, flush=True)
    out = []
    for w, x in works.items():
        x['seeds'] = sorted(citers[w])
        txt = (x['title'] or '') + ' ' + x['abstract']
        x['kw'] = sorted(set(m.lower() for m in KW.findall(txt)))
        x['score'] = 2 * len(x['seeds']) + len(x['kw']) + (2 if x['year'] and x['year'] >= 2015 else 0)
        out.append(x)
    out.sort(key=lambda x: -x['score'])
    json.dump(out, open(sys.argv[1], 'w'), indent=0)
    print(len(out), 'distinct citing works', file=sys.stderr)
