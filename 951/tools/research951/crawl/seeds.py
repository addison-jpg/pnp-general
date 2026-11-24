"""Resolve seed papers in OpenAlex by title search; print candidates so the right W-ids can be chosen."""
import json, sys, time, urllib.request, urllib.parse

SEEDS = [
    "Some remarks on Boolean sums",
    "On another Boolean matrix",
    "A new lower bound on the monotone network complexity of Boolean sums",
    "On a Boolean matrix Nechiporuk",
    "Complexity of monotone networks for computing conjunctions",
    "On negations in Boolean networks",
    "A superpolynomial lower bound for a circuit computing the clique function with at most (1/6) log log n negation gates",
    "On the negation-limited circuit complexity of merging",
    "An exponential gap with the removal of one negation gate",
    "Lower bounds for Boolean circuits of bounded negation width",
    "Lower bounds for DeMorgan circuits of bounded negation width",
    "On the complexity of slice functions",
    "Negation-limited complexity of parity and inverters",
    "Limiting negations in non-deterministic circuits",
    "The power of negations in cryptography",
    "Learning circuits with few negations",
    "Complexity of linear Boolean operators",
    "Thin circulant matrices and lower bounds on the complexity of some Boolean operators",
    "On the complexity of negation-limited Boolean networks",
    "The monotone network complexity of Boolean sums",
]


def get(url):
    req = urllib.request.Request(url, headers={"User-Agent": "research-crawler/0.1"})
    for i in range(4):
        try:
            return json.load(urllib.request.urlopen(req, timeout=60))
        except Exception as e:
            time.sleep(2 * (i + 1)); err = e
    raise err


if __name__ == '__main__':
    out = {}
    for t in SEEDS:
        q = urllib.parse.quote(t)
        d = get(f"https://api.openalex.org/works?search={q}&per-page=4&select=id,display_name,publication_year,cited_by_count,authorships")
        out[t] = [{'id': r['id'].split('/')[-1], 'title': r['display_name'], 'year': r['publication_year'],
                   'cites': r['cited_by_count'],
                   'authors': [a['author']['display_name'] for a in r['authorships']][:3]} for r in d['results']]
        print('##', t)
        for r in out[t]:
            print('  ', r['id'], r['year'], r['cites'], '|', r['title'][:90], '|', ', '.join(r['authors']))
        time.sleep(0.3)
    json.dump(out, open(sys.argv[1] if len(sys.argv) > 1 else 'seeds.json', 'w'), indent=1)
