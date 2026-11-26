# Feed: how the open sources feed each other

Design (proposed by the lead, not from asteroid: asteroid has no record of these sources).

1. Every source writes one record shape: `{source, id, url, licence, text}`. `source` is arxiv, openalex, zenodo or semantic-scholar. `id` is the source's own id.
2. Deduplication key: DOI when present, otherwise the arXiv id, otherwise `(source, id)`. A record with a key already seen is counted once.
3. Each source's raw response stays in the scratchpad. Only counts go into the repo.
4. Overlap is measured on distinct lowercased words, per pair of sources.

Samples (typed from the fetch, 2026-11-26):

| source | texts | tokens | distinct words |
|---|---|---|---|
| arxiv (cs.CL) | 200 | 30,907 | 4,079 |
| openalex (concept C41008148, with abstract) | 50 | 7,607 | 2,054 |
| zenodo ("language model", size 25) | 25 | 8,539 | 2,628 |

Overlap: 591 distinct words are shared between openalex and zenodo. The arxiv overlap is not computed yet, since the arxiv sample is not in this folder.

Status: semantic-scholar returned HTTP 429 (rate limit) on the first try; not sampled. Each record has a licence field, which the feed keeps with the record.

Not claimed: any mapping result, or that these sources cover the language.
