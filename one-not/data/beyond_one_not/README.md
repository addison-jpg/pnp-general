# one-not/data/beyond_one_not

Data of task `beyond-one-not` (README items C4, T6). Write-up: `workshop/notes/beyond-one-not.md`. Scripts: `one-not/tools/beyond_one_not/`.

| File | What it is |
|---|---|
| `enum_small.log` | exhaustive enumeration (`enum_small.c`): every circuit with at most S gates, any number of NOT gates, on five small systems |
| `hunts.log` | `one-not/tools/search/hunt.py` with at most 2, 3 and 99 NOT gates (hill climbing: finding nothing proves nothing) |
| `experiments.log` | `experiments.py`: the per-set flip-classes lemma, the hunt with NOT gates free, the 2^t faces |
| `worldbound.log` | `worldbound.py`: W1 on small systems and designs; the world bound on the corpus |
| `essential_t{1,2,3}_seed1.json` | circuits with exactly t NOT gates, no correct face and no repeated function (hunted, not minimal) |
