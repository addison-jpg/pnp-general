# Homestuck, as a formal subfield (public good, no reproduction of the comic)

A formal model of the *mechanics* of the alchemy tree, in general terms. Its rules are not the comic's recipe and no text is reproduced. Hussie's comic is the cited source of the idea; credit to Andrew Hussie and the Beyond Canon team.

- `../alchemy.ath` and `../alchemy_b3.bench` (repo root): the b = 3 model as a circuit, gates 4 < base 5.
- `alchemy.py`: exhaustive count of items reachable within depth d, saturating at 2^b − 1. Registered as `checked-finite` in the centre, with runner `python3 -I culture/homestuck/alchemy.py 3 3` and a second confirmation.
- Next, if wanted: counts for larger b, and the citation of the comic's own structure (act and page) as a `cite:` for any claim that needs it.

Limit: this counts a model. It says nothing about the comic's actual recipe until someone checks the recipe against the cited source.
