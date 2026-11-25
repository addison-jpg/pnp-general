"""Join cosmos + time: a property P of n universes is history-independent (physics/cosmos/invariant.py: its frequency
among the first N is the same in every ordering, at every N) exactly when p -> []p holds at every world of the S5
cluster on those n worlds (physics/time: no privileged world). Every n <= 6 and every P."""
from itertools import permutations
for n in range(1, 7):
    perms = list(permutations(range(n)))
    for P in range(1 << n):
        prof = {tuple(sum(P >> x & 1 for x in p[:k + 1]) for k in range(n)) for p in perms}
        box = P == (1 << n) - 1                                       # []p on the cluster: p at every world
        assert (len(prof) == 1) == all(not (P >> w & 1) or box for w in range(n)) == (P in (0, (1 << n) - 1))
print("n <= 6: ordering-independent at every cutoff  <=>  p -> []p valid on the S5 cluster  <=>  P constant"); print("PASS")
