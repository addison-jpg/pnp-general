"""Python -> Lean witness handoff (swarm update: Python discovers, Lean checks small self-contained witnesses).
Writes cfgI_witness.json: the circuit, every zero point's merge set M_z(w) and h(z), and two integer certificates.
Lean needs only finite membership/count checks over these lists; no search, no LP.
  cert_mergefrac: K (price 1 on each gate of K, scale |K|): sum_w min_z |M_z(w) ∩ K| = 2 < 3 = |K|  (MergeFrac dual value 2/3).
  cert_world0:    gate g13 lies in M_z(S0) for every zero point z of S0 with h(z) = 0, and the same for S1
                  => if S0 and S1 both use only h = 0 worlds, load(g13) = 2 > 1.
Each certificate is re-verified here from the circuit before writing."""
import itertools, json, sys
sys.path.insert(0, '/home/user/c951/tools')
from w951 import load
import cfgI_prices as P

c = load('cfgI.json')[0]
Z = [P.zero_menu(c, w) for w in range(len(c.sets))]
K = [12, 18, 33]
mins = [min(len(t[2] & set(K)) for t in zm) for zm in Z]
assert sum(mins) == 2 and len(K) == 3
for w in (0, 1):
    assert all(13 in t[2] for t in Z[w] if t[1] == 0) and any(t[1] == 0 for t in Z[w])
out = {
    'source': 'front-match w9/fb/cfgI.json', 'status': 'Python-generated witness; NOT a proof until checked in Lean',
    'circuit': c.to_dict(),
    'merge_sets': [[{'z': t[0], 'h': int(t[1]), 'M': sorted(t[2])} for t in zm] for zm in Z],
    'cert_mergefrac': {'K': K, 'min_per_set': mins, 'sum': sum(mins), 'size_K': len(K), 'claim': 'sum_w min_z |M_z(w) ∩ K| = 2 < |K| = 3'},
    'cert_world0': {'gate': 13, 'sets': [0, 1], 'claim': 'for w in {0,1}: forall z zero point of S_w with h(z) = 0, 13 ∈ M_z(w)',
                    'h0_points': {w: [t[0] for t in Z[w] if t[1] == 0] for w in (0, 1)}},
}
json.dump(out, open('cfgI_witness.json', 'w'), indent=1)
print('wrote cfgI_witness.json; mins', mins, '; h0 points', out['cert_world0']['h0_points'])
