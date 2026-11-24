# stat_search: naive-Bayes-guided upper bounds and SAT search for edge functions

Helper tooling, not a proof. This branch is never part of a proof pull request, because those
add exactly one Lean file.

`nb_search.py` works on the graph edge function f_G(x) = OR over edges uv of (x_u AND x_v).

## 1. Upper bounds ("min-max" covers)

f_G = OR over parts (A, B) of ( OR(A) AND OR(B) ), where every part is a biclique of G.

- A part costs |A| + |B| - 1 gates.
- Joining the parts costs (#parts - 1) more ORs.
- Using stars only gives |E| + k - 1 gates, where k is the size of a vertex cover. This is the
  bound in note 1 (d).
- Bicliques of the form K_{2,m} (4-cycles and up) can beat |E| + tau - 1. Note 1 points out this
  happens for C4.

At each decision point, a part is chosen by:

1. net savings: edges newly covered minus gates spent;
2. then a blend of NB and degree, a * z(NB) + (1 - a) * z(degree), taken over the center
   side A. NB is the naive-Bayes log-odds weight of x_v on the *remaining* function. a = 0.8
   by default.

A beam search keeps the best partial covers. It ranks them by gates spent plus a star-cost
estimate for the rest, using a maximal-matching lower bound on how many parts are still
needed. Every circuit is checked on all 2^n inputs before it is reported.

### Choosing a (star mode, 84 graphs, extra stars over the exact vertex cover)

| rule | extra stars |
|---|---|
| degree only | 19 |
| blend a=0.5 / 0.9 | 3 / 1 |
| beam a=0.5 | 1 |
| beam a>=0.6 | 0 |

### Benchmark (`python3 nb_search.py bench --count 40`, 45 graphs, total gates)

| method | total gates |
|---|---|
| \|E\| + tau - 1 | 1045 |
| stars, exact vertex cover | 1045 |
| stars, NB beam | 1045 |
| bicliques, NB greedy | 906 |
| bicliques, NB beam | 890 |

The biclique covers beat |E| + tau - 1 on 32 of the 45 graphs.

Q3 (the 3-cube): bicliques + NB beam give a **14-gate** monotone circuit, checked on all 256
inputs. The bound |E| + tau - 1 is 15.

## 2. SAT search (`--sat`)

Exact synthesis asks: is there a monotone fan-in-2 AND/OR circuit with S gates?

- Unused gates are allowed, so "exactly S" is the same as "at most S".
- The best heuristic circuit is passed in as **phase hints only**, and the inputs are renamed in
  NB order. Hints add no clauses, so an UNSAT answer is still a sound lower bound for
  **monotone** circuits. Circuits with NOT gates are out of scope.
- `--rows R` keeps only the inputs of Hamming weight <= R. UNSAT on those rows is UNSAT
  overall. A SAT answer is checked again on all rows, and is reported only if it passes.

Checks so far: C4 has 3 gates and 2 is UNSAT. L-meta-701 has 7 gates and 6 is UNSAT (this is the
plain gate count, not the weighted measure).

## Usage

    pip install python-sat
    python3 nb_search.py bench [-v] [--count N] [--a 0.8]
    python3 nb_search.py graph q3                      # upper bounds only
    python3 nb_search.py graph q3 --sat 13 --rows 3    # is there a 13-gate monotone circuit?
    python3 nb_search.py graph q3 --sat 0              # walk down from best-1 until UNSAT
    python3 nb_search.py graph "edges:0-1,1-2,2-3,0-3"

## 3. Which data structure should a search node use? (`ds_bench.py`)

Each search-tree node is a partial circuit, stored as a set of wire truth tables. A node has two
slots, and each slot takes one plain data structure:

- **frontier** (which node to expand next): stack (DFS), queue (BFS), binary heap (best-first
  by distance to the target truth table), or adaptive. Adaptive keeps one of each, *tags every
  node* with the container it lives in, and picks the container by epsilon-greedy on its
  novel-child rate.
- **memo** (has this partial circuit been seen before?): none, hash set, sorted array + binary
  search, or a hand-written unbalanced BST.

Results on small graphs with known optima:

| job | winner | why |
|---|---|---|
| find a circuit (budget S*) | **heap + hash set** | 159 nodes vs 1765 (queue) / 3808 (stack) |
| exhaust, i.e. a lower bound (budget S*-1) | **stack + hash set** | the memo cuts nodes 3.3x (6060 vs 19833). Frontier order doesn't change the count, but peak memory is 73 for the stack vs 4440 for the queue |

Sorted array and BST give the same node counts as the hash set but run slower. Adaptive never
beat plain heap/stack on these sizes.

These winners are built in as defaults: `python3 nb_search.py tree GRAPH S [--mode find|exhaust]`
(NB-ordered inputs, nodes use `DEFAULTS` from ds_bench.py). `python3 ds_bench.py --mode exhaust`
reruns the comparison.
