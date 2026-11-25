# Research plan: an agent board, a mapped Qwen, a GNN and a universal check

Status: a plan. Nothing in this file is built or checked unless the status line says so.

## 0. Terms (used exactly)

- **board**: the agent board structure (see `boards/TREE.md`, `workshop/board_formal/`). A set of nodes, each with a label from {checked, checked-finite, tested, refuted, analogy, open}.
- **node**: one board entry with an id, a label, a program, a claim and evidence.
- **Qwen-small**: a Qwen2.5 model of 0.5B or 1.5B parameters. The 3B is excluded (qwen-research licence).
- **monqwensor**: the existing code in `workshop/compute/monqwensor/` that maps memory names to Qwen vectors.
- **GNN**: a graph neural network. Not in the repo yet.
- **raw output**: one real value per GNN output unit.
- **binary decision**: a 0 or 1 read from one raw output by a fixed threshold.
- **combinatorial label**: a finite label built from several binary decisions, not one bit.
- **universal.ath**: named by the user. Not in the repo. Its contract is open (section 6).
- **formalization.ath**: named by the user. Not in the repo. Its contract is open (section 6).
- **mini proof agent**: one small agent that runs a single `.ath` check and reports its counts.

## 1. Scope

Read as a script. Each section is a step. A step is done only when its check passes or its failure is written down.

## 2. Inputs that exist

- Board: `boards/TREE.md`, `boards/tree.json`, 262+ nodes, with the label set above. 210 nodes have no second seat (see `workshop/board_formal/BOARD_FORMAL.md`).
- Qwen code: `workshop/compute/monqwensor/embed.py` (last-layer pooling on the 1.5B), `math/qwen/` (static embedding rows, shard byte ranges).
- Bus: `workshop/bus/` (L1, L3, L4 checked on one slice; FEED open).
- Mobius: `workshop/mobius/` (twist checked-finite; continuity open).

## 3. Inputs that do not exist

- A GNN in any language in this repo.
- `universal.ath` and `formalization.ath`.
- A third stage of the little, big, little chain.
- A second seat for the board nodes.

## 4. Steps

| step | what | check | status |
|---|---|---|---|
| 4.1 | Board as a formal structure: nodes, labels, seats | `workshop/board_formal/board.ath` counts | not started (stage three missing) |
| 4.2 | Qwen-small mapped to monqwensor, vectors per memory name | counts of vectors per name, exact | partial (static rows exist; contextual vectors need a forward pass) |
| 4.3 | Continuous vector weights, if needed | assess in 4.2; do not assume | open |
| 4.4 | GNN taking the board graph as input | forward pass shape check | not started |
| 4.5 | Raw GNN outputs mapped to binary decisions by fixed thresholds | count of decisions per output | not started |
| 4.6 | Combinatorial labels from several binary decisions | exact count of distinct labels | not started; the user notes these are probably not binary |
| 4.7 | Feed labels to universal.ath | contract in section 6 | blocked |
| 4.8 | Qwen-large for universal.ath, taken from Hugging Face | licence check first | blocked by 4.7 and by licence review |

## 5. Structure, not claimed

- Outer GNN units feed a central unit inside the same GNN. The shape is a hypercone with layered circular planes, polar coordinates a natural choice. This is a design picture, not a result.
- "Propagate, then adjust" is a training loop. No loop is written here.
- The one-to-one outflow from the GNN to the board is a mapping. Whether it is a bijection is open.

## 6. Open contracts

- `universal.ath`: what it takes as input and what it returns. Must be given before 4.7.
- `formalization.ath`: the same. The user should say whether it is one file or a folder.
- Whether the binary decisions in 4.5 are the right interface, or whether a finite non-binary alphabet is needed (4.6).

## 7. Not claimed

- No step is proved. No step is checked except where its check passes.
- No claim that a larger Qwen improves the board or the GNN.
- No claim about the P versus NP question.
