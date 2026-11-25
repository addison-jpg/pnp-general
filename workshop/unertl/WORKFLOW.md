# The unertl workflow: a formal scaffold

Status: a scaffold. No stage is built. No helper ran: the session had no Agent tool, so `h1_paths.txt` and
`h2_open.txt` were written by the lead and say so. Nothing was committed or pushed.

## 1. Terms (used exactly)

- **unertl workflow**: the user's term for the ideal workflow: binary outputs from a GNN fed to universal.ath, which gets its own Qwen.
- **stage**: one numbered step of the unertl workflow.
- **contract**: the input and output of a stage.
- **check**: an asteroid claim run with `bin/asteroid --no-lean`.
- **credential**: a key or token the user enters only through the secure form, never in chat or in a file.
- **channel**: one messaging route to the user's phone.
- **binary decision**: a 0 or 1 read from one raw output by a fixed threshold (PLAN.md section 0).
- **combinatorial label**: a finite label built from several binary decisions, not one bit (PLAN.md section 0).

## 2. Stages, in order

- (a) Board nodes and labels in.
- (b) A Qwen-small vector per node.
- (c) A GNN over the board.
- (d) Raw GNN outputs to binary decisions by fixed thresholds.
- (e) Binary decisions to combinatorial labels.
- (f) Labels to universal.ath.
- (g) universal.ath's own Qwen-large, from Hugging Face, after a licence check.

## 3. Contracts

A contract is open when its input or its output is not fixed.

| stage | input | output | state |
|---|---|---|---|
| (a) | `boards/tree.json`: 262 nodes, each with id and label | one (id, label) pair per node, in board order | defined |
| (b) | the (id, label) pairs and each node's text | one Qwen-small vector per node (0.5B or 1.5B; the 3B is excluded) | defined; contextual vectors need a forward pass |
| (c) | the board graph and the per-node vectors | raw outputs, one real value per output unit | open: edge set and number of output units not fixed |
| (d) | raw outputs | one binary decision per raw output | defined by type; the threshold rule is open (section 7) |
| (e) | several binary decisions per node | one combinatorial label per node from a finite set | defined |
| (f) | combinatorial labels | whatever universal.ath returns | open until the user defines universal.ath's contract |
| (g) | universal.ath's input | universal.ath's output, via a Qwen-large | open until the user defines universal.ath's contract |

Open contracts: 3, stages (c), (f), (g). The universal.ath proposal in `BOARD_FORMAL.md` is not the user's contract.

## 4. Checks

Named, not created.

| stage | check | possible now |
|---|---|---|
| (a) | `workshop/unertl/checks/a_board_in.ath`: label counts sum to the node count (as in `workshop/board_formal/board.ath`) | yes |
| (b) | `workshop/unertl/checks/b_rows.ath`: counts of label words with a static Qwen row in `math/qwen/semantic_rows.json` | yes, static rows only |
| (c) | none | no: no GNN exists |
| (d) | none | no: the threshold rule is open |
| (e) | `workshop/unertl/checks/e_labels.ath`: k binary decisions give at most 2^k labels; the six board labels need k >= 3 (2^2 = 4 < 6, 2^3 = 8 >= 6) | yes |
| (f) | none | no: contract open |
| (g) | none | no: contract open, licence check not done |

Stages with a check possible now: 3. No check file exists yet (`h1_paths.txt`).

## 5. Credentials and channels

Precondition, not done: the user's messaging bot is a separate channel. Before it can run it needs:

1. one provider account, of the user's choice;
2. one credential for that provider, entered by the user only through the secure form;
3. the provider's network host allowed in the environment.

None is in place. No credential was read or asked for.

## 6. Not claimed

- No stage is built.
- No result is claimed.
- The unertl workflow is a scaffold.

## 7. Open

- The user's choice of provider for the channel.
- universal.ath's contract (blocks stages (f) and (g)).
- The threshold rule for stage (d).
