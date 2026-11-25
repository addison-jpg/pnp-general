# tensor: the circuit framework as array programs

Bit-sliced evaluation of the one-NOT circuit dicts (`research/one-not/tools/search/core.py` format). Task: [`refuter-951`](../../../../boards/tasks/refuter-951.md).
A truth table over 2^n inputs is 2^n / 64 `uint64` words (bit x = value at input x, the order of `core.tables`). One gate is one array
operation over all inputs. Everything below is an array program; nothing loops over inputs, cubes or states in Python except the batches.

| function (`bits.py`) | what it computes |
|---|---|
| `tables(c)` | every wire's truth table, `[n + gates, W]` uint64; `to_int(row)` gives the `core.tables` integer |
| `correct(c)` | the same test as `core.correct` |
| `slack_cubes(c, any_gate=False, parts=False)` | slack at every cube Q (R = 0), `int32[2^n]`; `parts` gives (count, base) |
| `mixed_slack(c, ..., rs=None, compact=False)` | slack at every mixed state (Q, R), 3^n cells; dense `[R, Q]` (INVALID where Q meets R) or `compact=True`: one array per R in the layout of `continuous.slack_table` |
| `mixed_stats(c)` | reductions over all 3^n states without unpacking: state count, states with base > 0, least slack, number with slack < 0, histogram of slack |
| `dd_states(c)` | the DD states of a one-NOT circuit (A7 / A14 definition) at all 3^n states |

Definitions are copied from `continuous.slack_table` (which `core.slack` agrees with at R = 0); `test_tensor.py` checks exact equality.
For each R the batch works on the compact subcube x_R = 0 (all R with the same |R| share one array shape), so the work is 3^n, not 4^n.

## Run (CPU, NumPy; the only tested path)

    python3 -I research/one-not/tools/tensor/test_tensor.py [--f2lib]   # exact equality with the slow evaluators
    python3 -I research/one-not/tools/tensor/bench.py speed|big|maxn|mixed_n
    # from Python: sys.path.insert(0, 'research/one-not/tools/tensor'); import bits, corpus
    #   bits.mixed_stats(circuit_dict);  bits.slack_cubes(circuit_dict);  corpus.collect(maxn=12)

NumPy >= 2.0 is needed (`np.bitwise_count`).

## Run on a GPU machine

`backend.py` auto-detects: PyTorch with CUDA first, then JAX with a GPU/TPU, else NumPy. Override with `TENSOR_BACKEND=numpy|torch|jax`
or `bits.set_backend('torch')`. The torch and jax backends are thin (about 12 lines each) and UNTESTED here (this container has no GPU
and neither package). On the GPU box:

    python3 -m venv .venv && .venv/bin/pip install numpy torch      # or: jax[cuda12]
    TENSOR_BACKEND=torch .venv/bin/python research/one-not/tools/tensor/test_tensor.py    # must print the same equality line
    TENSOR_BACKEND=torch .venv/bin/python research/one-not/tools/tensor/bench.py big

Run the test first; if it fails on the GPU path the fault is in `backend.py` (torch uses int64 words with a masked right shift; jax needs x64,
which `JaxBackend` enables). Only `mixed_slack` / `slack_cubes` unpack to host `int32`; `mixed_stats` and `tables` stay on the device until the final popcounts.
Memory per R-batch is capped by `budget` (bytes, default 2 GiB); lower it for a smaller card.

## How to run a compute job (GitHub Actions, `.github/workflows/compute.yml`)

A job spec is a JSON file in the repo: `{"name", "entry": "path/to/script.py", "args": [...], "shards": N (<= 20), "output": "file.jsonl", "requirements": ["numpy>=2.0"]}`
(example: `compute/specs/fano_slack.json`). The entry must accept `--shard i --of N --out PATH` and write its share (JSON lines) to PATH; shard i takes items j with j % N == i.
Test it locally first on a small slice (`python3 -I ENTRY --shard 1 --of 400 --out /tmp/s.jsonl --verify 40`), push the spec and entry to main, then either

    gh api -X POST repos/addison-jpg/pnp-general/actions/workflows/compute.yml/dispatches -f ref=main -f 'inputs[spec]=compute/specs/fano_slack.json'
    # or push a branch compute/NAME whose compute/job.json is the spec

Poll with `gh api 'repos/addison-jpg/pnp-general/actions/runs?event=workflow_dispatch&per_page=5'`. Results are artifacts: `shard-i` per shard and `merged` (shards concatenated in order), fetched with
`gh run download RUN_ID -n merged`. The workflow is read-only (no commits, releases, tags, PRs or comments); record the result on the board by hand. From the cloud container the artifact host is blocked, so compare the sha256 printed in the merge job log (`gh run view RUN_ID --log`).
