# tensor: the circuit framework as array programs

Bit-sliced evaluation of the one-NOT circuit dicts (`one-not/tools/search/core.py` format). Task: [`refuter-951`](../../../boards/tasks/refuter-951.md).
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

    python3 -I one-not/tools/tensor/test_tensor.py [--f2lib]   # exact equality with the slow evaluators
    python3 -I one-not/tools/tensor/bench.py speed|big|maxn|mixed_n
    # from Python: sys.path.insert(0, 'one-not/tools/tensor'); import bits, corpus
    #   bits.mixed_stats(circuit_dict);  bits.slack_cubes(circuit_dict);  corpus.collect(maxn=12)

NumPy >= 2.0 is needed (`np.bitwise_count`).

## Run on a GPU machine

`backend.py` auto-detects: PyTorch with CUDA first, then JAX with a GPU/TPU, else NumPy. Override with `TENSOR_BACKEND=numpy|torch|jax`
or `bits.set_backend('torch')`. The torch and jax backends are thin (about 12 lines each) and UNTESTED here (this container has no GPU
and neither package). On the GPU box:

    python3 -m venv .venv && .venv/bin/pip install numpy torch      # or: jax[cuda12]
    TENSOR_BACKEND=torch .venv/bin/python one-not/tools/tensor/test_tensor.py    # must print the same equality line
    TENSOR_BACKEND=torch .venv/bin/python one-not/tools/tensor/bench.py big

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

## Structure between jobs

Jobs used to be alone: each run computed everything again and left its result in a log. Five small pieces now connect them
(`cache.py`, `dag.py`, `lemmad.py`, `compute.yml` + `compute-job.yml`). The old interface is unchanged: one spec with no `needs` runs as before.

1. **Cache (content-addressed).** `cache.get(KIND, circuit, compute)` returns the array of KIND (`slack_any`, `tables`, ...) for the circuit with
   address `sha256([n, sets, gates, outs])`, computing it only when no earlier job did. Entries travel as compressed packs. In Actions a shard reads
   the `compute-cache` branch plus the packs of earlier jobs of its own run, and uploads its misses; the last job of the run (`publish`, the only job
   with `contents: write`) commits them to `compute-cache`. Never main, never forced, no PR. Locally: `COMPUTE_CACHE=DIR`. Each shard prints
   `CACHE {"hit", "miss"}` and the merge job prints the hit rate. Limit: two runs in flight at the same time can both compute a circuit; the second
   to publish then adds a pack with the same entries.
2. **Job DAG.** A spec may say `"needs": ["other_spec"]` (a name in the same directory). `dag.py plan` sorts the specs into at most 4 levels;
   `compute.yml` runs level k after level k-1 (job `needs:`), every spec of a level through the reusable `compute-job.yml`. The entry of a spec with
   needs gets `--input NAME=PATH` for each merged upstream output. In a DAG the artifacts are `NAME-shard-i` and `NAME-merged`.
3. **Feedback.** `lemmad.py` is the refuter loop for Lemma D on BottomPay instances (one NOT gate), as specs:
   `fano_slack` → `lemmad_sweep` (the Fano circuits with the least cube slack, at all 3^7 states, plus random one-NOT switch circuits on AG(2,2),
   AG(2,3), PG(2,2), PG(2,3); writes its 20 tightest instances per shard as `SEED` lines) → `lemmad_neigh` (takes the tightest seeds; mutates each
   seed circuit and checks the states near the seed state; a seed without a circuit, as written by `REF1_phc.py`, gets a deeper payer-set search) →
   `lemmad_recheck` (every `VIOLATION` again with different code: tensor correctness, rebuilt instance, U1's matroid partition, a separate component
   count). Only a confirmed violation is written to the board, by `dag.py reduce`, with `boards.py add --runner`. To seed from REF1's sweep, add
   `"ref1_phc"` to the `needs` of `lemmad_neigh.json`. What this tests: Lemma D's count on BottomPay instances. It does not search for a circuit
   below base; that is SAT (`refuter-951`).
4. **Reduce up the tree.** The entry's last stdout line `SUMMARY {json}` is folded over shards (numbers add, `min*`/`max*` keys take min/max).
   The merge job prints `RESULT {json}` (lines, sha256, cache counts, summary) and `publish` stores it at `results/NAME/run-ID.json` on
   `compute-cache`, with the merged output gzipped beside it (up to 20 MB). So results are readable with `git fetch origin compute-cache`, where
   artifact downloads are blocked. A workflow never writes main; a seat does: `python3 -I one-not/tools/tensor/dag.py reduce --who SEAT` turns every
   result whose spec has a `"finding"` block into a `tested` record with a runner in that directory's `findings.jsonl` (who = `gha-run-ID`), reruns
   the runner here, and adds SEAT to `by` only if it passes. From there `boards.py` propagates it like any finding. Then `git add` the lines.
5. **GPU.** `compute.yml` takes a `runner` input (the `runs-on` label of the shard jobs, default `ubuntu-latest`). The backend auto-detects
   torch / jax, so a GPU runner needs only that label and `torch` in the spec's `requirements`. Paid runners are the owner's decision.

    python3 -I one-not/tools/tensor/dag.py plan compute/specs/lemmad_recheck.json       # the levels
    python3 -I one-not/tools/tensor/dag.py local compute/specs/test/tiny_sweep.json     # a two-spec DAG on this machine; run it twice to see the cache
    gh api -X POST repos/addison-jpg/pnp-general/actions/workflows/compute.yml/dispatches -f ref=main -f 'inputs[spec]=compute/specs/lemmad_recheck.json'
    git fetch origin compute-cache && git show FETCH_HEAD:results/lemmad_recheck/run-RUNID.json
    python3 -I one-not/tools/tensor/dag.py reduce --who SEAT --dry

## Design: the board as a tensor-backed state (proposal, not built)

The compute structure above is a small copy of what the boards do by hand. The proposal is to make it the only mechanism.

- **Record.** Every claim is one record: `id`, `statement`, `word` (checked / paper / tested / refuted / open / premise), `evidence` (paths or
  `file.lean::name`), `runner` (a command that re-derives it and exits 0), `needs` (ids it depends on), `serves` (the target it is about), `by`.
  This is today's `findings.jsonl` line plus `needs`. Records are append-only and content-addressed; a prose board line has no standing.
- **State.** The state of the repository is a table: one row per record, one column per fact that a machine can recompute: evidence exists,
  runner passed (when, on which commit, how long), second checker, word, and for searches the cell coordinates (family, size, number of NOT gates,
  method) with the count tested and the least slack seen. `boards.py build` already computes the first columns; `dag.py` results fill the rest.
  It is a tensor in the plain sense: target × cell × word, small, rebuilt from the records, never edited.
- **Propagation.** Up the directory tree as now, and along `needs`: a record is live only while every record it needs is live. A failed rerun
  or a refutation marks everything downstream stale in one pass. This is the job DAG's rule applied to claims.
- **Queue.** Open work is derived, not written: the cells of the state with no record, a stale record, an `open` word, or a `tested` word where a
  proof is wanted, ordered by what they block (the number of live records that need them). A seat takes the top cell; taking is itself a
  record (`word: open`, `by: seat`, with an expiry), so two seats do not collide and nothing needs a TAKEN line.
- **Compute.** A cell whose record has a runner is a job spec. The scheduler is `compute.yml`: the queue's runnable cells become a DAG, the
  cache makes reruns cheap, `publish` stores results, `reduce` appends records. Tightest cases seed the next cells (the feedback step).
- **Limits.** A runner passing means the command exited 0, no more: `tested` never becomes `checked`; only the Lean build gives `checked`.
  Workflows still cannot write main, so a seat (or one trusted reducer) appends the records. Prose still has a place for what a statement means
  and why it matters; it stops being where status lives.
- **First steps.** (1) add `needs` to `boards.py` records and the stale pass; (2) a `queue` command that prints the derived cells;
  (3) convert the task boards' OPEN / TAKEN lines to records; (4) let `reduce` run on a schedule from one seat.
