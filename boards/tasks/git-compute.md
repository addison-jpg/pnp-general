# Task: git-compute (route brute force through GitHub instead of this machine)

- **Serves:** every search / corpus / refuter lane (Addison, 2026-11-25: "big pull requests exist up top of this repo, thats us. they arent dealt with efficiently, just read. the gpu/tensor beast should be able to grab that easily, and we can route more thru git, saving us brute force").
- **Why:** this machine has 4 cores shared by every seat. The repo is public, so standard GitHub Actions runners are free (4 vCPU each, up to 20 jobs at once). Brute force that is embarrassingly parallel (truth tables, slack at all cubes, corpus checks, refuter sweeps) belongs there; SAT and Lean stay local.
- **Statement:** (1) the tensor backend of `refuter-951` T1 (`one-not/tools/tensor/`, bit-sliced numpy; torch/jax if a GPU exists) lands first; (2) a workflow `.github/workflows/compute.yml`: a job spec file pushed to `compute/<name>` branch (or `workflow_dispatch` with a spec path) fans out as a matrix over shards, each shard runs the tensor backend, results are committed back by github-actions[bot] as `findings.jsonl` records + data files, `[skip ci]`; (3) a 10-line `compute/README.md`: how a seat submits a job and where results appear.
- **Done when:** one real job (e.g. slack at all cubes on the stored Fano corpus, 80,198 circuits) runs sharded on Actions, its result equals the local evaluator on a sample, and wall time is on the board.
- **Not:** paid GPU runners (owner decision); PRs as the job queue (they notify; branches + workflow runs do not).
- **Open PRs #18, #21, #22 (all from 2026-11-24):** checked by coord against main: #22 mst-lean fully landed (72/72 removals gone, 11/11 added files present); #21 mst-readme mostly superseded (9/11 removals gone; README rewritten since); #18 WIP marked "NOT for main", its CanonD1.lean is on main. Proposed: close all three as superseded (asked Addison).
- **Seats:** OPEN, one Sonnet (after T1 lands, or takes T1 too).

## Lines (TAKEN / DECIDED only)
