# Research Plan: A Linear Head over Qwen Vectors, Coordinated by a Coordinator

## 1. Question

Can a linear head over frozen Qwen vectors, coordinated by a coordinator, give checked answers about the memory names, and what is the minimum result that would show it? The memory names are mapped by monqwensor. The minimum result is one held-out memory name that the linear head maps to a label confirmed by a check, where the work reaches the linear head through one n-partite push routed by the coordinator.

## 2. Background and status

2.1 Weights. The Qwen2.5 0.5B-Instruct weights are on disk in the scratchpad directory /tmp/claude-0/-home-user/c7c2895f-eb04-517d-b538-6d0d59d567a9/scratchpad. The file is 988,097,824 bytes. The parameter count is 494,032,768. The license is Apache 2.0.

2.2 Other sizes. Qwen2.5 1.5B and Qwen2.5 7B are licensed under Apache 2.0. Qwen2.5 3B is licensed under qwen-research, and its weights must not be redistributed.

2.3 Existing code. The file workshop/ath_prompts/measure/measure.py performs a forward pass on the 0.5B model. It requires torch and transformers, which are not installed in this sandbox. Its MODEL path points to a scratchpad folder that is missing. The file workshop/compute/monqwensor/embed.py runs a forward pass on the 1.5B model and mean-pools the last layer.

2.4 Routing. The file workshop/route/route.py computes a minimum spanning forest over three layers: programs, evidence, and center/shards. It does not reach models or vectors.

2.5 Environment. The sandbox has about 4 CPUs, about 12 GB of free RAM, and no GPU.

2.6 Remote. A release upload and pushes to the remote are blocked. The GitHub token is invalid, and the repository returns 404.

## 3. Hypotheses

H1. A linear head fitted with numpy only, over the static embedding rows of the 0.5B model, assigns held-out memory names to their correct labels at a rate above a majority-label baseline. Refuted by the check in step (a): if the held-out accuracy does not exceed the baseline, H1 is refuted.

H2. A numpy implementation of the forward pass of the 0.5B model produces logits that match the torch reference logits on one fixed prompt, within a stated tolerance. Refuted by the check in step (b): if the maximum absolute difference exceeds the tolerance, H2 is refuted.

H3. A linear head over contextual hidden states from the forward pass improves on the static linear head of H1, measured on the same held-out split. Refuted by the check in step (c): if the contextual linear head does not exceed the static linear head, H3 is refuted.

## 4. Method

Each step is performed in the order given. Output paths under workshop/plan/out are proposed and do not yet exist.

(a) Numpy-only linear head over static embedding rows.
Input: the embedding matrix of the 0.5B model, read from its shard byte ranges in the scratchpad weights file, and a labeled list of memory names.
Output: workshop/plan/out/head_static.npz.
Done-test: the head file loads with numpy alone, and the held-out accuracy and the baseline are written to a log.

(b) Forward pass checked against torch.
Input: one fixed prompt as token ids, and the 0.5B model weights.
Output: workshop/plan/out/logits_numpy.npy and workshop/plan/out/logits_torch.npy.
Done-test: the maximum absolute difference between the two logits arrays is recorded and is at or below the stated tolerance. This step requires torch (see Section 8).

(c) Linear head over contextual hidden states.
Input: hidden states from the forward pass of step (b) for the labeled memory names.
Output: workshop/plan/out/head_contextual.npz.
Done-test: the held-out accuracy and the baseline are logged on the same split used in step (a).

(d) Coordinator as a route.
Input: workshop/route/route.py, extended with a coordinator layer.
Output: an updated workshop/route/route.py and a route log at workshop/plan/out/route_log.json.
Done-test: the spanning forest includes the coordinator layer, and each memory name maps to exactly one n-partite push.

(e) Mapping to Qwen research weights, with a license gate.
Input: the route log of step (d) and the weights of the chosen model size.
Output: workshop/plan/out/weight_map.json.
Done-test: the mapping record names only model sizes whose license permits the intended use. License gate: the 3B model is excluded from every published, committed, or uploaded path, and its weights are never redistributed.

## 5. Coordinator design

| Unit | Size limit | Who runs it | Output file |
|---|---|---|---|
| CPU work unit: one n-partite push to one partition | One shard byte range; numeric limit not yet set | CPU in this sandbox | workshop/plan/out/push_log.jsonl |
| Coordinator unit: one linear head application over stored vectors | Open | Open (coordinator location not decided) | Open |
| Forward pass unit: token ids in, hidden state or logits out | Open | Open (coordinator location not decided) | Open |
| Check unit: one .ath file run as `asteroid --no-lean file.ath` | One check file per step | CPU in this sandbox | Check log, path open |

The rows marked open depend on the coordinator and are not decided.

## 6. Checks

Each step has one check file. The check files do not yet exist. No result is claimed in this plan.

- Step (a): workshop/plan/checks/step_a.ath claims that the held-out accuracy of the static linear head exceeds the majority-label baseline.
- Step (b): workshop/plan/checks/step_b.ath claims that the maximum absolute difference between the numpy logits and the torch logits is at or below the stated tolerance.
- Step (c): workshop/plan/checks/step_c.ath claims that the contextual linear head exceeds the static linear head on the same held-out split.
- Step (d): workshop/plan/checks/step_d.ath claims that each memory name maps to exactly one n-partite push, and that each shard byte range appears once.
- Step (e): workshop/plan/checks/step_e.ath claims that the weight map names no 3B weights.

## 7. Risks and limits

7.1 Compute. There is no GPU. The sandbox has about 4 CPUs.

7.2 Memory. The 0.5B model in fp32 requires about 2 GB (494,032,768 parameters at 4 bytes each is 1,976,131,072 bytes). The sandbox has about 12 GB of free RAM.

7.3 License. The 3B model cannot be redistributed. The license gate in step (e) applies.

7.4 Remote. The release upload and the pushes are blocked, so outputs remain local until the token and the repository are fixed.

7.5 Failure conditions. The plan fails if H1, H2, or H3 is refuted by its check. It also fails if the coordinator location is not decided, which blocks step (d). It is blocked at step (b) if torch is not installed.

## 8. Open questions for the user

1. Where does the coordinator run?
2. Should torch be installed in this sandbox?
3. Is the 3B model needed at all?

## 9. Status

- Step (a): not started.
- Step (b): partial. The file workshop/ath_prompts/measure/measure.py exists but cannot run in this sandbox.
- Step (c): not started.
- Step (d): partial. The file workshop/route/route.py exists, but it has no coordinator layer.
- Step (e): not started.
