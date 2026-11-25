# Task: model-in-the-loop (a language model inside the search, over the tensor evaluator)

- **Source:** Addison, 2026-11-25: "the tensors are relatively seperate here, so a structure that supercedes the tensor gpu wouldnt hurt. like a really strong cuda that has a BIIG qwens weights integrated into operations."
- **The honest form of the idea:** model-guided program search, the FunSearch / AlphaEvolve pattern. FunSearch (Romera-Paredes et al., Nature 2023) found new cap-set constructions this way.
  - A language model proposes programs: circuit generators, payer-set constructions, set-system families.
  - The tensor backend scores every proposal exactly.
  - The best proposals go back into the model's prompt.
  - The model supplies the guesses; the evaluator supplies the truth. Nothing a model says counts until the evaluator (`tested`) or Lean (`checked`) confirms it.
- **"Weights integrated into operations":** fusing an LLM's weights into the circuit kernels has no clear meaning. What does make sense: the model and the evaluator share one batched loop on the same device. On a GPU that means model sampling and tensor evaluation in one process with no copies between them; on GitHub's CPU runners, a quantised Qwen plus the NumPy backend.
- **Target:** the k = 1 flagship. Search for one-NOT circuits on linear set systems (AG(2,q), PG(2,q), cycles) that get below base, i.e. a counterexample to BottomPay or `no_minCE`. Second target: payer structures that make PHC tight, to suggest a proof.
- **Compute:** this machine (4 cores, no GPU) for development; git-compute runners (4 vCPU, 16 GB) for runs; a GPU runner is Addison's decision. Weights are never committed.

## Seats
- STOPPED (usage; reopen later): design and build the loop; partial code in workshop/compute/funsearch/ (untested). -> workshop/compute/funsearch/
- STOPPED (usage; reopen later; nothing pushed): monqwensor (Fable): the connection finder under the whole repo (index, candidates, generated board). -> workshop/compute/monqwensor/

## Lines (TAKEN / DECIDED only)
- STOPPED (usage; reopen later): FunSearch loop (Qwen proposer, sandboxed proposals, tensor scoring, islands database, target registry generated from the repo, independent recheck before any finding). -> workshop/compute/funsearch/
- NOTE (main, 2026-11-25; Addison: "the continuous monqwensor sphere is really useful"): MONQWENSOR's space already is a sphere. Normalised embeddings live on the unit sphere S^{d−1}, and cosine similarity is geometry on that sphere. For Qwen2.5-1.5B, d = 1536, so the sphere is S^{1535}: odd-dimensional. There the hairy ball theorem does NOT force a zero, and Adams gives exactly ρ(1536) − 1 = 17 everywhere-independent tangent fields (1536 = 2^9·3, ρ = 2^1 + 8·2 = 18). When MONQWENSOR restarts: index on that sphere; treat "connection flow" as a tangent field built from the cross-program gradient of similarity; record which sphere dimension each model gives (odd or even matters); keep the persistence filtration. Any "forced connection" claim from topology needs an even-dimensional sphere and a field with real meaning; otherwise it is an analogy.
