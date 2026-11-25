# Heavy Qwen instrument

A measuring instrument, not an agent: Qwen2.5 language models score fixed texts (teacher-forced log-probabilities, nothing generated). This builds on the first 0.5B measurement (`../results.md`) in two ways: a logit lens over the forward pass, and a statistics layer over the raw numbers. Results: [`results.md`](results.md).

**There is no GPU on the seat's machine** (4 CPU cores, 15 GB RAM). 0.5B, 1.5B (fp32) and 3B (bf16) ran there on CPU under `nice -n 19`; 7B ran as a 4-bit GGUF (Q4_K_M, llama-cpp-python) on git-compute runners (CPU, no GPU). `instrument.HFModel` uses CUDA unchanged when torch sees a GPU. Weights are never in the repository.

| file | what |
|---|---|
| `instrument.py` | `HFModel` (transformers; surprisal, predictive entropy, and the logit lens: every layer's residual stream decoded through the final RMSNorm and `lm_head`, checked against the model's own output) and `GGUFModel` (llama-cpp-python; surprisal and entropy, no lens). Every text is scored after a `<|endoftext|>` start token, so every token is scored. |
| `stats.py` | bits per token / character / word, paired bootstrap CIs over prompts, exact Wilcoxon signed-rank and sign tests, Spearman agreement, the verdict rule (holds at every size / shrinks with size / reverses / fails / not resolved), lens summaries (settle layer, half-information layer). |
| `data.py` | B1 pairs (Addison's verbatim prompts from `../../research-seat.md`, formal rewrites from `../measure.py`) and five English / .ath / Lean statement triples copied from the repository. |
| `run.py` | scores everything under one local model, writes `data/<size>.json`. |
| `compute_entry.py` | the same on git-compute (`compute/specs/heavy_qwen_7b.json`), and `--assemble` to rebuild `data/<size>.json` from the job logs. |
| `report.py` | builds `results.md` from whatever `data/*.json` exist, then appends `notes.md` (the written verdicts). |

Run (local):

    python run.py --label 0.5B --hf PATH/Qwen2.5-0.5B-Instruct
    python run.py --label 3B --hf PATH/Qwen2.5-3B-Instruct --dtype bfloat16 --threads 3
    python report.py

Needs `torch`, `transformers`, `numpy`; `llama-cpp-python` and `huggingface_hub` for the GGUF and compute paths.
