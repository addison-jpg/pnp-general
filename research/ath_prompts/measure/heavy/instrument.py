"""The heavy Qwen instrument: teacher-forced scoring with a logit lens.

Measurement only: nothing is generated. Every text is scored after one document-start token
(Qwen's <|endoftext|>), so EVERY token of the text is scored, including the first; total bits
are then the full information content of the text under the model, and dividing by characters
or words gives tokenizer-independent rates.

Backends:
  HFModel   - transformers, CPU or GPU (device="cuda" works unchanged), with the logit lens.
  GGUFModel - llama-cpp-python, for the 4-bit 7B model; no hidden states, so no lens.

Logit lens: the residual stream after each layer is decoded through the model's final RMSNorm
and unembedding (lm_head). For layer l and position t this gives p_l(x_{t+1} | x_<=t), the
probability the network "already" assigns to the actual next token at depth l.
"""
import math, os
os.environ.setdefault("HF_HUB_OFFLINE", "1"); os.environ.setdefault("TRANSFORMERS_OFFLINE", "1")

LN2 = math.log(2)


class HFModel:
    def __init__(self, path, dtype="float32", device=None, threads=None):
        import torch
        from transformers import AutoTokenizer, AutoModelForCausalLM
        if threads: torch.set_num_threads(threads)
        self.torch = torch
        self.device = device or ("cuda" if torch.cuda.is_available() else "cpu")
        self.tok = AutoTokenizer.from_pretrained(path)
        self.model = AutoModelForCausalLM.from_pretrained(path, torch_dtype=getattr(torch, dtype)).to(self.device).eval()
        self.n_layers = self.model.config.num_hidden_layers
        self.doc_start = self.tok.convert_tokens_to_ids("<|endoftext|>")

    def score(self, text, lens=True):
        """Return dict: tokens (strings), bits[t] (surprisal of token t, bits), ent[t] (predictive
        entropy before token t, bits), and if lens: lens_bits[l][t], lens_rank1[l][t] (lens top-1 == actual)."""
        torch = self.torch
        ids = self.tok(text, add_special_tokens=False).input_ids
        x = torch.tensor([[self.doc_start] + ids], device=self.device)
        tgt = x[0, 1:]
        with torch.no_grad():
            out = self.model(x, output_hidden_states=lens)
            lp = torch.log_softmax(out.logits[0, :-1].float(), -1)
            bits = (-lp.gather(1, tgt[:, None])[:, 0] / LN2).tolist()
            ent = (-(lp.exp() * lp).sum(-1) / LN2).tolist()
            res = {"tokens": self.tok.convert_ids_to_tokens(ids), "bits": bits, "ent": ent}
            if lens:
                hs = out.hidden_states          # n_layers + 1: embeddings, layer inputs..., final (already normed)
                norm, head = self.model.model.norm, self.model.lm_head
                LB, LR = [], []
                for l in range(1, len(hs)):     # after layer l (1..n_layers)
                    h = hs[l][0, :-1]
                    if l < len(hs) - 1: h = norm(h)
                    llp = torch.log_softmax(head(h).float(), -1)
                    LB.append((-llp.gather(1, tgt[:, None])[:, 0] / LN2).tolist())
                    LR.append((llp.argmax(-1) == tgt).tolist())
                # sanity: the last lens layer is the model's own output
                assert max(abs(a - b) for a, b in zip(LB[-1], bits)) < 1e-2, "lens/final mismatch"
                res["lens_bits"], res["lens_top1"] = LB, LR
        return res


class GGUFModel:
    def __init__(self, path, threads=2, n_ctx=2048):
        from llama_cpp import Llama
        import numpy as np
        self.np = np
        self.llm = Llama(model_path=path, n_ctx=n_ctx, n_threads=threads, logits_all=True, verbose=False)
        self.n_layers = None
        self.doc_start = self.llm.tokenize(b"<|endoftext|>", add_bos=False, special=True)[0]

    def score(self, text, lens=False):
        np = self.np
        ids = self.llm.tokenize(text.encode("utf-8"), add_bos=False, special=False)
        seq = [self.doc_start] + ids
        self.llm.reset(); self.llm.eval(seq)
        logits = np.asarray(self.llm.scores[: len(seq) - 1], dtype=np.float64)
        logits -= logits.max(-1, keepdims=True)
        lp = logits - np.log(np.exp(logits).sum(-1, keepdims=True))
        bits = (-lp[np.arange(len(ids)), ids] / LN2).tolist()
        ent = (-(np.exp(lp) * lp).sum(-1) / LN2).tolist()
        toks = [self.llm.detokenize([i]).decode("utf-8", "replace") for i in ids]
        return {"tokens": toks, "bits": bits, "ent": ent}
