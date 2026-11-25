"""Proposers: something that, given a target and a few scored parent programs, returns new program TEXTS.  Text only: nothing here
runs a program (sandbox.py does) and nothing here scores one (the target's evaluator does).
  QwenHF     transformers; device auto-detect: CUDA when torch sees a GPU (the tensor backend then picks torch/cuda too, so model
             sampling and circuit evaluation share one device and one process), else CPU.  Local sizes that fit 15 GB: 0.5B, 1.5B, 3B.
  QwenGGUF   llama-cpp-python, for the 4-bit 7B model on CPU runners (n_gpu_layers=-1 when FUNSEARCH_GPU_LAYERS is set).
  Mutate     no model: random text edits of the parents.  It exists to test the loop and as the baseline a model has to beat.
Weights are found in a local directory or downloaded with huggingface_hub into $FUNSEARCH_WEIGHTS (default: the system temp
directory), never into the repository."""
import os, re, ast, glob, random, tempfile

SYSTEM = 'You are an expert Python programmer and circuit designer. You improve a function step by step. You answer with one Python code block and nothing else.'

def header(target):
    seed = target.seeds[0]; return seed[:seed.index('\n') + 1]                    # the `def build(...):` line of the skeleton

def prompt(target, parents):
    """ChatML prompt ending inside the assistant's code block, at the skeleton's signature (the model continues the function body)."""
    u = [target.api, '']
    if parents:
        u.append('Earlier versions, worst first, with their scores:')
        for i, (src, label) in enumerate(parents): u += ['', 'Version %d (%s):' % (i + 1, label), '```python', src.rstrip(), '```']
        u += ['', 'Write version %d: a NEW build that is different from the versions above and scores higher.' % (len(parents) + 1)]
    else: u.append('Write build.')
    u.append('Keep it short (under 25 lines). Change one idea at a time; the result must stay correct.')
    return ('<|im_start|>system\n' + SYSTEM + '<|im_end|>\n<|im_start|>user\n' + '\n'.join(u) + '<|im_end|>\n<|im_start|>assistant\n```python\n' + header(target))

def clean(target, completion):
    """header + completion -> normalised source with a top-level `build`, or None.  Parsed (ast), never executed."""
    text = header(target) + completion.split('```')[0]
    for _ in range(12):                                                          # a cut-off last line: drop lines until it parses
        try: tree = ast.parse(text); break
        except SyntaxError:
            if '\n' not in text.rstrip('\n'): return None
            text = text.rstrip('\n'); text = text[:text.rindex('\n') + 1]
    else: return None
    if not any(isinstance(x, ast.FunctionDef) and x.name == target.entry for x in tree.body): return None
    tree.body = [x for x in tree.body if isinstance(x, (ast.FunctionDef, ast.Assign, ast.Import, ast.ImportFrom))]
    src = ast.unparse(tree) + '\n'
    return src if len(src) <= 6000 else None

def find_weights(spec, pattern=None):
    """spec: a local directory / file, or a Hugging Face repo id.  -> local path."""
    if os.path.exists(spec):
        if os.path.isdir(spec) and pattern: return sorted(glob.glob(os.path.join(spec, '**', pattern), recursive=True))[0]
        return spec
    from huggingface_hub import snapshot_download
    os.environ.pop('HF_HUB_OFFLINE', None)
    wdir = os.path.join(os.environ.get('FUNSEARCH_WEIGHTS') or os.environ.get('RUNNER_TEMP') or tempfile.gettempdir(), 'funsearch-weights', spec.replace('/', '--'))
    assert not os.path.abspath(wdir).startswith(os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..')) + os.sep), 'weights must stay outside the repository'
    snapshot_download(spec, local_dir=wdir, allow_patterns=[pattern] if pattern else ['*.json', '*.safetensors', '*.txt'])
    return sorted(glob.glob(os.path.join(wdir, pattern)))[0] if pattern else wdir

class QwenHF:
    def __init__(self, spec, dtype=None, threads=None, max_new=260, temperature=0.8):
        import torch
        from transformers import AutoTokenizer, AutoModelForCausalLM
        if threads: torch.set_num_threads(threads)
        path = find_weights(spec); self.torch = torch
        self.device = 'cuda' if torch.cuda.is_available() else 'cpu'
        dtype = dtype or ('bfloat16' if self.device == 'cuda' else 'float32')
        self.tok = AutoTokenizer.from_pretrained(path); self.tok.padding_side = 'left'
        self.model = AutoModelForCausalLM.from_pretrained(path, torch_dtype=getattr(torch, dtype)).to(self.device).eval()
        self.max_new, self.temperature = max_new, temperature
        self.name = '%s (%s, %s, %s)' % (os.path.basename(path.rstrip('/')), 'transformers', dtype, self.device); self.tokens = 0
    def propose(self, target, parents, n):
        torch = self.torch; x = self.tok(prompt(target, parents), return_tensors='pt', add_special_tokens=False).to(self.device)
        with torch.no_grad():
            out = self.model.generate(**x, do_sample=True, temperature=self.temperature, top_p=0.95, max_new_tokens=self.max_new, num_return_sequences=n,
                                      stop_strings=['```'], tokenizer=self.tok, pad_token_id=self.tok.pad_token_id or self.tok.eos_token_id)
        new = out[:, x.input_ids.shape[1]:]; self.tokens += int(new.numel())
        return [clean(target, t) for t in self.tok.batch_decode(new, skip_special_tokens=True)]

class QwenGGUF:
    def __init__(self, spec, pattern='*q4_k_m*', threads=4, max_new=260, temperature=0.8, ctx=4096):
        from llama_cpp import Llama
        path = find_weights(spec, pattern)
        self.llm = Llama(model_path=path, n_ctx=ctx, n_threads=threads, n_gpu_layers=int(os.environ.get('FUNSEARCH_GPU_LAYERS', 0)), verbose=False)
        self.max_new, self.temperature = max_new, temperature; self.name = '%s (llama.cpp)' % os.path.basename(path); self.tokens = 0
    def propose(self, target, parents, n):
        out = []; p = prompt(target, parents)
        for _ in range(n):
            r = self.llm(p, max_tokens=self.max_new, temperature=self.temperature, top_p=0.95, stop=['```', '<|im_end|>'])
            self.tokens += r['usage']['completion_tokens']; out.append(clean(target, r['choices'][0]['text']))
        return out

class Mutate:
    name = 'mutate (no model: random text edits)'
    def __init__(self, seed=0): self.rng = random.Random(seed); self.tokens = 0
    def _edit(self, src):
        rng = self.rng; lines = src.rstrip('\n').split('\n'); k = rng.randrange(6)
        body = [i for i in range(1, len(lines)) if lines[i].strip() and not lines[i].strip().startswith('#')]
        if not body: return src
        i = rng.choice(body)
        if k == 0:
            nums = list(re.finditer(r'(?<![\w.])\d+(?![\w.])', lines[i]))
            if nums: m = rng.choice(nums); lines[i] = lines[i][:m.start()] + str(max(0, int(m.group()) + rng.choice([-1, 1, 1, 2]))) + lines[i][m.end():]
        elif k == 1: lines[i] = lines[i].replace('C.AND', 'C.\0').replace('C.OR', 'C.AND').replace('C.\0', 'C.OR') if rng.random() < .5 else lines[i].replace('C.OR', 'C.AND', 1)
        elif k == 2: lines.insert(i, lines[i])
        elif k == 3 and len(body) > 3: del lines[i]
        elif k == 4:
            j = rng.choice(body); ind = lambda s: len(s) - len(s.lstrip())
            if ind(lines[i]) == ind(lines[j]): lines[i], lines[j] = lines[j], lines[i]
        else:
            names = re.findall(r'\b[a-zA-Z_]\w*\b', lines[i]); other = re.findall(r'\b[a-z]\b|\b[A-Z]\b|\bS0\b|\brest\b', src)
            if names and other: a = rng.choice(names); lines[i] = re.sub(r'\b%s\b' % re.escape(a), rng.choice(other), lines[i], count=1)
        return '\n'.join(lines) + '\n'
    def propose(self, target, parents, n):
        out = []
        for _ in range(n):
            src = self.rng.choice(parents)[0] if parents else target.seeds[0]
            for _ in range(self.rng.choice([1, 1, 2, 3])): src = self._edit(src)
            out.append(clean(target, src[src.index('\n') + 1:]))
        return out

def make(kind, spec=None, **kw):
    if kind == 'mutate': return Mutate(kw.get('seed', 0))
    kw.pop('seed', None)
    if kind == 'hf': return QwenHF(spec, **kw)
    if kind == 'gguf': return QwenGGUF(spec, **kw)
    raise ValueError(kind)
