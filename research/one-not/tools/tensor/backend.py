"""Array backends for the bit-sliced evaluator.  NumPy is the default and the only tested path.
torch / jax.numpy are used only when importable AND a GPU is visible (or when TENSOR_BACKEND=torch|jax|numpy is set).
Words are 64-bit; every backend keeps the same bit layout, and everything outside this file is written with
& | ^ ~, reshape, slicing and the few methods below, so a backend is about 30 lines."""
import os
import numpy as np


class NumpyBackend:
    name = 'numpy'
    def const(self, v): return np.uint64(v)
    def from_numpy(self, a): return np.ascontiguousarray(a, dtype=np.uint64)
    def to_numpy(self, a): return np.asarray(a, dtype=np.uint64)
    def zeros(self, shape): return np.zeros(shape, np.uint64)
    def zeros_like(self, a): return np.zeros_like(a)
    def stack(self, xs, axis): return np.stack(xs, axis=axis)
    def shr(self, x, k): return x >> np.uint64(k)       # logical (unsigned)


class TorchBackend:
    """int64 words (torch has no usable uint64 bit ops); right shift is made logical by masking."""
    name = 'torch'
    def __init__(self, torch, device):
        self.t = torch; self.dev = device
    def const(self, v):
        v &= (1 << 64) - 1
        return self.t.tensor(v - (1 << 64) if v >> 63 else v, dtype=self.t.int64, device=self.dev)
    def from_numpy(self, a): return self.t.from_numpy(np.ascontiguousarray(a, dtype=np.uint64).view(np.int64)).to(self.dev)
    def to_numpy(self, a): return a.cpu().numpy().view(np.uint64)
    def zeros(self, shape): return self.t.zeros(shape, dtype=self.t.int64, device=self.dev)
    def zeros_like(self, a): return self.t.zeros_like(a)
    def stack(self, xs, axis): return self.t.stack(xs, dim=axis)
    def shr(self, x, k): return (x >> k) & ((1 << (64 - k)) - 1)


class JaxBackend:
    name = 'jax'
    def __init__(self, jax):
        jax.config.update('jax_enable_x64', True); self.jnp = jax.numpy
    def const(self, v): return self.jnp.uint64(v)
    def from_numpy(self, a): return self.jnp.asarray(np.ascontiguousarray(a, dtype=np.uint64))
    def to_numpy(self, a): return np.asarray(a, dtype=np.uint64)
    def zeros(self, shape): return self.jnp.zeros(shape, self.jnp.uint64)
    def zeros_like(self, a): return self.jnp.zeros_like(a)
    def stack(self, xs, axis): return self.jnp.stack(xs, axis=axis)
    def shr(self, x, k): return x >> self.jnp.uint64(k)


def _try_torch(force):
    try:
        import torch
    except Exception: return None
    if torch.cuda.is_available(): return TorchBackend(torch, 'cuda')
    if getattr(torch.backends, 'mps', None) and torch.backends.mps.is_available() and force: return TorchBackend(torch, 'mps')
    return TorchBackend(torch, 'cpu') if force else None


def _try_jax(force):
    try:
        import jax
    except Exception: return None
    if any(d.platform in ('gpu', 'tpu') for d in jax.devices()) or force: return JaxBackend(jax)
    return None


def get_backend(name=None):
    """name: 'numpy' | 'torch' | 'jax' | None (auto: a GPU torch, else a GPU jax, else numpy; env TENSOR_BACKEND overrides)."""
    name = name or os.environ.get('TENSOR_BACKEND') or 'auto'
    if name == 'numpy': return NumpyBackend()
    if name == 'torch':
        b = _try_torch(True)
        if b: return b
        raise RuntimeError('torch not importable')
    if name == 'jax':
        b = _try_jax(True)
        if b: return b
        raise RuntimeError('jax not importable')
    return _try_torch(False) or _try_jax(False) or NumpyBackend()
