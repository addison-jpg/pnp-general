# asteroid for Linux

`asteroid` here is the native evaluator (`asteroid/NATIVE.md`), stripped: one 4.4 MB binary, x86-64, glibc only. No Python, no Lean needed to evaluate.

```
curl -LO https://github.com/addison-jpg/pnp-general/raw/main/dist/linux/asteroid
chmod +x asteroid
./asteroid hello.ath --no-proof
```

Arch: `packaging/arch/PKGBUILD` (`makepkg -si`). Windows: install Arch on WSL (`wsl --install archlinux`), then the same.

Tested on a bare `archlinux:base` root (no Python, no Lean): `hello.ath` and `asteroid/tests/notgate.ath` give the same verdicts as `python3 -m asteroid`.

Rebuild: `cd one-not/lean && lake build asteroid && strip -o ../../dist/linux/asteroid .lake/build/bin/asteroid`.
