# Tensor backend: benchmark (NumPy, 4 cores, 15 GB, no GPU)

Reproduce: `python3 -I research/one-not/tools/tensor/bench.py speed|big|maxn|mixed_n`. Baselines are the existing scripts' own loops:
`continuous.slack_table(c, R, parts=True)` for every R (the inner loop of `A5_transfer_t1.py` and `continuous.py mixed`), and the DD-state
test at the head of `A14_bottom_hall.analyse` / `A7.check_state` at all 3^n states. Exact equality is in `test_tensor.py` (114 stored circuits
incl. the t4/t5/t6 witnesses, plus random n = 1..8; the earlier 3,199-circuit `--f2lib` run passed before the final refactor and was not rerun
after it, stopped on request).

## Speed-up (same circuits, all stored one-NOT circuits with 6 <= n <= 9, total over the set)

| task | old | tensor | speed-up |
|---|---|---|---|
| slack at all 3^n mixed states (A5 loop), dense table | 3.21 s | 0.95 s | 3x |
| same, `mixed_stats` reductions only (no unpacking) | 3.21 s | 0.87 s | 4x |
| DD states at all 3^n states (A14 head, n <= 8) | 0.6 s | 0.064 s | 9x |
| slack at all cubes, one circuit | 0.035 s | 0.069 s | 0.5x (overhead-bound at n <= 9) |

The gain grows with n, since the stored circuits are tiny:

| task | old | tensor | speed-up |
|---|---|---|---|
| cube slack, n = 16, 55 gates | 0.26 s | 0.013 s | 19x |
| cube slack, n = 22, 46 gates | 34 s | 0.9 s | 38x |
| mixed slack, all 4.8M states, n = 14, 31 gates | about 6 s (extrapolated from 60 sampled R) | 0.42 to 0.7 s | about 10x |

The A14 Hall / matroid-union part is not tensorised (it is a combinatorial search); only the DD-state enumeration is.

## Largest n that fits (15 GB RAM)

| quantity | largest n measured | time, peak RSS |
|---|---|---|
| truth tables (all wires) | 25 with 50 gates (n = 28 by size: 2^n / 8 bytes per wire) | 0.4 s |
| slack at every cube | 25 (synthetic, 50 gates) | 44 s, 6.8 GB; n = 24: 17 s, 3.2 GB; n = 26 was killed (memory) |
| mixed slack, all 3^n states (`mixed_stats`) | 16 measured (43M states, 55 gates) | 15 s, 1.1 GB |

Memory is dominated by the unpacked `int32` slack table (4 bytes per cube); a packed-only reduction (`mixed_stats`) stays small.
`mixed_stats` time grows about 3^n: n = 18 is about 2.5 min, n = 20 about 20 min on this machine (extrapolated, not run).
