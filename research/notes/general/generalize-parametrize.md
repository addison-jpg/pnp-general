# Parametrizing the constants 4 and 6 in the XOR extension results

Companion to `generalize-xor-extension.md` and `generalize-xor-residual.md`. Same model:
AND, OR, NOT of fan-in at most two, every gate counted, inputs free. `C(g)` is the least
circuit size of `g`. For `f` on `n` inputs and `k` fresh inputs `x_1, ..., x_k`, write
`F_k = x_1 ⊕ ... ⊕ x_k ⊕ f` (`F_0 = f`), `lo = min(C(f), C(¬f))`, `hi = max(C(f), C(¬f))`.
Known: `hi - lo ≤ 1`.

## (a) The constant 4 as a function `c(k)` of the number `k` of fresh variables

### Proved (Lean, `proofs/main/PEqualNP/General/XorIterate.lean`, namespace `PEqualNP.General.XorIterate`)

For non-constant `f` and `k ≥ 1`:

* `iter_lower`: `C(F_k) ≥ hi + 3k`.
* `iter_upper`: `C(F_k) ≤ lo + 4k` (for every `f`, `k ≥ 1`).

Proof: induction on `k`. The lower bound applies `xor_lower` to `g = F_{k-1}`, which is
non-constant (`extIter_nonconst`), and uses only the first conjunct of its conclusion
(`C(g) ≤ s + 3(k-1)`), then the induction hypothesis. The upper bound applies the first
conjunct of `L_meta_716` to `g = F_{k-1}`, starting from `f` or `¬f`.

Validity of the iteration. The intermediate function is `g = F_{k-1} = x_{k-1} ⊕ F_{k-2}`, which
is non-constant, and `¬g = x_{k-1} ⊕ ¬F_{k-2}`. Both proofs avoid computing `max` or `min` over
`{g, ¬g}`. The lower bound uses only the first conjunct of `xor_lower` (`C(g) ≤ C(F_k) - 3`),
so `C(F_k) ≥ C(F_{k-1}) + 3 ≥ hi + 3k` by induction. The upper bound uses only the first
conjunct of `L_meta_716` (`C(F_k) ≤ C(g) + 4`), so `C(F_k) ≤ C(F_{k-1}) + 4 ≤ lo + 4k`. The
second conjunct of `xor_lower` and `¬g` are not used.

### What the two bounds give

`hi + 3k ≤ C(F_k) ≤ lo + 4k`. The gap is `k - (hi - lo) ≥ k - 1`, so the bounds agree only for
`k = 1` and `hi = lo + 1`.

| `k` | statement | status |
|---|---|---|
| 1 | `C(F_1) = lo + 4` if `C(f) ≠ C(¬f)` | proved (`xor_exact`) |
| 1 | `C(F_1) = lo + 4` if `C(f) = C(¬f)` | open (evidence in (b)) |
| 2 | `C(F_2) ∈ [lo + 7, lo + 8]` if `C(f) ≠ C(¬f)`; `C(F_2) ∈ [m + 6, m + 8]` if `C(f) = C(¬f) = m` | range proved, exact value open |
| `k ≥ 2` | `C(F_k) = lo + 4k` | open for every `f` |

The `k = 2` range is sharper than the iterated bound `hi + 6` when `hi = lo + 1`. If
`C(f) ≠ C(¬f)`, `xor_exact` gives `C(F_1) = C(¬F_1) = lo + 4`, because `¬F_1 = x ⊕ ¬f` and
`f`, `¬f` have the same `lo`. Then `xor_lower` applied to `g = F_1` gives `C(F_2) ≥ lo + 7`.
So `F_1` is a function with `C(g) = C(¬g)`, the open type of `xor_exact`, and `k = 2` is open
even when `C(f) ≠ C(¬f)`. (This sharper range is a consequence of `xor_lower` and
`xor_exact`; it is not a separate Lean statement.)

The honest parametrized statements are therefore:

* `C(F_k) ≤ lo + 4k` is proved.
* `C(F_k) ≥ hi + 3k` is proved.
* `C(F_k) = lo + 4k` is proved only for `k = 1` with `C(f) ≠ C(¬f)`. For `f` the parity of
  `n` inputs it holds for all `k` by Red'kin's theorem (`C(XOR_{n+k}) = 4(n + k - 1)`).
* Consequence of one open statement. If `C(x ⊕ g) = min(C(g), C(¬g)) + 4` held for every
  non-constant `g` (the open case `C(g) = C(¬g)` of `xor_exact`), then `C(F_k) = lo + 4k` for
  every `k`, by induction on `k` with `g = F_{k-1}` (not formalized).

## (b) The constant 6 as a parameter `M`

Statement: no counterexample to `C(x ⊕ f) = lo + 4` with `C(f) = C(¬f) = m ≤ M`.

### Data

`f` depending on `k` of its variables has `m ≥ k - 1`, so `m ≤ M` forces `k ≤ M + 1`.
The runs (`research/tools/xor-extension/`, `research/tools/xor-extension/residual/`):

| `k` | exact synthesis or residual-shape SAT | covers `m` |
|---|---|---|
| 3 | exact synthesis (`synth.py`) | `m ≤ 7` |
| 4 | `sat-4var.log` (exact synthesis) | `m ≤ 5`; residual shape `r = 9` (`k4r9.log`, 149 s) gives `m = 6` |
| 5 | `loc567.log`, `loc567r9.log`: `r = 7, 8, 9` UNSAT (3 s, 74 s, 920 s) | `m ≤ 6` |
| 6 | `r = 8` UNSAT (110 s), `r = 9` UNSAT (3165 s) | `m ≤ 6` |
| 7 | `r = 9` UNSAT (4467 s) | `m = 6` |

Honest claim: `M = 6`, conditional on the encoding of `cegar2.py` and on the hand derivation
of the residual shape (`generalize-xor-residual.md` §1). For `k ≤ 7` variables and `r ≤ 9`
gates (`m ≤ 6`) the data covers every `f`. For `k = 3` the data goes to `m = 7`, but `M` is
a bound over all `k`, so `M = 6` is the largest value covered for every number of variables.
This is evidence, not a proof; the statement for every `M` is the open conjecture.

### Cheapest next extension: `M = 7` (`r = 10`)

`M = 7` needs `r = 10` for `k = 4, 5, 6, 7, 8` (`k ≤ M + 1 = 8`); `k = 3` is already covered.
The logged timings give the growth with `r`: `k = 5`: 74 s at `r = 8`, 920 s at `r = 9`
(factor 12); `k = 4`: 149 s at `r = 9`, and `loc.py 4 10` and `loc.py 4 11` were stopped by
the 1500 s timeout (`locF4.log`), so `k = 4`, `r = 10` already exceeds 25 minutes. With the
factor 12 per added gate, estimates for `r = 10` (single thread, same solver) are: `k = 4`
more than 1500 s (measured lower bound; extrapolation about 30 minutes), `k = 5` about
3 hours, `k = 6` about 10 hours, `k = 7` about 15 hours, `k = 8` not estimated (a larger
instance than any run so far). None of these fits the 10-minute limit of this task, so
no run was launched. The cheapest single step is `k = 4`, `r = 10`, with at least 25 minutes.
The extrapolation is a rough factor argument from two data points per `k`, not a measurement.

## Summary: proved, evidence, open

* Proved (Lean, standard axioms): `iter_lower`, `iter_upper`.
* Evidence only: `C(x ⊕ f) = lo + 4` for `C(f) = C(¬f) = m ≤ 6` (any number of variables),
  and for `m ≤ 7` on 3 variables.
* Open: `C(F_k) = lo + 4k` for `k ≥ 2` in every case; `C(F_1) = lo + 4` when `C(f) = C(¬f)`;
  `M ≥ 7` for all numbers of variables.
