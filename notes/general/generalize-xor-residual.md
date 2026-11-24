# The residual shape for `C(x ⊕ f)` when `C(f) = C(¬f)`: partial results

Written by a Fable helper of Generalize, 2026-11-24, stopped early when the seat stood down. NOT verified by
Generalize: "PROVED" below means a hand argument by the helper, not Lean-checked and not refereed. Scripts and logs:
`tools/xor-extension/residual/`.

Companion to `generalize-xor-extension.md`. Same model (AND/OR of fan-in 2, NOT, every gate
counted, inputs free, no constants). `f` is non-constant on inputs `y`, `x` is a fresh input,
`C(f) = C(¬f) = m`, and `D` is a hypothetical circuit for `F = x ⊕ f` with `t = m + 3` gates.

**Result in one line: the conjecture `C(x ⊕ f) = m + 4` is NOT proved here and NOT disproved.**
The work was stopped early (see the last section). What exists: a rigorous re-derivation of the
residual shape (no gap found), a list of further necessary conditions, a SAT check that uses
them and does not need a list of candidate functions, and a clean statement of what blocks a
proof.

Each claim is marked PROVED (full hand argument below, not Lean-checked), CHECKED (script and
range given), UNVERIFIED (argued in my head only, not written out and not run), or CONJECTURE.

Scripts and logs: `/tmp/claude-0/-home-user/1e731afa-6bae-5bb8-9550-bd1ed9db3359/scratchpad/fable-xor/`
(`cegar.py`, `cegar2.py`, `loc.py`, `loc2.py`, `*.log`). That directory is a scratchpad and is
not durable; copy the four scripts to `tools/xor-extension/` if they are to be kept.

## 1. The residual shape, re-derived (PROVED, hand argument)

Used facts: (a) `count`-style redundancy: with `x := c`, a gate is *redundant on side c* when
its restricted function is constant or equals that of an earlier wire; by the Lean lemma `se`
any set of gates redundant on side `c` can be dropped. (b) `t = m + 3 = C(F)` by `xor_lower`,
so `D` is a minimal circuit for `F`.

**M1 (minimal circuit).** In `D` no gate computes a constant, no gate computes the same
function of `(x, y)` as another wire (inputs included), and every gate except the output has a
reader. *Proof.* A duplicate can be merged into the earlier wire; a dead gate can be dropped.
Constant gates: every non-constant reader of a constant gate equals its other input (a NOT
reader is constant). The output is not constant. So bypass every such reader to its other
input and delete all constant gates; at least one gate disappears. ∎

**R (three per side).** If four gates are redundant on one side `c`, then `F|x=c` has `t - 4 =
m - 1` gates, contradicting `C(f) = C(¬f) = m`. So at most three gates are redundant on each
side.

Every reader of `x` is redundant on both sides (`NOT x`: constant on both; `AND(x, h)`:
constant 0 on side 0, equal to `h` on side 1; `OR(x, h)`: dual; here `h ≠ x` by M1). A reader
of a gate that is constant on side `c` is redundant on side `c`. The output is constant on no
side, so a gate that is constant on some side is not the output and has a reader.

**No reader of `x` reads another reader of `x`.** `op(x, op'(x, h))` and `op(x, NOT x)` are, in
all cases, constant or equal to `x` or equal to the inner gate. M1 forbids this.

Let `r` be the number of gates reading `x`; `1 ≤ r ≤ 3` by R (and `r = 0` is impossible).

- `r = 3`: two readers `P, Q` are constant on a common side `c`. `P` has a reader, which is
  not a reader of `x`, hence a fourth gate redundant on side `c`. Contradiction.
- `r = 1`, reader `P`: all influence of `x` passes through `P`, and `F` flips with `x` at every
  `y`, so `P` flips at every `y`; `P` is constant on one side, hence on both. `P = AND(x, h)`
  would give `h|x=1 = 1` and `P = x` (M1). So `P = NOT x`. No reader of `P` is a NOT (it would
  equal `x`). Let `a` be a reader of `P`; `a` is constant on some side `c`. `a` has a reader
  `a'`; `a'` reads `P`'s reader `a`, and if `a'` also read `P` it would be `op(P, op'(P, h))`,
  a duplicate. So besides `P, a, a'` (all redundant on side `c`) any further reader of `P` is a
  fourth. Hence `a` is the only reader of `P`; but then `a` flips at every `y`, is constant on
  both sides, so equals `x` or `¬x = P`. Contradiction with M1. So `r = 1` is impossible.
  (This is slightly stronger than the parent note, which only says "a fourth redundant gate".)
- `r = 2`, readers `P, Q`:
  - `P = NOT x`: `P` is constant on both sides, `Q` on a side `c`. On side `c` the readers of
    `P` and of `Q` are redundant, so there is exactly one such gate `R`, reading both. Then `R`
    is constant on side `c` and has a reader: a fourth. Contradiction.
  - both AND (or both OR): both constant on the same side; same argument.
  - `P = G1 = AND(x, h1)`, `Q = G2 = OR(x, h2)`: side 0 gives `{G1, G2} ∪ readers(G1)`, side 1
    gives `{G1, G2} ∪ readers(G2)`, so each of `G1`, `G2` has exactly one reader `H1`, `H2`.
    `H1 = H2 = op(G1, G2)` is `G1` or `G2` (since `G1 ≤ x ≤ G2`), forbidden. `H1 = NOT G1` or
    `H1 = AND(G1, u1)` is constant on side 0 and has a reader; that reader is not `G2`
    (`OR(x, NOT(x ∧ h1)) = 1`, `OR(x, x ∧ h1 ∧ u1) = x`), so it is a fourth on side 0.
    Hence `H1 = OR(G1, u1)`, and dually `H2 = AND(G2, u2)`.

So the residual shape of the parent note is correct; **I found no gap in that derivation.**
`u1, h1` are wires other than `x, G1, G2`; same for `u2, h2`.

**Duality (PROVED).** Swapping AND/OR in `D` gives a circuit for `x ⊕ f(¬y)`, and
`C(f(¬y)) = C(¬f)`, `C(¬f(¬y)) = C(f)`. It exchanges the roles of `(G1, H1)` and `(G2, H2)`.
`H1`, `H2` cannot each be downstream of the other, so one may assume `H2` is not downstream of
`H1`; then `h2, u2` depend on `y` only.

**One correction to a tempting shortcut.** "The output is not `H1` or `H2`" is false in
general: in the dualized frame the output is not `H2` (then `F = u2 ∧ (x ∨ h2)` would be
monotone in `x`), but it can be `H1`. The SAT-found shape circuits of size `min + 5` have the
shape gate as output.

## 2. Further necessary conditions for a counterexample (PROVED)

Write `E0` for the gates `Z ∪ {H2}` on side 0 (`H2` acts as `AND(h2, u2)`, readers of `H1`
read `u1`) and `E1` for `Z ∪ {H1}` on side 1. Both have `m` gates and compute `f`, `¬f`.

- N1. `E0` and `E1` are optimal circuits. So on side 0 the wires of `E0` (inputs `y` included)
  are non-constant and pairwise different as functions of `y`; same for `E1` on side 1.
- N2. No wire of `E0` other than the output computes `¬f`; no wire of `E1` other than the
  output computes `f` (its cone misses the output gate, giving `m - 1` gates).
- N3. The output gate of `D` is not a NOT (else `x ⊕ ¬f` has `m + 2` gates, against
  `xor_lower` applied to `¬f`).
- N4. `u2 ≰ h2`, `h2 ≰ u2`, `u2 ∧ h2 ≠ 0` (from N1 for the gate `H2` in `E0`); on side 1,
  `u1 ≰ h1` and `h1 ≰ u1`.
- N5. Split `x` into `x1` (feeding `G1`) and `x2` (feeding `G2`). `g(x2, y) = D(0, x2, y)` has
  the `m + 1` gates `Z, G2, H2`, depends on `x2`, and `g(0, ·) = f`; by `restrict_one` its
  size is at least `m + 1`. So this circuit is optimal for `g = f ⊕ (x2 ∧ 1_S)`, and likewise
  `D(x1, 1, y)` is optimal (`m + 1` gates) for `¬f ⊕ (¬x1 ∧ 1_T)`.
- N6. Let `ψ = D(1, 0, y)`. `D(1, x2, y)` and `D(x1, 0, y)` have `m + 2` gates. If `ψ = f`
  everywhere the first computes `x2 ⊕ f`; if `ψ = ¬f` everywhere the second computes
  `x1 ⊕ f`; both contradict `xor_lower`. So `ψ` agrees with `f` at some `y` and with `¬f` at
  another.
- N7 (frame of the duality remark; `z(b, y)` is `Z` with `H1 := u1` and the wire `H2` replaced
  by a free input `b`). `z(0, ·)` has at most `m - 2` gates and equals `f` wherever
  `u2 ∧ h2 = 0`. So there is a `y` with `u2 = h2 = 1` (this `y` lies in `T`) at which `z`
  depends on `b`. Hence `z` depends on `b` both on `S` (where it is `b ⊕ f`) and at a point
  outside the set `{u2 = 1, h2 = 0}` where `H2` is sensitive to `x`.
- N8. Substituting wires for the two copies of `x` gives nothing new: `D(w1, w2, y) = f`
  forces `w1 = 0` on `T`-type points and `w2 = 0` on `S`; the choices that also collapse the
  four shape gates are `(u1, h2)`, which is `E0` again (and `(h1, u2)` is `E1`).
- N9 (only when neither of `H1`, `H2` is downstream of the other). Every `y` must have `H1` or
  `H2` sensitive to `x`, which gives `u1 ≤ u2`, `h2 ≤ h1`, `u1 ∧ h2 = 0`, `h1 ∨ u2 = 1`. Then
  any gate that combines `H1` and `H2` (or their negations) directly is constant or a
  duplicate on side 0 or on side 1, so N1 forbids a gate reading both.

## 3. SAT checks (CHECKED)

Encoding (`cegar2.py`, function `build`): the residual shape as in `synth.py`, the function
`f` left FREE, the output flips with `x` at every `y`, plus the necessary conditions M1, N1,
N2, N3 (flags `A`, `B`+`C`+`D`, `E`, `F`). `loc2.py` adds "every `y` input is read" (valid
when `f` depends on all its variables). UNSAT means: no counterexample with that number `k`
of `y`-variables and `t = r` gates, for any `f`, without needing the exact sizes of `f`.

| `k` | `r = m + 3` | result | script |
|---|---|---|---|
| 3 | 5, 6, 7, 8, 9 | UNSAT (0 candidate functions) | `cegar.py` |
| 4 | 9 | UNSAT, 149 s | `cegar.py` |
| 5 | 7, 8 | UNSAT | `loc2.py` |
| 6 | 8 | UNSAT | `loc2.py` |
| 4 | 10, 11 | NO RESULT (timeout 1500 s each) | `loc.py` |
| 5, 6, 7 | 9 | NOT RUN TO COMPLETION (stopped) | `loc2.py` |

New over the parent note: `k = 4, m = 6`; `k = 5, m ≤ 5`; `k = 6, m = 5`. Had the `r = 9`
runs for `k = 5, 6, 7` finished UNSAT, the statement would be "no counterexample with
`m ≤ 6`, any number of variables" (an `f` depending on `k` variables has `m ≥ k - 1`). They
did not finish. The encoding was sanity-checked only in one direction: without the local
flags it finds the known shape circuits (`k = 3, r = 8`, 44 functions, all with smaller
circuits). I did not cross-check it against an independent implementation.

Ablation at `k = 3` (CHECKED, `cegar2.py`, `loc.py`): flag `B` alone (no gate of `E0` constant
on side 0, none of `E1` constant on side 1) is already UNSAT for `r ≤ 9`, but SATISFIABLE for
`r = 10, 11, 12, 13` (`locB3.log`). `B`+`D` is UNSAT at `r = 9`; not run beyond.

## 4. Why no local argument can close it

The small-size UNSAT results suggest a "local lemma": *a residual-shape circuit whose output
flips with `x` everywhere has a constant or duplicate wire in `E0` or in `E1`*. That lemma
would prove the conjecture.

**I believe the local lemma is false for larger circuits (UNVERIFIED: constructed by hand, not
evaluated by machine).** Sketch: take `Z = (g ⊕ H1) ⊕ H2` with the two XORs nested (not
`g ⊕ (H1 ⊕ H2)`, which hits N9), `g = y3`, `u1 = y0`, `h1 = ¬y1 ∨ y2`, `u2 = y0 ∨ y1`,
`h2 = ¬y0 ∧ y2`, so that exactly one of `H1`, `H2` is sensitive at each `y`. About 17 gates.
The resulting `f = y3 ⊕ y0 ⊕ (¬y0 ∧ y1 ∧ y2)` has far smaller circuits, by an algebraic
rewrite of the whole XOR chain, not by any constant or duplicate wire. If this checks out, any
proof must use optimality of `E0`, `E1` in a non-local way. **First thing to do next: evaluate
this circuit and run `build`'s constraints on it.**

## 5. The cleanest open statement (CONJECTURE)

In the frame of section 1 (`h2, u2` functions of `y`), let `z(a, b, y)` be the function of the
`m - 1` gates `Z` with the wires `H1`, `H2` replaced by free inputs `a`, `b`, and let `u1, h1`
be the corresponding tapped wires (functions of `b, y`).

> **Open.** There are no `Z`, `u1, h1, u2, h2` with
> `z(u1, u2 ∧ h2, y) = f(y)` and `z(u1 ∨ h1, u2, y) = ¬f(y)` for all `y`
> (`u1, h1` evaluated at the same `b`) and `C(f) = C(¬f) = |Z| + 1`.

Equivalently: `f` and `¬f` have optimal circuits that are the same `m - 1` gates plus one AND
gate (for `f`) or one OR gate (for `¬f`), and removing either extra gate gives the same
function `φ`, which equals `¬f` on `S` and `f` on the complement `T`, both non-empty.
A sufficient lemma: *every residual-shape circuit with `t` gates for `x ⊕ f` yields a circuit
with `t - 4` gates for `f` or for `¬f`.* The SAT data of the parent note (`min + 5`, `min + 6`)
is consistent with the stronger `t - 5`.

Sub-case tried and NOT settled: output `= H1`. There `f = 0` on `T`, `φ = ¬f ∧ 1_S`,
`f ≤ u2 ∧ ¬h2`, `¬f = φ ∨ h1`; every hand construction hit a duplicate wire, but I have no
proof.

## 6. Where I stopped, and what to try next

Stopped on instruction, after roughly the exploration above; no proof attempt reached a
complete argument and no counterexample candidate was found.

1. Verify (or refute) the 17-gate example of section 4 mechanically.
2. Finish `loc2.py` for `(k, r) = (5, 9), (6, 9), (7, 9)` to get "no counterexample with
   `m ≤ 6`". Then `(4, 10)`, which needs more than 25 minutes or symmetry breaking (fix the
   dualized frame, order independent gates).
3. Counterexample search: `cegar.py k r` already does CEGAR over `f` (blocks `f` when `C(f)`
   or `C(¬f)` is at most `r - 4`). It prints `COUNTEREXAMPLE CANDIDATE` if one survives; that
   line would still need the certificate `C(f), C(¬f) ≥ r - 3` re-run independently. Satisfiable
   instances may be found fast at `r = 11, 12` even where UNSAT proofs are slow.
4. Proof direction with the most structure: N5 and N7. `Z` holds `b ⊕ f` on `S` and also
   depends on `b` at a point with `u2 = h2 = 1`; a partial-domain version of `count_main` for
   the input `b` of `z` (how many gates of `Z` die under `b := 0`) combined with
   `f = z(0, ·)` off `{u2 ∧ h2 = 1}` is the natural next step. I did not get a bound from it.
