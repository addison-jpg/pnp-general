# XOR with a fresh variable: `C(x ⊕ f) ≥ max(C(f), C(¬f)) + 3` (L-gen-005, L-gen-006)

Unrestricted circuits (any number of NOT gates): an exact-size result by gate elimination.
A generalization of `L_meta_174` (AND with a fresh variable costs exactly one gate) to XOR.
Model: `PEqualNP.MetaComplexity.HasCircuitSize` (AND, OR, NOT, fan-in at most two, every gate
counted, NOT included, inputs free). `C(g)` is the least circuit size of `g`.

## Status

| Statement | Status |
|---|---|
| L-gen-005 (`xor_lower`): for non-constant `f`, `C(x ⊕ f) ≥ max(C(f), C(¬f)) + 3` | checked row |
| L-gen-006 (`xor_exact`): if `C(f) ≠ C(¬f)`, then `C(x ⊕ f) = min(C(f), C(¬f)) + 4` | checked row |
| `C(x ⊕ f) = min(C(f), C(¬f)) + 4` for every non-constant `f` | OPEN when `C(f) = C(¬f)` |

"Checked row" means: the files build with the pinned toolchain (Lean 4.36.0) and the pinned
Mathlib, have no `sorry`, and `#print axioms` lists only `propext`, `Classical.choice`,
`Quot.sound`. Files: `lean/PEqualNP/General/L005.lean`, `L006.lean` (the statements) and
`lean/PEqualNP/General/XorExtension.lean` (the proof; it imports `L_meta_174` for basic wire
lemmas and `L_meta_716` for the upper bound `min + 4`).

Check it:

    cd lean && lake exe cache get && lake build PEqualNP.General.L005 PEqualNP.General.L006

## The exact Lean statements

    theorem xor_lower (n s : ℕ) (f : (Fin n → Bool) → Bool)
        (hf : ∃ y y' : Fin n → Bool, f y ≠ f y')
        (h : HasCircuitSize (n + 1)
          (fun x => xor (x (Fin.last n)) (f (fun i : Fin n => x i.castSucc))) (s + 3)) :
        HasCircuitSize n f s ∧ HasCircuitSize n (fun y => !f y) s

    theorem xor_exact (n : ℕ) (f : (Fin n → Bool) → Bool) (hf : ∃ y y', f y ≠ f y') (s₀ : ℕ)
        (hdiff : (HasCircuitSize n f s₀ ∧ ¬ HasCircuitSize n (fun y => !f y) s₀) ∨
          (HasCircuitSize n (fun y => !f y) s₀ ∧ ¬ HasCircuitSize n f s₀)) (t : ℕ) :
        HasCircuitSize (n + 1) (fun x => xor (x (Fin.last n)) (f (fun i => x i.castSucc))) (t + 4)
          ↔ (HasCircuitSize n f t ∨ HasCircuitSize n (fun y => !f y) t)

`restrict_three` is the same lower bound for any `F` that changes whenever its last input is
flipped.

## Proof idea

Take any circuit for `x ⊕ f` (no minimality is assumed). For a constant `c`, call a gate
*redundant on side `c`* when, after `x := c`, its function is constant or equals the function of
an earlier wire.

1. Semantic elimination (`se`): any set `S` of gates redundant on side `c` can be dropped, so the
   restriction has a circuit with `t - |S|` gates.
2. Counting (`count_main`): there are 4 redundant gates on one side, or 3 on each side. The proof
   splits on the number of gates that read `x` (every such gate is redundant on both sides):
   - three or more readers: done;
   - two readers: either both are constant on a common side (then the gates that read them give
     a fourth gate on that side, or a third on each side), or they are constant on opposite
     sides (then each has a further reader, which is redundant on that side);
   - one reader: it must be split at every input, so it is constant on both sides; the same
     holds for its only reader, and that gate has a reader;
   - no reader: impossible.
   The tool for "impossible" is `block`: if no split gate outside a set `B` of wires reads a
   split wire of `B`, then the output lies in `B`; but the output is constant on no side.
3. Four gates on side `c` give `C(F|c) ≤ t - 4`, and the other side costs one NOT gate more.
   Three on each side give both bounds directly.

Since `|C(f) - C(¬f)| ≤ 1`, the bound `max + 3` equals `min + 4` exactly when the two sizes
differ, and `L_meta_716` gives the matching upper bound.

## What is left open

If `C(f) = C(¬f) = m`, the theorem gives `m + 3 ≤ C(x ⊕ f) ≤ m + 4`.

A circuit of size `m + 3` would have to be of the following *residual shape* (hand argument, not
Lean-checked; it reruns the case split of `count_main` on a minimal circuit): `x` is read by
exactly two gates `G1 = AND(x, h1)` and `G2 = OR(x, h2)`; `G1` has exactly one reader
`H1 = OR(G1, u1)`; `G2` has exactly one reader `H2 = AND(G2, u2)`; and `H1 ≠ H2`. Every other
case of the count gives a fourth redundant gate on one side.

Finite evidence for `m + 4` (exhaustive, NOT a proof; scripts and logs in `tools/xor-extension/`):

| Functions `f` | Method | Result |
|---|---|---|
| all non-constant 3-variable `f` with `min(C(f), C(¬f)) ≤ 4` (126) | `bfs4b.cpp`, all 4-variable circuits up to 8 gates | `C(x ⊕ f) = min + 4` |
| all 3-variable `f` with `C(f) = C(¬f) = m`, `m = 3, 4, 5, 6, 7` | `synth.py` (SAT exact synthesis), `run3.py` | no circuit with `m + 3` gates |
| all `f` depending on 4 variables with `C(f) = C(¬f) = m`, `m = 4, 5` (30 classes) | `run4.py` | no circuit with `m + 3` gates |
| residual shape, 7 sample `f` on 3 variables | `shape_min.py` | least size of a circuit of the residual shape is `min + 5` or `min + 6`, never `min + 4` |

Classes are taken up to permuting the variables of `f` and replacing `f(y)` by `f(¬y)` (the
dual circuit, AND and OR swapped, shows that this keeps `C(x ⊕ f)`). `XOR_3` and its
complement (`m = 8`) are covered by Red'kin's theorem, so with the rows above every
non-constant `f` on at most 3 variables has `C(x ⊕ f) = min + 4`. Functions `f` on 5 or more
variables are not covered.

The last row suggests a stronger statement that would close the gap: a circuit of the residual
shape for `x ⊕ f` has at least `min(C(f), C(¬f)) + 5` gates. No proof is known here.

## Prior work, as far as searched

- Red'kin (1973) / Kombarov (2011): `C(XOR_n) = 4(n - 1)` in this basis with NOT counted. The
  theorem here gives the inductive step `C(x ⊕ f) ≥ C(f) + 3` for every `f`, not only parities.
- Carmosino, Dang, Jackman, "Simple Circuit Extensions for XOR in PTIME" (arXiv 2511.16903), and
  Ilango (2020): "simple extensions" `C(g) = C(f) + (number of new variables)`.

No source stating `xor_lower` for arbitrary `f` was found in a short search (a handful of web
queries). That is weak evidence of novelty; the argument is classical gate elimination.
