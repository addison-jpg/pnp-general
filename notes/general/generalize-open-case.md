# The open case `C(f) = C(¬f)` of `C(x ⊕ f) = min + 4`: candidate lemmas and their status

Written by a Fable helper of Generalize, 2026-11-24. Companion to `generalize-xor-extension.md`
and `generalize-xor-residual.md`; same model (`HasCircuitSize`: AND/OR of fan-in 2, NOT, every
gate counted, inputs free).

**Result in one line: the open case is NOT proved and NOT refuted.** No Lean file
`XorOpenCase.lean` was written, because no complete proof exists. This note records every
candidate lemma that was tried, with a status label on every claim:

- CHECKED: machine-checked (Lean, or a script that evaluates a concrete object exhaustively).
- EVIDENCE: SAT or finite enumeration on the stated range only.
- UNVERIFIED: hand argument, written out below, not machine-checked and not refereed.

Scripts and logs: `tools/xor-extension/opencase/`.

## 0. Setting and notation

`f` is non-constant on inputs `y`, `x` is a fresh input, `C(f) = C(¬f) = m`. A *counterexample*
is a circuit `D` for `x ⊕ f` with `t = m + 3` gates. By `generalize-xor-residual.md` §1
(UNVERIFIED hand derivation, no gap found by two readers) a counterexample has the residual
shape: `x` is read by exactly `G1 = AND(x, h1)` and `G2 = OR(x, h2)`; the only reader of `G1` is
`H1 = OR(G1, u1)`; the only reader of `G2` is `H2 = AND(G2, u2)`. `Z` is the set of the other
`m - 1` gates. *Side `c`* means `x := c`. Minimality gives M1 (no constant gate, no two wires
with the same function, every gate except the output has a reader) and N1 (the side-0 circuit
`E0 = Z ∪ {H2}` is optimal for `f`, the side-1 circuit `E1 = Z ∪ {H1}` is optimal for `¬f`).

Write `a` for the wire `H1` and `b` for the wire `H2`. `(a0, b0)` are their functions of `y` on
side 0, `(a1, b1)` on side 1. *Frame A* means: `H2` is not downstream of `H1` (then `u2`, `h2`
are functions of `y` alone, `b0 = u2 ∧ h2`, `b1 = u2`). One of frame A and its dual always
holds (duality: exchange AND and OR; this exchanges `(G1, H1)` with `(G2, H2)` and `f(y)` with
`f(¬y)`, and keeps the hypothesis `C(f) = C(¬f) = m`).

## 1. Summary table

| # | Candidate lemma | Status |
|---|---|---|
| L1 | Local lemma: a residual-shape circuit has a constant or duplicate wire on side 0 or on side 1 | REFUTED, CHECKED (`residual/ex17.py`, earlier note §4) |
| L2 | Abstract core: if `f = z(a0, b0, y)`, `¬f = z(a1, b1, y)` for a circuit `z` with `ζ` gates and ARBITRARY functions `a0 ≤ a1`, `b0 ≤ b1` of `y`, then `min(C(f), C(¬f)) ≤ ζ` | REFUTED, UNVERIFIED hand counterexample (§3); the cost of computing `u1, h1, u2, h2` inside `Z` cannot be dropped |
| L3 | INV: on side 0 never `H1 = H2 = 1`; on side 1 never `H1 = H2 = 0` | holds; UNVERIFIED hand proof (§2) and EVIDENCE (`inv.py`: `k = 3, r ≤ 8`; `k = 4, r = 7`; `k = 2, r = 9`) |
| L4 | OUT: in a counterexample the output gate is neither `H1` nor `H2` | holds; UNVERIFIED hand proof (§4); EVIDENCE consistent (§5) |
| L5 | MONO, first step: in frame A, if no path from `H1` to the output passes a NOT gate, then `f ≤ u2 ∧ ¬h2`, `f = w(0, y) ∧ ¬h2`, and at most one gate of `Z` is redundant under `H2 := 0` | holds; UNVERIFIED hand proof (§4) |
| L6 | MONO: in frame A, a counterexample has a NOT gate on some path from `H1` to the output (`z` is not monotone increasing in `a`) | holds; UNVERIFIED hand proof (§4, written after L4 and read once only); the decreasing variant is only sketched |
| L7 | SHAPE+5: every residual-shape circuit with `r` gates for `x ⊕ f` (no minimality assumed) has `r ≥ min(C(f), C(¬f)) + 5` | holds on the tested range, EVIDENCE (§5): every non-constant `f` on 3 variables reachable with `r ≤ 9`; with output `H1` or `H2` also `r = 10` and `k = 4, r ≤ 9` |
| L8 | SHAPE+6 when the output is not `H1`, `H2` | holds on the tested range, EVIDENCE (§5): `k = 3`, `r ≤ 9` |
| L9 | The conjecture itself for `f` on 4 variables with `m = 7` | holds, EVIDENCE (§5: SAT, fixed `f`, all 65 classes UNSAT) |

The single most promising unproved lemma is stated in §6.

## 2. INV and the five transition types (UNVERIFIED hand proof; EVIDENCE by SAT)

Frame A. `u1`, `h1` may depend on `b`; write `u1(b, y)`, `h1(b, y)`. Let `z(a, b, y)` be the
output as a function of the two wires and `y`. Then `a0 = u1(b0)`, `a1 = u1(b1) ∨ h1(b1)`,
`f = z(a0, b0)`, `¬f = z(a1, b1)`, and `φ = z(u1(b1), b1)` (the function of `Z` alone, `G1 := 0`,
`G2 := 1`). Let `S = {φ = ¬f}`, `T = {φ = f}`.

- On `S`: `z(u1(b1), b1) ≠ z(u1(b0), b0)`, so `b1 ≠ b0`: `u2 = 1`, `h2 = 0`, `b0 = 0`, `b1 = 1`.
- On `T`: `z(u1(b1), b1) ≠ z(a1, b1)`, so `u1(b1) = 0`, `h1(b1) = 1`, `a1 = 1`.
- **INV, side 1:** `a1 ∨ b1 = 1` everywhere (on `T` `a1 = 1`, on `S` `b1 = 1`).
- **INV, side 0:** `a0 ∧ b0 = 0` everywhere: `b0 = 1` forces `y ∈ T` and `b1 = b0 = 1`, hence
  `a0 = u1(b0) = u1(b1) = 0`.

The statement of INV is self-dual, so it holds without the frame. `inv.py k r` searches for a
violation among all residual-shape circuits whose output changes with `x` at every `y` (no
minimality): UNSAT for `(k, r) = (3, 5), (3, 6), (3, 7), (3, 8), (4, 7), (2, 9)` (`inv.log`).

Consequence. For each `y` the pair `(a, b)` moves monotonically from its side-0 value to its
side-1 value, and the output changes. Only five moves are possible:

| type | side 0 → side 1 | `f` | `¬f` |
|---|---|---|---|
| A | `00 → 10` | `z00` | `z10` |
| B | `00 → 01` | `z00` | `z01` |
| C | `00 → 11` | `z00` | `z11` |
| D | `10 → 11` | `z10` | `z11` |
| E | `01 → 11` | `z01` | `z11` |

Here `z_ij(y)` is `Z` with the wires `H1`, `H2` replaced by the constants `i`, `j`. Each `z_ij`
has at most `m - 2` gates (a reader of a constant wire is redundant), so in a counterexample no
`z_ij` equals `f` or `¬f`, and no circuit made of one `z_ij` plus one further gate does. In
particular `z00 = f` exactly on the types A, B, C and `z11 = ¬f` exactly on C, D, E; every `y`
is of one of these types, and the types D or E, and A or B, both occur.

## 3. The abstract core is false (L2; UNVERIFIED hand example)

Drop the requirement that `a0, a1, b0, b1` are produced by the shape gates from wires of `Z`.
Take `z(a, b) = a ⊕ b` (4 gates). For ANY `f` and any functions `p`, `g` of `y` put
`a0 = f ∧ p`, `b0 = f ∧ ¬p`, `a1 = f ∨ g`, `b1 = f ∨ ¬g`. Then `a0 ≤ a1`, `b0 ≤ b1`,
`a0 ∧ b0 = 0`, `a1 ∨ b1 = 1`, `z(a0, b0) = f`, `z(a1, b1) = ¬f`. So the transition structure of
§2 alone bounds nothing: a proof must charge the gates of `Z` that compute `u1, h1, u2, h2`.
This is the same message as L1 from the other direction.

## 4. The output is not a shape gate (L4), and the first step of MONO (L5)

All of this section is UNVERIFIED (hand proof, written out in full).

**Semantic elimination, as used here.** If a circuit with `s` gates over inputs `(y, r)`
computes `K(r, y)` and `ρ` of its gates are redundant under `r := 0` (constant, or equal to an
earlier wire), then `K(0, ·)` has a circuit with `s - ρ` gates. This is the Lean lemma `se` of
`XorExtension.lean` (CHECKED there for the last input). A gate that reads a constant wire is
redundant.

**L5.** Frame A, and assume `z` is monotone increasing in `a`. Let `f(y) = 1`. Then
`z(a0, b0) = 1` and `z(a1, b1) = 0`; by monotonicity `z(a1, b0) = 1`; hence `b0 ≠ b1`, so
`u2 = 1` and `h2 = 0`. So `f ≤ u2 ∧ ¬h2`. Let `w(b, y) = z(u1(b, y), b, y)` (the gates `Z` with
the wire `H1` replaced by the wire `u1`; `m - 1` gates over the inputs `y, b`). If `h2 = 1`
then `f = 0`; if `h2 = 0` then `b0 = 0` and `f = w(0, y)`. Hence

    f = w(0, y) ∧ ¬h2.

The circuit `K = Z + NOT(h2) + AND` has `m + 1` gates over `(y, b)` and `K(0, ·) = f`. So in a
counterexample at most ONE gate of `K` is redundant under `b := 0`. (If `z` is decreasing in
`a`, the same argument gives `¬f ≤ u2 ∧ ¬h2`, `¬f = w'(1, y) ∧ u2` with
`w' = z(u1 ∨ h1, b, y)`, and at most one redundant gate under `b := 1`.)

**L4.** Suppose the output of a counterexample is `H1` (the case `H2` is dual). No gate reads
`H1` (it would be dead), so frame A holds, `z = a`, and every gate of `Z` is a function of
`(b, y)`: `f = u1(b0, y)`, `¬f = h1(b1, y) ∨ u1(b1, y)`.

Chain. Let `R_0 = H2`. Suppose gates `R_1, ..., R_j` of `Z` are given with
`R_i = OR(R_{i-1}, c_i)`, every `c_i` a function of `y` alone, and `R_i` the only reader of
`R_{i-1}` in `D` (`j = 0` is allowed). Put `r = R_j`, `W = c_1 ∨ ... ∨ c_j`, `r0 = W ∨ (u2 ∧ h2)`,
`r1 = W ∨ u2`. Every wire depends on `b` only through `r`; write `u1(r, y)`, `h1(r, y)`, and let
`Z_j = Z \ {R_1, ..., R_j}`, a circuit with `m - 1 - j` gates over `(y, r)`.

- Claim A: `f ≤ u2 ∧ ¬h2 ∧ ¬W`. If `f(y) = 1` then `u1(r0, y) = 1` and, since `¬f = 0`,
  `u1(r1, y) = 0`; so `r0 ≠ r1`, that is `r0 = 0`, `r1 = 1`.
- Claim B: `f = u1(0, y) ∧ ¬(h2 ∨ W)`. If `h2 ∨ W = 1` then `f = 0` by A; otherwise `r0 = 0`.
- Circuit `K_j`: `Z_j`, `j` OR gates for `h2 ∨ c_1 ∨ ... ∨ c_j`, one NOT, one AND: `m + 1`
  gates over `(y, r)`, `K_j(0, ·) = f`. So at most one gate of `Z_j` is redundant under `r := 0`.

The readers of `r` are gates of `Z_j`, or `G1` (when `h1 = r`), or `H1` (when `u1 = r`); there
is at least one (M1).

1. `u1 = r`: `f = r0`, but `f = 1` forces `r0 = 0` (Claim A). So `f = 0`. Contradiction.
2. Two gates of `Z_j` read `r`: two redundant gates. Contradiction.
3. No gate of `Z_j` reads `r`: only `G1` does, so `u1` does not depend on `r`, and `f = u1` is
   computed inside `Z`. Contradiction with `C(f) = m`.
4. Exactly one gate `R'` of `Z_j` reads `r`, and `R'` is `NOT r` or `AND(r, c)`. `R'` is
   constant under `r := 0`. A reader of `R'` in `Z_j` is a second redundant gate. If `u1 = R'`
   with `R' = AND(r, c)`: `u1(0, y) = 0`, so `f = 0` by Claim B. If `u1 = R' = NOT r`:
   `f = ¬r0`; `f = 1` gives `r1 = 1` (Claim A) and `f = 0` gives `r0 = 1`, so `r1 = 1`
   everywhere, and `¬f = h1(1, y)`: on side 1 the wire `h1` computes `¬f` with gates of `Z`
   only, so `C(¬f) ≤ m - 1`. Otherwise `G1` is the only reader of `R'`, `u1` does not depend on
   `r`, and case 3 applies. Contradiction in every sub-case.
5. Exactly one gate `R'` of `Z_j` reads `r`, and `R' = OR(r, c)`. Then `c` does not depend on
   `r` (a path from `r` to `c` would pass `R'`). If also `h1 = r`: write `u1 = ũ(r ∨ c, y)`;
   `f(y) = 1` gives `¬f = r1 ∨ ũ(r1 ∨ c) = 0`, so `r1 = 0`, hence `r0 = 0`, and
   `f = ũ(c) = ũ(r1 ∨ c) = 0`. So `f = 0`. Contradiction. With case 1, `R'` is the only reader of
   `r` in `D`, and the chain extends: `R_{j+1} = R'`, `c_{j+1} = c`.

The chain cannot extend forever. So no counterexample has output `H1`. ∎

How the argument looks on the smallest shape circuit (found by `enum_shape.py 3 7`, CHECKED by `ex7.py`: the
7-gate circuit `H2 = AND(y0, OR(y2, x))`, `n = NOT H2`, output
`OR(AND(y0, n), AND(x, OR(y2, n)))` computes `x ⊕ (y0 ∧ ¬y2)`): `u1(0, y) = y0`, `h2 = y2`,
`f = y0 ∧ ¬y2`, and all three gates of `Z` are redundant under `H2 := 0`. This circuit has
`min + 5` gates; the proof above shows that `min + 3` is impossible with this output gate.

**L6 (increasing case).** Frame A, `z` monotone increasing in `a`, output not `H1` (L4), so the
output is a gate of `Z`. Work in the *K-world*: the gates `Z` with the wire `H1` replaced by the
wire `u1` (acyclic, because `u1` is not downstream of `H1`). The chain is defined as in L4, with
two changes: `R_i` is the only reader of `R_{i-1}` AMONG THE GATES OF `Z` (readers `G1`, `H1` are
allowed), and `c_i` is the K-world function of the second input of `R_i`; the invariant adds
`u1 ≠ R_i` for `i < j`. `K_j` is `Z_j` over `(y, r)` with the wire `H1` replaced by `u1` (by the
input `r` when `u1 = R_j`), plus `j` OR gates, one NOT, one AND: `m + 1` gates.

- Claim A: `f ≤ u2 ∧ ¬h2 ∧ ¬W`. If `f(y) = 1`: `z(a0, b0) = 1`, `z(a1, b1) = 0`, and
  `z(a0, b1) ≤ z(a1, b1) = 0` by monotonicity. So with the wire `H1` held at the constant
  `a0(y)`, the output changes between `H2 = b0` and `H2 = b1`. With `H1` held constant, all
  influence of `H2` inside `Z` passes through the chain, so `R_j` changes: `b0 = 0`, `b1 = 1`
  and every `c_i` is 0 at `H1 = a0`, which is its side-0 value. In the K-world the `c_i` do not
  depend on `r` (they are upstream of `R_j`), so their K-world functions are the side-0 values.
- Claim B and the bound "at most one gate of `K_j` is redundant under `r := 0`" follow as in L4.

Let `Rd` be the gates of `Z_j` that read `r` in `K_j` (true readers of `R_j`, and readers of
`H1` when `u1 = R_j`).

1. `R_j` is the output: `f = r0`, against Claim A. `|Rd| ≥ 2`: two redundant gates.
2. `Rd` empty: the K-world output does not depend on `r`, so `f` is computed by `Z_j`
   (`m - 1 - j` gates). (If `u1 = R_j` and no gate of `Z` reads `H1`, then `H1` is the output:
   L4.)
3. `Rd = {R'}` and `R'` is constant under `r := 0` in the K-world (`NOT r`, `AND(r, c)`, or
   `OR(R_j, H1)` with `u1 = R_j`): a K-world reader of `R'` is a second redundant gate; if
   there is none and `R'` is not the output, case 2 applies; if `R'` is the output, then
   `f = 0` (AND, OR) or the output is a NOT gate, against N3.
4. `Rd = {R'}`, `R' = OR(r, c)` in the K-world, `c` not `r`. If `R'` does not truly read `R_j`
   (it reads `H1`, `u1 = R_j`): no gate of `Z` reads `R_j`, so with `H1` held constant the
   output does not depend on `H2`, against Claim A (`f = 0`). Otherwise `R'` truly reads `R_j`.
   If `u1 = R_j`: the readers of `H1` in `Z` lie in `Rd = {R'}`; none means output `H1` (L4);
   `R' = OR(R_j, H1)` is case 3. So `u1 ≠ R_j`, and the chain extends by `R_{j+1} = R'`.

The chain is finite. ∎ (UNVERIFIED.)

Decreasing case (sketch only, NOT written out): `¬f ≤ u2 ∧ ¬h2`, `¬f = w'(1, y) ∧ u2`, and the
chain consists of AND gates under `r := 1`; the gate `H1 = OR(h1, u1)` stays in the circuit, and
`h1` or `u1` may be chain gates. Not checked.

**Why this does not extend to the whole case.** L5 needs a monotone path structure from `H1` to
the output. In the 17-gate example of the earlier note both `H1` and `H2` enter XOR
sub-circuits, `z` is monotone in neither wire, and neither `f` nor `¬f` lies below `u2 ∧ ¬h2`.

## 5. Finite data (EVIDENCE)

`enum_shape.py k r [outH | outZ]` enumerates, by SAT with blocking, every non-constant `f` on `k`
variables (up to permuting variables and `f(y) ↦ f(¬y)`) such that `x ⊕ f` has a
residual-shape circuit with exactly `r` gates. Only the shape and "the output changes with `x`
at every `y`" are imposed (no minimality). It reports `r - min(C(f), C(¬f))` from the exact
size tables `sizes3.txt`, `sizes4.txt`. `outH`: the output gate is `H1` or `H2`; `outZ`: it is
not.

| `k` | `r` | restriction | classes of `f` | least `r - min` | log |
|---|---|---|---|---|---|
| 3 | 6 | none | 0 | none | `k3.log` |
| 3 | 7, 8, 9 | none | 2, 7, 17 | 5, 5, 5 | `k3.log` |
| 3 | 10 | none | NO RESULT (stopped at 700 s; 16 improving classes seen, least 5) | | `k3.log` |
| 3 | 7, 8, 9, 10 | `outH` | 2, 7, 17, 24 | 5, 5, 5, 5 | `k3outH.log` |
| 4 | 7, 8, 9 | `outH` | 2, 7, 24 | 5, 5, 5 | `k4outH.log` |
| 3 | 7, 8, 9 | `outZ` | 1, 5, 13 | 7, 6, 6 | `k3outZ.log` |
| 3 | 10 | `outZ` | NO RESULT (stopped at 660 s; least seen 6) | | `k3outZ.log` |

Readings (EVIDENCE only): L7 (`r ≥ min + 5`) holds on every completed row; the value `min + 5`
is attained only with output `H1` or `H2`; with the output inside `Z` the least value seen is
`min + 6` (L8). So the sub-case removed by L4 is the one in which the shape is cheapest.

`fixed4.py m part nparts`: for every class of `f` depending on 4 variables with
`C(f) = C(¬f) = m` (exact, `sizes4.txt`), SAT search for a residual-shape circuit with `m + 3`
gates for `x ⊕ f` that satisfies the necessary conditions M1, N1, N2, N3 (`cegar2.py`, flags
`ABCDEF`) and reads every `y`. Result for `m = 7` (65 classes): UNSAT for all 65 classes, 40 s to 190 s each: no counterexample with `m = 7` for `f` on 4 variables
(`fixed4-m7-part*.log`). This is conditional on the encoding and on the hand-derived residual
shape, as in the earlier note §3. `m = 8` on 4 variables (126 classes) was not run.

## 6. The single most promising unproved lemma

> **Lemma (UNPROVED).** Let `D` be a counterexample in frame A in which some path from `H1` to
> the output passes a NOT gate. Then `f` or `¬f` has a circuit with `m - 1` gates.

With L6 (UNVERIFIED) and duality this lemma implies the open case. Evidence: the SAT rows
of §5 and of the earlier note §3 (no counterexample found). What a proof has to do, by §2 and §3: use the table of the five
transition types (`z00 = f` on A, B, C; `z11 = ¬f` on C, D, E; each `z_ij` has at most
`|Z| - 1` gates) AND charge the gates that compute `u1, h1, u2, h2`; neither ingredient alone
suffices (L1, L2). The proof of L4 shows the mechanism in the one case where it is complete:
an inclusion `f ≤ u2 ∧ ¬h2 ∧ ¬W` lets the constant `0` replace the wire `H2`, which trades the
gate `AND(u2, h2)` for two gates and wins as soon as two gates of `Z` are redundant.

Suggested next steps: (1) referee L6 and write out its decreasing variant; (2) Lean-check §2
and L4 (this needs the residual shape in Lean first, which `count_main` does not export); (3) for the non-monotone
case, look for an inclusion that plays the role of Claim A, for example with the pair
`(z00, z11)` on the types C, D, E.
