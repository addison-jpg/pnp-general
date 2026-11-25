# Is a new "Lean 4 + Python flexibility" language necessary?

Date: 2026-11-24. Toolchain used for tests: Lean 4.36.0 + the project's pinned Mathlib, 4 cores, 15 GB RAM. Every claim is marked **[tested]** (run, files in this folder), **[read]** (source or web page read) or **[recalled]** (from memory, not re-verified). Author: coord-desktop's Fable agent; refereed summary by coord-desktop.

## Verdict
**No. A new language is not necessary, and building one would make the main pain point worse.** Lean 4 is already a compiled general-purpose language with Python-style imperative `do` code, arrays, hash maps, a verified union-find, C FFI and user-extensible syntax. Every listed pain point has an integrated fix inside Lean that costs days to weeks. A new language costs person-years and adds a second trusted semantics that the project's checker (standard axioms only) could not accept without a translation into Lean anyway.
- One Lean definition can serve `#eval`, compiled code and kernel proofs. A kernel-checked evaluator written for the kernel (truth table as one `Nat`) checks **1000 circuits with 9 inputs and 60 gates on all 512 inputs in 15.8 s**, axioms `[propext]` only. **[tested]**
- The naive version of the same check is 10x slower and runs out of memory at 1000 circuits. How the checker is written matters more than which language it is written in. **[tested]**
- `bv_decide` is **not usable** under the project rule: it adds a native axiom. Mathlib's `lrat_proof` **is** usable: it turns a CaDiCaL LRAT proof into a kernel proof with the three standard axioms. **[tested]**

## 1. State of the art
| Capability | Status | Mark |
|---|---|---|
| Compiled code, `IO`, `Array`, `ByteArray`, `UInt*`, `Std.HashMap/HashSet` | Mature. Toy enumeration (n=4): CPython 0.86 s / 3.53 s, compiled Lean 0.12 s / 1.17 s (3-7x faster, un-tuned). The interpreter took 3.9 s on the first case (slower than CPython). | tested |
| Imperative style: `do`, `let mut`, `for`, `while`, early `return` | Mature. Reads close to Python. | tested |
| Verified union-find | `Batteries.Data.UnionFind`, already a dependency. Used in `Dsl.lean`. | tested |
| Custom syntax / embedded DSL | Mature. A 25-line `circuit (x, y, z): a = x & y ...` block elaborates to the ordinary `Circuit` term, with 'unknown wire' errors at the right position. | tested |
| `decide`, `decide +kernel` | Mature. Kernel has GMP-backed `Nat` arithmetic and bit operations, so bit-parallel checks are fast; list-walking code is slow. | tested |
| `native_decide` / `Lean.ofReduceBool` | Fast but trusts the compiler. Forbidden by the project. | recalled |
| `bv_decide` | Verified bit-blasting + CaDiCaL + verified LRAT checker, but runs the checker as compiled code and records an axiom `thm._native.bv_decide.ax_1_5`; the project checker would reject it. | tested |
| Std's verified LRAT checker by kernel reduction | `decide +kernel` on `Reflect.verifyCert` gets stuck at the parser (built for compiled execution). Not practical. | tested |
| Mathlib `lrat_proof` / `from_lrat` | Builds a real proof term from CNF + LRAT. PHP(5,4), 55 LRAT lines: 0.66 s. PHP(8,7), 9865 lines: 42 s wall (30 s kernel). Axioms: propext, Classical.choice, Quot.sound. About 3-4 ms per LRAT line, so about 10^5 lines is the practical limit per theorem. | tested |
| CaDiCaL | Shipped inside the Lean toolchain (`bin/cadical`); emits LRAT with `--lrat --no-binary`. | tested |
| PBLean (pseudo-Boolean / VeriPB certificates in Lean 4, arXiv 2602.08692) | Exists; relevant to LP/price checks. Maturity not checked. | read (search result only) |
| C FFI (`@[extern]`, Lake `extern_lib`) | Works; officially unstable interface. | read |
| Python -> Lean drivers: LeanInteract, Pantograph, lean4-repl, LeanDojo | Process/REPL drivers (the 'wrapper' kind the owner excluded). LeanInteract lists support up to Lean v4.32.0-rc1. | read / recalled |
| In-process Lean <-> Python FFI | Nerodia (leanprover/nerodia): 'work-in-progress', 'very limited API', needs CPython 3.14. Others (lean.py, LeanPythonRaw, pylean4) experimental. | read / search only |
| Lean in Jupyter | lean4_jupyter kernel exists; niche. | recalled |

The project's `Defs/BinaryCircuit.lean` is already suitable except that `op : Bool → Bool → Bool` is a function field (cannot be compared, printed or serialized); a data twin with an opcode (`Fin 16`) and `toBinaryCircuit` solves that. **[read]**

## 2. Pain point -> cheapest integrated fix
| Pain point | Fix | Option |
|---|---|---|
| Lean and Python definitions of a class drift | The Lean `def` is the only definition; `Decidable`/`Bool`-valued, compiled; the enumerator calls it directly. | (i) |
| Circuit semantics implemented twice | One `Circuit` data type + `eval`; a fast bit-parallel `tt` proved equal to `eval` once. | (i) |
| Scratchpad-only data | Corpora as generated `.lean` data files (packed `Nat` per circuit) with a `checkAll ... = true := by decide +kernel` theorem each. | (i)+(iii) |
| Slow kernel checks of large finite facts | Kernel-friendly checkers: bit masks, closed forms, packed data, chunked theorems (~1000 circuits per file, parallel Lake build). | (iii) |
| UNSAT claims from pysat | Solver emits LRAT; `lrat_proof` imports it; plus a one-time proof that the CNF encodes 'no circuit of size s computes f'. | (iii) |
| SAT / witness claims | Keep explicit witness + decidable check (already works: 36 PureSDRs in about 40 s). | (iii) |
| Agents writing ad-hoc scripts | A small Lean library + `lake exe` entry points; optional surface syntax. | (i)+(ii) |
| LP / price checks | Export a rational dual certificate and check it with `decide`/`norm_num`; see PBLean. | (iii) |

| Option | Effort | Risk | Removes drift? |
|---|---|---|---|
| (i) Computation in Lean, one semantics | 1-2 weeks core; 3-6 weeks to port main drivers | Low-medium (more verbose than Python; solver stays external) | Yes |
| (ii) Python-flavoured syntax in Lean | 1-3 days for circuit literals | Low if kept to data literals; high if it grows into a general language | No (cosmetic) |
| (iii) Certificates with kernel-friendly checkers | 2-5 days; 1-2 weeks for the exact-synthesis CNF soundness proof | Medium (LRAT import tops out near 10^5 lines per theorem) | Yes, for data |
| (iv) New language | Person-years | Very high: new trusted base the checker cannot use; Mathlib re-binding; agents know Lean/Python, not it | No: adds a third definition |

Note on 'integration, not wrapper': a SAT solver is native code whatever the host; what makes the pipeline integrated is that the encoding and the certificate check live in Lean.

## 3. Recommendation
Build a small Lean library, not a language. Keep Python only for disposable exploration, with the rule that nothing from Python counts until a Lean theorem re-checks it.
Minimal first step (about one week):
1. `CircuitData`: gates with opcodes, `DecidableEq`, `Repr`, pack/unpack to a `Nat`, and `toBinaryCircuit` into the existing definition.
2. `tt : Nat → CircuitData → Nat`, bit-parallel, plus the one-time theorem `(tt n C).testBit r = C.eval (bits n r)`. Not attempted yet; the prototype only kernel-checks agreement on examples.
3. `checkAll` over a packed corpus with `by decide +kernel`; convert one existing corpus and one hand-matched class definition, delete the Python twin.
4. One UNSAT import: CaDiCaL LRAT for a small exact-synthesis instance through `lrat_proof`, to measure real proof sizes before committing to the encoding-soundness proof.
5. Optional: the `circuit (...)` literal syntax.

What would change the verdict: (a) real exact-synthesis UNSAT proofs far above 10^5 LRAT lines that cannot be split (then: one audited axiom, not a language); (b) 10^5-circuit corpora needing more than ~30 min of kernel time even when chunked (extrapolated from 16 ms/circuit); (c) a need for numpy-class numerics once Nerodia matures (then: an in-process bridge, still not a language).

## Limits
Random circuits, not the project's corpora; no real exact-synthesis LRAT sizes; the refinement and encoding-soundness proofs are estimated, not written; LeanDojo, lean4-repl and Jupyter maturity from memory. Anecdote: the first closed form for the input truth tables was wrong (it was the complement) and `decide +kernel` rejected it at once: the drift problem caught by the proposed mechanism.
