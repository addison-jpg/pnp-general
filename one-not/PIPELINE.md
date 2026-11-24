# Search and verification pipeline for L-meta-951 (`no_minCE`)

The owner's handoff framework, recorded 2026-11-24 as given. It governs how search code and Lean
divide the work on `no_minCE`. In this repository: search code and witness scripts live under
`one-not/tools/` and `one-not/work/`; the Lean project is `one-not/lean/`; heavy generated output goes under
an `artifacts/` directory, which git ignores. `native_decide` is not allowed in any row here, so
a witness check must go through the kernel (`decide` on a compact witness, or a structured proof).
The figures in section 3 (the size of the empirical suite, the numbers for `Config (I)`) are the
owner's summary and have not been re-run by the board integrator.

---

# HANDOFF TO CLAUDE/GEMINI FACILITATOR: L-META-951 (`no_minCE`) — PYTHON/C++ ↔ LEAN 4 PIPELINE

## 1. Execution Architecture: Python/C++ Search + Lean 4 Verification
- **Role Split:** Use Python (+ C++ where inner loops need speed) for all search, LP/dual exploration, counterexample hunting, potential-function testing, and graph/circuit enumeration. Use Lean 4 strictly to type-check theorems and compact certificates—never as an exploratory search loop.
- **Concrete Python ↔ C++ ↔ Lean Interfaces:**
  1. **Search & Optimization (Python + C++):** Write inner search/LP/graph loops in C++ exposed to Python via `nanobind` or `pybind11` (or a small CLI binary emitting JSON), paired with Python (`scipy.optimize.linprog`, `numpy`, `networkx`) for fast prototyping and LP dual inspection.
  2. **Lean State & Tactic Automation:** Use **Pantograph** (Lean 4 RPC server) or **LeanDojo-v2** tracing utilities when programmatically inspecting goals/tactics in the repo.
  3. **Certificate / Witness Handoff (Python → Lean):** Export minimal, deterministic JSON/Lean-literal witnesses (e.g., small dual multipliers, gadget indices, or certificate parameters) rather than dumping giant brute-force tables. In Lean, prefer small kernel-checkable checks (`decide` on compact witnesses) over `native_decide` to preserve `lean4checker` compatibility.

## 2. Private Repo Workflow & Verification Gate
- **Repo Hygiene:** Keep heavy generated traces/scratch outputs out of git history (via `.gitignore` or `artifacts/` scratch paths), while keeping clean, reproducible witness scripts and Lean modules organized.
- **Verification Bar:** `lake build` passes with zero `sorry` warnings, and `#print axioms ` confirms only standard intended axioms are used.

## 3. Core Mathematical Target & Baseline State
- **Goal:** Discharge `no_minCE` in `L-meta-951` (for sets S_1...S_m with |S_i| >= 2 and pairwise intersection <= 1, any AND/OR/NOT circuit with <= 1 NOT gate computing all ORs has >= sum(|S_i| - 1) gates), reduced to `hload` (`MergeFrac`).
- **Already Proved in Lean:** `small3_bound` (|S_i| <= 3, covering Fano, Pasch, sunflowers, triple systems) and two-world monotone sandwiching (non-DD cases). Empirical suite (~1.1M configs): 0 violations, min slack = 1.
- **Blocked Wall:** Local point-killing rules fail at 3rd+ merge for |S_i| >= 4. Key hard gadget: `Config (I)` (25 gates, fractional load 0.35 < 1).
- **Physics Notes Context:** CTCs (L-lib-061/062), low-degree quantum amplitudes (L-lib-065/076, deg <= 2T), and holographic complexity vs. natural proofs (L-lib-086) do not bypass classical complexity barriers; target a global combinatorial/LP/charge proof.

## 4. Immediate Swarm Tasks
- **Track A (Price Form / LP Dual):** Formulate `MergeFrac` constraints for `Config (I)` and near-tight gadgets in Python (`scipy.optimize.linprog`); inspect tight constraints and dual variables.
- **Track B (Double Counting) & Track C (Lifted y-Induction):** Simulate cross-world gate charging and candidate potential functions Phi over the virtual y-coordinate in Python across `Config (I)` before encoding lemmas in Lean.
- **Lean Landing Prep:** Keep `MergeFrac` / `hload` interfaces clean and ready to receive candidate lemma decompositions or compact witness checks once Python/C++ isolates the mechanism.
