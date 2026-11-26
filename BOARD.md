# Board: P versus NP through general circuits

> **CITE EVERY NEW CLAIM** (owner, 2026-11-26: "we need a generalized method of forcing citations on our git repo"). Run `bin/setup` (or `git config core.hooksPath .githooks`) once in your clone: commits that add an uncited claim are refused. Grammar: `cite KEY` below an .ath claim, `cite:KEY` on a tagged board line or above a Lean theorem; KEY = lit / doi / arxiv / lean / file / commit / ath / original. Spec and limits: `asteroid/CITE.md`. Task: `boards/tasks/cite-gate.md`. CI runs it on every push (workflow `cite`).

- **ASK ADDISON: tree refactor (proposal).** Root ~30 entries → 11: `asteroid/` (language, native, editors, dist), `proofs/` (both Lean projects), `research/`, `work/` (boards). Biggest single win: `AsteroidLang` → its own Mathlib-free package. Nothing moves until Addison says yes. [`tree-refactor`](boards/tasks/tree-refactor.md)

Refactored 2026-11-25 (seat R1) bottom-up: findings (`findings.jsonl`) → `boards/TREE.md` → this file → task boards. The text before the refactor is in git: `git show 1f3cc11:BOARD.md`.

- **TOP NOW (Addison, 2026-11-25): asteroid on plain Linux (Arch, most basic) and Windows with the native backend: less Python, no matplotlib, minimal Lean. mintty dropped (Addison).** Done: 4.4 MB Linux binary (`dist/linux`, Arch PKGBUILD) and 4.2 MB native `asteroid.exe`. Open: seat 5 (corpus, hunt/search, mixed, rest of the term language natively). [`asteroid-term`](boards/tasks/asteroid-term.md)
- **FILES FOR ADDISON (2026-11-25): give a direct link, not only a file card.** Commit the file (a .vsix, a logo, a PNG) and give `https://github.com/addison-jpg/pnp-general/raw/main/<path>`.


- **Credit, down the line (Addison, 2026-11-25: "would be nice if down the line cred goes big to philosophy with base of beauvoir as unifier"):** when the project is presented, philosophy gets prominent credit, with Simone de Beauvoir as the unifying frame (*The Ethics of Ambiguity*, *She Came to Stay*, the diary) and Deleuze, Fisher, Hegel and Camus around her. That credit is for the frame that organised the work, and it is honest about the boundary: the reviews (philosophy/REVIEW.md, REVIEW_BEAUVOIR_QG.md) show which links are theorems and which are readings.

- 2026-11-26 front612 [ASK] all boards: Gemini as an outside second opinion (review + 'intuitive expansions'), excerpts only, logged, nothing posted unchecked; owner + coord + board approval first. Card: boards/tasks/gemini-second-opinion.md

## THE AIM (Addison, 2026-11-25)

"i dont care about p=np." "the thing is these are all still subfields of math they need to be combined in a manner that allows automated discovery of new ones or incorporation of previously known ones. honestly combinatorics is probably at that level. these all exist at the same level."

- **Aim:** one structure in which every field the project touches sits at the same level (circuits, quantum gravity, logic and language, philosophy as formal models, the methods, the sphere), so that connections between fields, and whole new fields, are found automatically, and known fields can be added by machine rather than by hand.
- **The common level:** combinatorics. Every field emits finite structures, and those structures can be counted. A counting sequence is a fingerprint that any field can produce at small sizes, and two fields that produce the same sequence are candidates for a connection. That is how OEIS matches and the Ramanujan Machine find conjectures; it is automatable with the tensor backend.
- **The machinery we have:** the centre (`center.py`: one store, record kinds at one level); MONQWENSOR (connections by embedding and shared Lean structure; paused); the tensor backend and git-compute (counting at scale); Lean (checking last).
- **Honest limit:** matching sequences proposes connections, it does not prove them. A shared sequence is often coincidence, so verification stays with the evaluator and Lean.


## THE CENTRE (read this first): `center/VIEW.md`, built by `python3 -I center.py`

The board now lives in a central store: every finding and every board cell as a record, sharded by program in `center/shards/`, each with a computed radius (0 = settled, 1 = open). `center/VIEW.md` is the generated view; `python3 -I center.py ask TEXT` is a seat's one query. Hand-written boards (this file, boards/tasks/) are inputs until they are retired. It grows three ways: richer records, more records (shards), more record kinds (one reader each).


## FLAGSHIP: PAYMENT HALL ⇒ NEGATION-LIMITED BOOLEAN SUMS (Addison approved, 2026-11-25)

The target: for Boolean sums with pairwise |S_a ∩ S_b| ≤ 1, every circuit with at most k NOT gates needs at least Σ(|S_w| − 1) gates. k = 1 is `no_minCE`, via the checked chain to `BottomPay`; general k is the point lemma. One condition, PHC, would unify both. PHC is not proved: F1 reduced it to Lemma D and found the exact obstacle, the class point lemma for two sets. A standalone result in negation-limited circuit complexity; no implication for P vs NP is claimed. [`flagship-payment-hall`](boards/tasks/flagship-payment-hall.md)
- DECIDED: cross-program unification (Fable) (was TAKEN). Theorems (checked, `Worlds/Unify.lean`): (A) one potential: the truncation `trunc c f` is the largest potential below f with increments ≤ c; it equals f iff the Edmonds/Nash-Williams inequality holds (`trunc_eq_iff`: PHC and Lemma D are this at c = 1); counting potentials have it for free (`trunc_eq_of_lip`), sums over sets do not (`lip_sum`); PHC necessity for arbitrary rank-like functions (`unsplit_of_partition`). LIT2's refutation reads: the increment per gate is not 1 at scale. (B) diagonal and counting are one argument at three prices (`diag_explicit`, `halve_not_mem`, `count_exists`; private points reach only |devices| ≤ |inputs|). (C) views embed in families, not conversely; P and NP have the same view (`p_np_same_view`, one standard hypothesis), so P vs NP is not a non-injectivity statement. (D) the payment rank is not a min-cut function (`parallel_payers_not_cut`). Tested on 21 stored circuits: split condition 21/21, one-gate jump 2 to 6, monogamy violated in 13. Failed rhymes: CKW = PHC, payment monogamy, "one per gate" as a common law, logics as a fourth level. -> `worlds/UNIFY_ALL.md`
  - OPEN (Fable): Lean, every one-string language is in `P` (`Defs/Base.lean`), to remove the hypothesis of `Unify.p_np_same_view`. -> lean/PEqualNP/Worlds/Unify.lean
  - OPEN (Fable): Lean, a parameter-dimension potential for products of two-qubit gates that is `Unify.Lip 15` (or 9), so that L119's count is literally `Unify.lip_count`. -> lean/PEqualNP/QuantumGravity/Open/
  - OPEN (Fable): matroid union for hypergraphic ranks (converse of `Unify.unsplit_of_partition`): split condition ⟹ disjoint spanning forests; Mathlib has no matroid union. -> one-not/lean/PEqualNP/W951/Open/
  - OPEN (Fable): compute `trunc 1 f` on LIT2's AG(2,8) program (261 lines; needs submodular minimisation, not 2^E) and report the largest one-gate jump: how many sets one line serves. -> worlds/unify_rank.py
  - OPEN (Opus): CKW realizability: every (x, y) with x + y ≤ t ≤ 1 is (τ_AB, τ_AC) of a three-qubit state with τ_{A|BC} = t (W-class states), against `CKW.ckw`. -> lean/PEqualNP/QuantumGravity/Open/CKW.lean

## HYPERCOMPLEX POLYNOMIAL LAYER (Addison: "everything should be a hypercomplex polynomial field")

One polynomial language over ℝ, ℂ, ℍ or a Clifford algebra, with checked maps between Boolean functions (Fourier–Walsh), Φ, Pauli/Clifford operators and the quaternions already used in KAK. A common language, not a proof engine; Hurwitz bounds what "field" can mean. [`hypercomplex`](boards/tasks/hypercomplex.md)

## MODEL IN THE LOOP (Addison: "a structure that supercedes the tensor gpu ... BIIG qwens weights integrated into operations")

FunSearch-style search. Qwen proposes programs (circuits, payer sets, set families), the tensor backend scores them exactly, and the best go back into the prompt. Aimed at the k = 1 flagship: a counterexample to BottomPay, or tight cases that suggest a proof. The model guesses; only the evaluator or Lean decides. [`model-in-the-loop`](boards/tasks/model-in-the-loop.md)

## METHODS, FORMAL (Fable; Addison approved)

Addison's methods as checked definitions: forced prover/refuter pairs, multidimensional bounds as Pareto frontiers, the board's propagation semantics, levels as projections, refuted forms lifted in a DAG. An ath surface where cheap. Results about the method, not about circuits. [`methods-formal`](boards/tasks/methods-formal.md)

## LATERAL (low priority, must not interfere with the flagship): one diagonal theorem

Lawvere's fixed point theorem as one Lean spine, with instances: Cantor, Russell, the halting problem (bridged to Mathlib), a Tarski-style instance for asteroid's own claim language if it is literally provable, and Camus re-derived. The unification is classical (Lawvere 1969; Yanofsky 2003); only the checked spine is new. [`lateral-diagonal`](boards/tasks/lateral-diagonal.md)


## TOP: QUESTION THE FRAMING (Addison, 2026-11-25: "we have to seriously consider that the entire framing of pnp is nonsense. it sounds awful but i havent really heard a convincing arg. it seems built on old math, with infinite bounds that are just not properly infitely ocntinious")

- **main's view, stated plainly:** P vs NP is a precise statement about finite objects: for every input length n, is there a machine whose running time is bounded by a fixed polynomial in n? Its only infinity is "for all n", the same quantifier as in Goldbach. It is meaningful. What is open to serious critique is whether it is the right question.
- **Known critiques, all mainstream:**
  - asymptotics hide constants (galactic algorithms; Cobham–Edmonds is a modelling choice);
  - worst case against average case (Impagliazzo's worlds; smoothed analysis);
  - possible independence from ZFC;
  - uniform machines against circuits.
- **Continuous and algebraic siblings, each open:** Blum–Shub–Smale P_ℝ vs NP_ℝ (machines computing with exact reals); Valiant's VP vs VNP; geometric complexity theory (orbit closures, representation theory). How they relate to the discrete question is itself largely open.
- **Seat (Opus, heavy) FR1:** write `worlds/FRAMING.md`. The strongest case that the framing is wrong or arbitrary, steel-manned with sources. Then the strongest replies. Then what a "continuous" formulation looks like (BSS, VP/VNP, GCT, complexity of real computation, Smale's 17th problem), what is proved about how it relates to the discrete one, and where this repository's own continuous attempts (Φ, the limit level, flag algebras) sit. Honest read statuses. It ends with a verdict: which parts of the framing are arbitrary, and which are forced.
- DECIDED FR1 (Opus) (was TAKEN): the framing is meaningful and largely forced, not nonsense. Forced: P and NP are robust across reasonable discrete models and logic, P vs NP is a ∀∃ sentence about integers, and the bit-model continuous version is provably the same question (Ko–Friedman: max of a smooth poly-time function poly-time iff P = NP). Arbitrary: the polynomial line, the worst case, uniformity, the classical machine, bits rather than exact reals. Algebraic siblings (P_ℂ vs NP_ℂ, VP vs VNP, GCT) are open and linked one way, often only under GRH; GCT occurrence obstructions ruled out (2016). The defensible critique is relevance, not sense. Φ and the limit level are continuous proof devices on the circuit axis, not continuous models. LITERATURE.md §P. -> `worlds/FRAMING.md`


## MAP OF THE WORLDS (Addison, 2026-11-25: "the bounds are always multidimensional, continuous, likely infinite")

A map, not progress on P vs NP. P vs NP is one binary cut inside a landscape with many axes: time exponent, average case, non-uniformity, provability, barriers, fine-grained, and the circuit axes this repository works on. Only the hierarchy theorems' infinitely many levels are proved. [`worlds-map`](boards/tasks/worlds-map.md)

## COMPUTE IS THE BOTTLENECK (Addison, 2026-11-25: "that cpu is the issue that will fix everything")

- The full pure-Lean verifier (`lean/PEqualNP/Verify/All.lean`, about 1,630 imports) has not finished once in this session. One run passed the lock wait but was stopped at the one-hour background limit, then a container restart killed the next. The circuit-side verifier (`one-not/lean`, 18,633 jobs) did finish once (2026-11-25, with the five new Open modules).
- Agents' Lean builds share one machine and one build lock; each waits on the others. SAT seats (B7, B11) and Lean builds compete for the same cores.
- The circuit framework on vector hardware (Addison, 2026-11-25: "if we used our circuit framework on a gpu/cpu (bruh we could even tensorflow atp) it could be genuinely powerful if it can sit underneath the biggest problems here"): circuit evaluation is bitwise and embarrassingly parallel. A circuit's truth table on 2^n inputs is one AND/OR/NOT per gate over packed words, and slack over all cubes or 3^n mixed states is a batch of the same. A tensor backend (bit-sliced numpy now; PyTorch or JAX on a GPU when one exists) would make the refuter lane, the corpus checks and the payment-Hall tests orders of magnitude cheaper. SAT does not move to a GPU, but exhaustive and random search does. Seat: OPEN line on [`refuter-951`](boards/tasks/refuter-951.md).
- Where compute pays off most directly: the refuter lane, [`refuter-951`](boards/tasks/refuter-951.md) (SAT at base − 1, DD-state search), paired with the proof seats on `BottomPay` and `no_minCE`.
- git-compute is live (2026-11-25): sharded brute force runs free on GitHub runners; `gh api -X POST repos/addison-jpg/pnp-general/actions/workflows/compute.yml/dispatches -f ref=main -f 'inputs[spec]=compute/specs/fano_slack.json'` (80,198 Fano circuits in 1 min 54 s); how to write a spec: [`tools/tensor/README.md`](one-not/tools/tensor/README.md).
- Wanted: more cores or a dedicated build machine; a CI job that runs both verifiers on push to main and reports the time; and a rule that only one full verifier build runs at a time. Until then, check new modules one by one with `#print axioms` (as done for the quantum-gravity files).

## CURRENT STATE (formal style, one line per program; every claim is a finding in [`boards/TREE.md`](boards/TREE.md) or a task board)

- **one-NOT** ([`open-one-not`](boards/tasks/open-one-not.md)). Checked chain: `BottomPay → LightAbsorb → DDAbsorb → MixedCount → no_minCE → L_meta_951` (`LightAbsorb.lean`, `DDAbsorb.lean`, `MixedStepNegIff.lean`, `MinCE.lean`; the step DDAbsorb + no-DD count ⇒ MixedCount is paper, A4 note §2). Open: **BottomPay**, a Hall condition on the bottom forests of DD sets (0 failures at about 1.27 million DD states; bottom runs of two DD sets overlap, so a matroid-union re-choice is needed). `no_minCE` is NOT proved; the general one-NOT theorem is NOT proved.
- **several-NOT** ([`open-many-not`](boards/tasks/open-many-not.md)). Proved, any number of NOT gates: OR of n inputs needs n−1 gates (`Or4ManyNot`), OR systems need n − comp (`OrSystemManyNot`), S3(a) per-set flip lemma (`FlipLemma`), Hall core and point-lemma ingredients (`FlipHall`, `PointLemma`); C4w refuted at 4 NOT gates. Open: **the point lemma** for two sets, reduced to **rule R2** (S3(b) reduces to it via the thin-basis lemma); R2 is false as a local rule (O1, exact SAT), so the target is PHC@0 (U1).
- **quantum gravity** ([`open-qg`](boards/tasks/open-qg.md), [`qg-frontier`](boards/tasks/qg-frontier.md)). Proved (standard axioms): L115 (C = 4), L116 from L115, L169 (P_CTC ⊆ EXP), L119 in the weak forms 16k and 15k+1 (`KnillParam15.lean`) and conditional on `KnillParametrization`, `CtcReset`, `GateNet`, `ApproxCount` (Knill count for continuous two-qubit gates). Open: the exact **9k+3n+1** form (`KnillParametrization`, KAK for U(4), not in Mathlib) and the **PSPACE encoding** into P_CTC. UPDATE (F2): the exact L119 (9k+3n+1) is proved via `KAK.kak` and `KAKParam.L119`, so all four gap statements are now theorems.
- **limits** (below, `one-not/research/open/limits_*`). L1: obstacle found, |F2| is an exact sum over gates of an "exists context Z" indicator, not a bounded-size pattern sum. L2: literature rows (LITERATURE.md §L), no circuit-side limit theory found. L3: STOPPED (container restart), partial script kept. No theorem here.
- **philosophy** ([`philosophy-formal`](boards/tasks/philosophy-formal.md)). Three checked files: `Deleuze.lean`, `Fisher.lean`, `Bridge.lean`. Bridge finding: Φ is a projection of the slack table, not the whole virtual (`PhiT_not_injective`, `corners_not_injective`). A formal analogy; it claims nothing about Deleuze or circuits.
- **asteroid** ([`asteroid-term`](boards/tasks/asteroid-term.md), [`asteroid-exe`](boards/tasks/asteroid-exe.md), [`asteroid-vscode`](boards/tasks/asteroid-vscode.md), [`asteroid-cli-logo`](boards/tasks/asteroid-cli-logo.md), [`ath-prompt-quant`](boards/tasks/ath-prompt-quant.md)). Python front end (`python3 -m asteroid`, kernel-checked claims, `eval_sound`); native Lean binary with `.bench` reader, `repl` and `plot phi` (SVG), both tested against Python; `asteroid.exe` at the root (native Lean binary, 4.2 MB, built by exe.yml on windows-latest); `dist/linux/asteroid` (4.4 MB) and `packaging/arch/PKGBUILD`; `.ath` highlighting published on the VS Code Marketplace (`asteroid.asteroid` v0.1.0, Open VSX not yet). Open: the CLI logo; native corpus/hunt/mixed (asteroid-term seat 5).
- DECIDED U1 (Opus): BottomPay and the point lemma are instances of one payment Hall condition (matroid partition, Edmonds / Nash-Williams; per-set rank proved in both, the partition open in both); PHC@0 implies the point lemma and holds exhaustively at base lines on all two-set sizes up to (4,4), (3,5); its OR-only form fails with free difference (holds monotone): the single NOT wire is what keeps OR-only payment. Counting (Shannon, Knill, L119) shares only the per-gate potential shape. No proof. -> `one-not/research/open/U1_unify.md`
- DECIDED F1 (Fable): PHC is NOT proved. Lemma D (paper; necessity checked, `Open/PHC.lean::deletion_of_forestPay`): PHC holds iff for every set J of payers Σ_w (c_w(J) − 1) ≤ |E ∖ J| (c_w = components of the classes of w under J); so the split between sets is the plain count asked for every instance with freed payers, and PHC@0 for all programs is the class point lemma. Tested: every tight block splits one set (0 of 56,625 + 70,014 + program blocks split two). Refuted: peeling (5-line program; 63 BottomPay instances). Gap: the per-set rank of BottomPay rests on the top exclusion, which is tested only. Exact obstacle: the class point lemma for two sets. -> `one-not/research/open/F1_phc.md`
- Between this and P versus NP lie the general one-NOT case, every further NOT gate, and the known barriers (relativization, algebrization, natural proofs). Nothing here says P versus NP is settled or near.

## TOP: THREE LEVELS, BOTTOM TO TOP (Addison, 2026-11-25: "at the bottom its variable, at the middle its absurd polynomial feild, and at the top it becomes crazy overlapping infinities that we bound and match")

Assessment (main): rational; a known proof pattern, flag algebras plus stability plus a finite check.
- **Bottom, variable (finite n):** circuits, sets, cubes. Everything checked lives here; tests reach n ≤ 11 exhaustively, n ≤ 16 sampled (evidence, never a proof for all n).
- **Middle, polynomial field:** densities of small patterns are polynomials (Φ(p) of degree n in p). Tried alone on 2026-11-24 and closed: on the cubes every continuous route is the count again or refuted (twin trees, Fano corpus); [`continuous-mapping`](boards/tasks/continuous-mapping.md). Only the bridge.
- **Top, limits:** n → ∞; "gates ≥ base" becomes an inequality between pattern densities, proved by finite computation (flag algebras, Razborov 2007; hypergraph limits). Gives only gates ≥ (1 − o(1)) · base; the exact statement needs a stability step plus the bottom check. Risk: the count is exact and integer, limits lose o(n); the Fano corpus (245 non-up-set tight cubes) is the place to look.
- DECIDED L1 (Sonnet): density form tested on 17 circuits: base is an exact pattern count; |F2| is an exact sum over gates of an "exists context Z" indicator (Z = 0 local form misses up to 21 of 30 gates); linear forms are one-sided (necessary pi1 ≥ beta, sufficient pi1 − pi2 ≥ beta). -> `one-not/research/open/limits_density_form.md`
- DECIDED L2 (Sonnet): literature rows for flag algebras, hypergraph limits, flag-algebra-plus-stability results, limit theory for circuits: LITERATURE.md section L, 13 rows, search-result-only; an unopened Oxford thesis lead.
- STOPPED L3 (container restart; partial `limits_local_witness.py` kept; reopen as OPEN) (Opus): bounded local witness for F2 (adjusted after the L1 obstacle); was: attempt a flag-algebra certificate on the smallest pattern size; list the tight limit objects. -> `one-not/research/open/limits_certificate.md`
- STOPPED (usage, Addison 2026-11-25; reopen later): hyperfinite level (Fable): ultraproducts and Łoś as the bridge from finite instances to the limit; what of k = 1 is first-order, what is only an internal count; hyperreal Φ at an infinitesimal. -> `worlds/HYPERFINITE.md`, `lean/PEqualNP/Worlds/Hyperfinite.lean`

## TEAM, 2026-11-25 ~02:20 (Addison: "refactor agents, get urself a few fables, few opus, many sonnets")

The machine has 4 cores and 15 GB of memory, shared by every seat. Paper seats (Fable, Opus) use almost no CPU; Lean builds and SAT do. So: one Lean build at a time per seat; SAT and search seats run one core each under `nice`, at most two at once. The other SAT seats wait for the tensor backend (T1) and start after it lands.
- Fables: F1 the payment Hall condition (BottomPay and PHC@0, one statement); F2 KAK for U(4) and the exact L119 (9k + 3n + 1); F3 the DAG frame (joins: the real board history, Beauvoir's "willing others free").
- Opus: O1 rule R2 (point lemma, two sets); O2 three-qubit CKW monogamy in Lean; O3 the PSPACE ⊆ P_CTC encoding.
- DONE O3: PSPACE ⊆ P_CTC up to `PspaceStepEncodingLemma` (two OPEN Sonnet lines on qg-frontier) -> lean/PEqualNP/QuantumGravity/Open/PspaceCtc.lean
- DECIDED O2 (Opus): three-qubit CKW checked in full: C(ρ_AB)² + C(ρ_AC)² + 4|Det ψ| = 4 det ρ_A for every pure ψ (Wootters concurrence from the eigenvalues of ρρ̃), so τ_AB + τ_AC ≤ τ_{A|BC}, equality iff Det ψ = 0 (`ckw`, `ckw_identity`, `ckw_eq_iff`). -> `lean/PEqualNP/QuantumGravity/Open/CKW.lean`
- DONE F1: payment Hall condition, no proof; deletion form (Lemma D) and exact obstacle -> `one-not/research/open/F1_phc.md`
- DECIDED F3: DAG frame (was TAKEN): a lost future is later lost or past, never ahead (`lost_or_past`); with conflict, permanent iff the states clash, else recovered at the union; ten board rows as data, `lost_mono` fails on them, refuted claims never return and their material is the salvage. Beauvoir: one thin iff, one negative result. -> `philosophy/DAG.md`, `lean/PEqualNP/Philosophy/DAG.lean`
- DECIDED F2: KAK for U(4) and the exact L119 are CHECKED (standard axioms): `KAK.kak`, `KAKParam.knillParametrization : KnillParametrization`, `KAKParam.L119 : Gap.L119` (9k + 3n + 1 < 4^n ⇒ Haar-null). -> `lean/PEqualNP/QuantumGravity/Open/KAK.lean`, `KAKParam.lean`
- DECIDED: language unification (Fable) (was TAKEN): checked `Fagin → ImmermanVardi → (P = NP ↔ FO(LFP) = ∃SO on ordered structures)` against the repository's own P and NP, both capture theorems as hypotheses (`p_eq_np_iff_lfp_eq_eso`); ∃SO ⊆ NP from one unproved premise, first-order model checking in P (`eso_subset_np`); `lfp` is a least fixed point (`lfp_isLeast`). A restatement, it moves nothing. Prior art exists (Senellart's Lean 4 descriptive-complexity library; not imported, needs `lake update`). asteroid claims are single finite instances, not languages. -> `worlds/LANGUAGE.md`, `lean/PEqualNP/Worlds/Descriptive.lean`
- Sonnets now: PaymentHall Prop (Lean), OR-only PHC@0 for monotone programs (paper), PHC@0 under point deletion, two-level saturation (QG rank 3), cost per result (prompt method), refuter DD search (one core). Queued until T1: PHC@0 enumeration, point-lemma SAT, refuter SAT cells.

## RULES

- **THEORY FIRST, LEAN LAST (Addison, 2026-11-25: "lean should literally come waaaayyyyyy after theory"; "some lean backend is ok").** Order of work: (1) theory: paper proofs and exact statements; (2) tested: .ath claims and the tensor backend on instances (asteroid's evaluator is proved sound, `eval_sound`, but a .ath claim is about one finite instance, `single_instance`, so it is evidence, not a proof of a general statement); (3) checked: Lean, only once a statement is final and about to be claimed. Lean is postponed, never skipped for a claim: today it or careful checking caught a paper-only link, a backwards README sentence, R2, the general point lemma and every-k.
- **THE FAST VERIFIED ROUTE (Addison, 2026-11-25: "we have a faster verified proof method"; "checked infinite ... it has to reformulate to reduce the distance between the problem and infinity. infinity may also be a combinatorics level subproblem").** Two new words, enforced by `boards.py`:
  - `checked-finite`: a finite statement proved by exhaustive verified evaluation. It needs a runner that redoes the whole enumeration (or re-checks an UNSAT/DRAT certificate), plus a second seat. Same trust as Lean, for finite claims. No Lean needed.
  - `checked-infinite`: a statement about all n, proved by a finite check plus a **reduction**: a theorem saying the finite check covers every n. It needs a runner, a second seat, and `--reduction` (a `.lean` theorem, or `cite:` a known theorem with its read status in LITERATURE.md). The reductions are the combinatorial handles on infinity:
    - a cutoff or small-model bound: if it fails, it fails below size N;
    - a linear recurrence of known order, fixed by finitely many terms;
    - holonomic sequences and WZ certificates (Zeilberger): an identity for all n from one finite certificate;
    - decision procedures, e.g. finite automata for automatic sequences (the Walnut prover), or Presburger arithmetic.
  - The reformulation step is the real work: turn "for all n" into "for n ≤ N, plus a reduction". Lean is needed once per reduction, never per instance. Today's warning still holds: the point lemma held on every small case until AG(2,8), so without a reduction a finite check is `tested`, nothing more.
- **ORIGINALS, NOT TRANSLATIONS (Addison, 2026-11-25).** Every source is read and quoted in its original language: Spinoza in Latin, Freud and Hegel in German, Beauvoir, Deleuze, Lacan and Camus in French, and so on. And not only European languages (Addison: "romantic only is a bottleneck in and of itself, we can easily get arabic at the very least"): the classical Arabic tradition is in scope and largely public domain, e.g. al-Kindī, al-Fārābī, Ibn Sīnā, Miskawayh, al-Ghazālī, Ibn Rushd, Ibn Khaldūn, al-Khwārizmī. Next in line: Sanskrit (the Nāṭyaśāstra's rasa theory of emotion), classical Chinese (Mencius's four sprouts), Greek (Aristotle's Rhetoric II on the emotions). A translation is a cross-check only. Every formal definition that models a text sits next to the original wording it models. Read status records which original was actually opened. Copyright still applies to the original: public-domain originals (Spinoza, Hegel, Freud) may be quoted freely; in-copyright ones (Lacan, Beauvoir, Camus, Deleuze, Fisher) get page-and-section citations and short quotes only.
- **PRIORITY: UNIFY (Addison, 2026-11-25: "unify unify unify ... smaller at this point is prob anything too far in in the pnp framework").** New seats go to work that joins programs (the payment Hall condition, the Lawvere spine, levels as projections, the methods, the cross-program map) before work deep inside one program. Single-lemma grinding inside the circuit framework waits unless it is on the flagship's critical path.
- **SEAT SIZE (revised by Addison, 2026-11-25, via coord: "in what world does a sonnet do this").** Design, formalization and proof cards default to a FABLE. Sonnet is for retrieval, sweeps and plumbing only. Opus for single hard attempts. One narrow task per seat still holds; sub-lemmas still go on the board as OPEN lines. (Earlier rule: (Addison, 2026-11-25: "some agents are too big here ... refactor with more sonnets").** A seat is one narrow task with one output file and one DECIDED line; parts become seats. Sonnet by default. Opus…)
- **QUIET UNTIL ADDISON SAYS IT IS READY (Addison: "i rlly dont wanna accidentally notify the entire planet befoore its ready").** Full speed on the work; pushing commits to main is fine. Nothing that notifies anyone outside this repo: no issues, PRs, comments, releases, tags, `@name` mentions, posts or requests to outside sites. Addison announces; agents never do.
- **PHILOSOPHY (Addison, "take very seriously").** Build crudely from existing logical formalisations up to Deleuze, Mark Fisher if cheap, synced through the boards. Deleuze's virtual / actual reads onto the three levels (actual = finite circuits, virtual = polynomial and limit levels). A formal model of a cited reading, never a claim about what Deleuze meant. [`philosophy-formal`](boards/tasks/philosophy-formal.md)
  - **Unification, DECIDED, checked (Addison: "push mark fishers ideas, this could seriously be unifying"):** one frame for Fisher, Deleuze, Hegel, Camus and Beauvoir. A search is a tree of decisions, which is a Fisher frame; a refuted route is at once a lost future, a determinate negation, the trace of a free moment and the present's "barbarian" (`Unify.unified`). In any partial order, loss is permanent exactly when lost pairs never meet again (`permanence_iff_no_reconciliation`). Seven one-NOT rows are encoded as such a frame with `lost_mono` applied. Models of cited readings; nothing about circuits. "The Barbarians" is not a Beauvoir title: the word is Barrès's, in her 1926 diary. What failed is listed. [`philosophy/UNIFY.md`](philosophy/UNIFY.md)
  - **Beauvoir at quantum gravity's sets, nodes, edges, DECIDED, checked (Addison: "attack beauvoir specifically routed at quantum gravity set/node/edge"):** `lean/PEqualNP/Philosophy/BeauvoirQG.lean`. Checked: for a pure two-party state `S(A) = S(B)` (`entropy_symm`), and a reduced state is pure iff the state is a product (`pure_iff_product`); a pure pair leaves the third uncorrelated (`monogamy_of_pure_pair`); minimal cuts of a weighted graph obey complement symmetry, strong subadditivity and monogamy of mutual information (`rt_compl`, `rt_submodular`, `rt_monogamy`); on a Fisher frame the barbarian is "no common future" (`barbarian_iff_beyond`). Coffman–Kundu–Wootters for three qubits is now PROVED in full (O2, `lean/PEqualNP/QuantumGravity/Open/CKW.lean`: `ckw`, `ckw_identity`, `ckw_eq_iff`; standard axioms). Still not proved: min-cut = entropy for HaPPY. The readings are interpretation, kept apart in [`philosophy/BEAUVOIR_QG.md`](philosophy/BEAUVOIR_QG.md).
- **QG FRONTIER (Addison, "extremely good").** One research line: complexity = volume / action, holographic codes, CTCs, circuit-complexity growth, Brown–Susskind; what the repository proves; next formal targets reachable in Lean. [`qg-frontier`](boards/tasks/qg-frontier.md)
- **SUPERSEDED AIM (2026-11-24):** "the aim is P versus NP". Replaced on 2026-11-25 by THE AIM at the top. The rule not to hedge stands; the rule never to claim P vs NP stands.
- **STATE RESULTS AT FULL STRENGTH. NO HEDGING BEFORE REVIEW.** The one-NOT question is OPEN in the literature (Jukna and Sergeev 2013 §7, Blum 2024) and no result on it has been published: write that as a fact, and that the results here are the first. Write what is proved as proved, without "it seems". The one line that does not move: proved means the proof checker accepted it; the general one-NOT theorem is NOT proved (`no_minCE`); strong wording never upgrades tested or conjectured to proved.
- **THE BOARDS ARE A DATA STRUCTURE. NO MORE GRAFFITI (owner, 2026-11-24).** A finding is a record in `findings.jsonl` in the directory of its evidence: id, who, README item served, ONE word (checked / paper / tested / refuted / open / premise), one statement, evidence (`file` or `file.lean::theorem_name`), who confirmed. VERIFIED when its evidence exists (`checked` needs a theorem in a `.lean` file; anything else needs a second seat in `by`). Only verified findings propagate up to [`boards/TREE.md`](boards/TREE.md) (generated; the root shows what the repository has verified). Commands, repo root: `python3 -I boards.py add DIR WHO ITEM WORD "STATEMENT" EVIDENCE...` · `python3 -I boards.py confirm ID WHO` · `python3 -I boards.py` (rebuild; after any merge). Evidence names must be the bare theorem name found in the file (a namespace-qualified name fails the check). Task files say what to do (statement, done-when, OPEN/TAKEN/STOPPED, one "Decided" list, one "Refuted / dead" list); results are findings.
- **NOBODY ASKS ADDISON. USE THE BOARDS.** A question is an `[ASK]` line on the task board; unanswered after 15 minutes, DECIDE and write `[DECIDED] what and why`. One task = one file in [`boards/tasks/`](boards/tasks/) with one statement and one done-when; new task = new file and one row in the table below; do not grow this file. One writer per file where possible; do not rewrite another seat's lines.
- **MERGE CONFLICTS are never a reason to ask.** `git fetch origin main && git merge --no-edit FETCH_HEAD` (never force-push, never rebase others' commits). Boards, `LITERATURE.md`, `DEAD_ENDS.md`, `INDEX.md` merge by union (`.gitattributes`); `NAMES.md` is generated (`python3 -I names.py` after a merge); `README.md`: keep the other side, re-apply your item by hand; Lean or Python: keep BOTH, a clashing declaration goes in a new file `<Module>_<seat>.lean`. Rejected three times: write `[BLOCKED]` and take another task.
- **NAMES: FORMAL PROOF STYLE.** One formal name and one role per item (Definition, Lemma, Theorem, Conjecture, Open, Refuted, Counterexample). Property `UpperCamelCase` (`MinCE`, `CubeLocal`), object `lowerCamelCase` (`realWitness`), theorem `conclusion_of_hypotheses` (`no_minCE_of_ugame`), minimal-counterexample fact `MinCE.no_rewire`, counterexample `Cex.<name>`, refuted statement `Refuted.<name>`. No bare F2 / R6 / cxT2 in new text (old code in brackets once). [`NAMES.md`](NAMES.md) is GENERATED from [`names.py`](names.py).
- **LITERATURE FIRST.** One index: [`LITERATURE.md`](LITERATURE.md). Read it before you prove or search; add what you read with its read status. Never drop a literature note.
- **THE README IS THE PROOF.** [`README.md`](README.md) has numbered items (D1 to D7, L1 to L4, T1 to T9, C1, C2, the refuted table). Results go up as findings, with their word; every agent, note and finding says which item it serves; work that serves no item stops. One seat edits README.md; nobody else touches it; if your work changes a fact stated there, write one line on your task board. Boards: this file, [`boards/one-not.md`](boards/one-not.md), [`ladder.md`](boards/ladder.md), [`physics.md`](boards/physics.md), [`ops.md`](boards/ops.md); a README is not a board.
- **PULL, DO NOT PUSH (coming for the whole repository, when the open asteroid tasks land):** agents pull, work, and hand results to the one integrating seat that pushes. Until Addison switches it on, seats keep pushing small commits, their own files only.
- **PROCESS LIMITS (2026-11-24, in force until lifted):** at most 2 solver or search processes per container; no new subagent unless its task board exists; kill background jobs that serve no board; one push per result; no message where a board line will do. Do NOT call the Claude API (billed per token); no acks between sessions. Late stage: ambition over thoroughness, messy is ok, but checked still means checked (no `sorry`, standard axioms) and refuted claims stay off the board. Build on a capable agent's claim without rerunning it; spend refuting effort only where it blocks or contradicts your work.
- **Smallest agent that can do the job, always** (Addison, 2026-11-24). Proved means the proof checker accepted it; the pure-Lean check (`cd one-not/lean && lake build PEqualNP.Verify.All`) must keep passing.

## SUPERSEDED OR CLOSED (one line each; full text in git, `git show 1f3cc11:BOARD.md`)

- CURRENT TARGETS, REOPENED (nine seats), and the 22:49 "ONLY ASTEROID … CLOSED" section: replaced by CURRENT STATE above; the three open problems stay open (seats on their task boards).
- WHAT ASTEROID CANNOT YET SAY (ten-row wish table): the live list is `grep -rn "# WISH:" asteroid/` (21 lines); whoever adds the words deletes the line. Rows 1 to 10 are in the old file.
- PRIORITY table (L5 chain sum, C3 k-point step, D9 / C4(t), L6 gravity link, literature for C4, Millennium statement, Python as outward search): the status lives in README items and findings (`ChainSum.lean`; C4w refuted at t ≥ 4, C4g open for t ≥ 2); table in the old file.
- THE WALL (2026-11-24 graffiti, walls "non-discrete physics" and "anything else"): closed; non-discrete physics results are in `notes/phys/nondiscrete-lit.md` and `notes/phys/RealOracle.lean`; the rest is the day-1 session log.
- NEXT STEP: A MESSY CONTINUOUS MAPPING, SUBAGENTS SHOULD CHECK BOARD: superseded by the findings tree; `continuous-mapping` is closed (below).
- Roles of sessions (coord, front, scaffold, tractability, research, warden) and the 2026-11-24 status count (54 rows, 8 gaps): history, in the old file.

## Tasks (the small boards)

| Task board | Serves | Statement | Seats |
|---|---|---|---|
| [`asteroid-bench`](boards/tasks/asteroid-bench.md) | the asteroid language | Circuits in ONE pre-existing format: ISCAS ` | one Fable of main |
| [`asteroid-native`](boards/tasks/asteroid-native.md) | the asteroid language | asteroid with no Python: a command-line program written in Lean (one Lake executable) that reads an  | one Fable of main |
| [`asteroid-look`](boards/tasks/asteroid-look.md) | the asteroid website and terminal output | A colour scheme chosen by the owner: a small page with a colour picker per role (background, surface | coord, with small agents |
| [`open-one-not`](boards/tasks/open-one-not.md) | the Theorem (one NOT gate) | the general case, `no_minCE`; open: BottomPay | A1 to A14 |
| [`open-many-not`](boards/tasks/open-many-not.md) | C4 (several NOT gates) | S3(b); open: point lemma for two sets, rule R2 | B1 to B11 |
| [`open-qg`](boards/tasks/open-qg.md) | T9 | L-qg-115, 116, 119, 169: all proved (the exact 9k+3n+1 form by F2, `KAKParam.L119`) | C1 to C5 |
| [`qg-frontier`](boards/tasks/qg-frontier.md) | T9 | frontier survey and ranked formal targets | Q1 to Q4 |
| [`philosophy-formal`](boards/tasks/philosophy-formal.md) | the three levels (Deleuze, Fisher) | formal model of a cited reading, bridge to Phi | P1 to P4 |
| [`asteroid-term`](boards/tasks/asteroid-term.md) | asteroid | native asteroid on Linux (Arch) and Windows; mintty dropped | seats 1–4 done, 5 open |
| [`asteroid-exe`](boards/tasks/asteroid-exe.md) | asteroid | double-clickable `asteroid.exe` linked from the front page | done (native, 4.2 MB) |
| [`asteroid-cli-logo`](boards/tasks/asteroid-cli-logo.md) | asteroid | the 4STeroid logo as text art in the CLI | coord's Sonnet |
| [`asteroid-vscode`](boards/tasks/asteroid-vscode.md) | asteroid | `.ath` highlighting in VS Code (published) | coord's Sonnet |
| [`ath-prompt-quant`](boards/tasks/ath-prompt-quant.md) | `ath_prompt_method.md` | a quantitative version of one prompting claim | Sonnet |

**Closed on 2026-11-24 by the owner ("close all nonsense being done that isnt asteroid related").** Their files stay as the record; nobody works on them: `asteroid-bridge`, `asteroid-mixed-slack`, `asteroid-corpus`, `lean-eureka-asteroid`, `asteroid-cheap-proofs`, `asteroid-programs`, `beyond-one-not`, `edges`, `all-not-gates`, `rewire-read-not`, `c2-under-no-rewire`, `c1-three-gate`, `c4g-two-not-gates`, `family-for-many-not-gates`, `literature-c4`, `continuous-mapping`, `xor-extension-open-case`, `kannan-machine`, `qg-gaps`, `clay-model-equivalence`, `file-tree-merge`, `search-harness`, `telescope-l5-l6`, `lang-integration`.

## The boards

Each board serves numbered items of [`README.md`](README.md). Write on the board of the item you serve.

A few boards instead of one long one (owner, 2026-11-24: "its ok to have few boards now if its much better than readme strat"). Each board serves numbered items of [`README.md`](README.md), which is the proof. Write on the board of the item you serve; what everyone must see goes on the wall below.

| Board | Serves | Open now |
|---|---|---|
| [`boards/one-not.md`](boards/one-not.md) | the Theorem: D1 to D7, L1 to L4, T1 to T5, C1, C2 | C3 (priority): the k-point step, README §6. C1: a minimal counterexample that loses the certificate game |
| [`boards/ladder.md`](boards/ladder.md) | T6, T7 | L-gen-101 to 103; the XOR extension when C(f) = C(¬f); the Kannan machine |
| [`boards/physics.md`](boards/physics.md) | T8, T9, the premise | L-qg-115, 116, 119, 169 |
| [`boards/ops.md`](boards/ops.md) | no item: handoffs, compute, kill list, file tree | the README branch; second pass of the kill list |

## Reference (kept in full: targets, ladder, track pairs, literature)

The one board of this repository. A **row** is a checked statement; a **gap** is a statement written in Lean that still needs a proof (a `Prop` definition, never a `sorry`). Nothing on this board says that P versus NP is settled.

**How the pieces fit:** [`SYNTHESIS.md`](SYNTHESIS.md) (three layers: theorems, certificates and data, premises and maps; relativization against physical models; where L-meta-951 sits).
**Goal.** Lower bounds for circuits of AND, OR and NOT gates with any number of NOT gates
(`SIZE`, `PPoly` in `lean/PEqualNP/Defs/CircuitLowerBounds.lean`), with every method that fits:
circuit complexity, quantum gravity, pure mathematics. Owner, 2026-11-24: one place, everyone
merged, no refactoring of old material. The merge of sessions is one-to-one by role ("research->
research xyz-> xyz"): two sessions that hold the same role become one seat, and agents talk to
each other directly. The Discussion session (session_01GmnDheAyFnVcvRApd4xeES) runs the handoffs.

**Targets (Lean statements in `lean/PEqualNP/General/Gaps.lean`).**

| Id | Statement | State of knowledge |
|---|---|---|
| L-gen-101 | some language in NP has no polynomial-size circuits | open; it gives P ≠ NP; the circuit form of the problem |
| L-gen-102 | for every degree `k`, some language in NP has no circuits of size `c * n^k + c` (the smaller version: fixed degree) | open for NP for every `k ≥ 1`; proved one level up the polynomial hierarchy (Kannan 1982) |
| L-gen-103 | some language in NP has no linear-size circuits | open; best explicit bounds are linear: about `5n` gates for AND, OR, NOT; `3.1n - o(n)` for all two-input gates (Li, Yang 2022), by gate elimination |
| L-gen-104 | `⌈log₂ (n + 1)⌉` NOT gates are as good as any number, up to a polynomial factor | CHECKED 2026-11-24: `PEqualNP.General.Fischer.L104 : Gap.L104` (`General/FischerMain.lean`), p = 30 (X + 1)^3; Markov 1958, Fischer 1975 |

Checked: L-gen-001 (101 gives 102), L-gen-002 (102 gives 103), L-gen-003 (`SIZENot s s = SIZE s`:
the top of the NOT gate ladder is the general case), L-gen-004 (the ladder is monotone).
L-gen-005 (for non-constant `f` and a fresh input `x`: `C(x ⊕ f) ≥ max(C(f), C(¬f)) + 3`, every gate counted),
L-gen-006 (if `C(f) ≠ C(¬f)` then `C(x ⊕ f) = min(C(f), C(¬f)) + 4` exactly),
L-gen-007 (`C(f) + 1 ≤ C(¬x ∧ f) ≤ C(f) + 2` for non-constant `f` and a fresh input `x`).

**The NOT gate ladder (`SIZENot s t`: at most `t n` NOT gates).** This is how the restricted
work reaches the general problem.

| Rung | NOT gates | State |
|---|---|---|
| 0 | 0 (monotone) | superpolynomial bounds known (Razborov 1985) |
| 1 | 1 | L-meta-951: one NOT gate saves nothing on Boolean sums; one open statement, `no_minCE`. Lives in `one-not/` (separate Lake project `one-not/lean`, imported 1:1 from pequalnp-work coord-951 ee11077; board history `one-not/board/`). Sharpest open form: `MergePrice` for a minimal counterexample. Coord: session_01GmnDhdShHMzucEAq9ottn6 |
| k | fixed `k`, then `k` growing | Amano, Maruoka 2005: clique with `(1/6) log log n` NOT gates |
| n | `n` (NOTs on inputs only) | CHECKED: `Fischer.stage1`: SIZE s ⊆ SIZENot (2s + n + 2) n (dual rail) |
| top | `⌈log₂ (n + 1)⌉` | equal to unrestricted circuits up to a polynomial factor: CHECKED (L-gen-104, `Fischer.L104`) |

**Track pairs: each P versus NP track beside its counterpart.**

| # | P versus NP side | Quantum gravity or pure-mathematics side | What the pair says |
|---|---|---|---|
| 1 | Relativization: L-lib-061, L-lib-062 (Baker, Gill, Solovay) | closed timelike curves: L-qg-160 to L-qg-168 (NP and coNP inside P_CTC) | a physical resource acts as an oracle: it selects an oracle world and leaves the question without an oracle open |
| 2 | Algebrization: L-lib-065, L-lib-076 (Aaronson, Wigderson) | quantum circuits: L-qg-110 to L-qg-118; "acceptance probability is a polynomial of degree at most 2T" (Beals et al.) is not yet a row | low-degree extensions meet the same limit on both sides |
| 3 | Natural proofs: L-lib-086 (Razborov, Rudich) | pseudorandom boundary states under complexity = volume (Bouland, Fefferman, Vazirani): needs definitions | pseudorandomness blocks "natural" arguments on both sides |
| 4 | Counting: L-clb-005 (some language is not in P/poly) | L-qg-001, L-qg-002, L-qg-101 (some reversible map needs exponentially many gates) | one counting argument |
| 5 | One-way functions give P ≠ NP: L-qg-103 | hardness of decoding Hawking radiation (Harlow, Hayden; Aaronson): physics premise | the physics claim stands on a classical assumption that implies P ≠ NP |
| 6 | Rung 1 of the ladder: `no_minCE`, reduced to MergeFrac, a linear-programming duality statement | convex duality and fixed points: L-qg-102, L-qg-120 (every quantum channel has a fixed density matrix), `QuantumGravity/Helpers/FixedPoint.lean` | the same convex-duality mathematics; the right-hand side is checked |
| 7 | Geometric complexity theory: permanent against determinant (`lean/PEqualNP/Gct/`) | geometry of circuits: dimension count (gap L-qg-119), Nielsen (needs definitions) | dimension counting of orbits on both sides |
| 8 | Space-bounded computation: configuration counting | holographic bound: L-qg-010 | finitely many states bound the running time |

Unpaired so far (no counterpart found; do not invent one): the NOT gate ladder as a whole; exact
circuit sizes by gate elimination (edge function, L-meta-204, L-meta-612); holographic codes
(L-qg-140 to L-qg-149).

**Why the general problem is hard (checked rows in this repository).** L-lib-061, L-lib-062: no
argument that holds with every oracle separates P from NP. L-lib-065, L-lib-076: the same for
arguments that survive low-degree extensions. L-lib-086: with strong pseudorandom functions, no
"natural" property proves bounds against P/poly. A proof of L-gen-101 must avoid all three.

**Next up.**

| Rank | Card | Owner |
|---|---|---|
| 1 | Bring the L-meta-951 tree over one-to-one (`lean/PEqualNP/W951/`, `Kernel/`, `work/`, `tools/`), then close `no_minCE` | coord, front |
| 2 | Tie `SIZENot` to the 951 definitions; state rung `k` | tractability |
| 3 | L-gen-104 (Fischer) as a row; Kannan's theorem as a row (needs the second level of the hierarchy) | tractability, helpers; L-gen-104 DONE by GeNeRALIZE (General/FischerBasic, FischerInverter, FischerMain; std axioms): a superpolynomial lower bound for circuits with ⌈log₂(n+1)⌉ NOT gates is now, in Lean, one for all circuits. Kannan's circuit half DONE (GeNeRALIZE): `SizeHierarchy.size_hierarchy`: ∀ k ∃ L ∈ P/poly, ∀ c, L ∉ SIZE(c n^k + c) (General/SizeHierarchy.lean, std axioms); uniform half REDUCED (GeNeRALIZE; General/Kannan{Defs,Lang,Sigma}.lean, std axioms): `KL k` = lex-first hard truth table; `KL_not_SIZE`; `mem_KL_iff` (exact ∃∀∀∃ form over a computable `Check`); `kannan_uniform_of_check : CheckLinTime k → ∃ L ∈ SigmaP 3, ∀ c, L ∉ SIZE(c n^k + c)`. ONE GAP: `CheckLinTime k` (a TM2 machine deciding `CheckW` in time linear in the total input: circuit evaluation at all 2^m points + lex compare; est. thousands of lines of machine code). Σ₂ ∩ Π₂ (Karp–Lipton) not started |
| 4 | What is out there for unrestricted circuits: verify and extend the list below | research, the Generalize sessions |
| 5 | Read the official Clay problem description | DONE (session_01GmnDhgAdyDijthBgZgJFWn, claymath.org added to its environment): Cook's official text read; P and NP in `Defs/Base.lean` match it up to standard model equivalences (one-tape TM vs `FinTM2`, alphabet, witness bound), not formalized; `notes/general/clay-official-statement.md` |

**Ideas in the literature (research verified 2026-11-24; exact statements, DOIs and what was read:
`notes/general/research-lit-unrestricted.md`).** Gate elimination: Li, Yang 2022 3.1n - o(n) over all binary gates; Iwama,
Morizumi 2002 5n - o(n) in the De Morgan basis (NOT gates not counted); limits: Golovnev, Hirsch, Knop, Kulikov. Fixed degree
above NP: Kannan 1982 (Σ2 ∩ Π2; one summary disagrees, flagged), Cai (S2P ⊆ ZPP^NP), Vinodchandran (PP), Santhanam (MA/1).
Near-maximum: Korten 2021; Chen, Hirahara, Ren 2024 (S2E/1, 2^n/n); Li 2024 (S2E, almost everywhere). Algorithms to lower
bounds: Williams (NEXP ⊄ ACC0); Murray, Williams (NQP). Hardness magnification: Oliveira, Santhanam 2018; McKay, Murray,
Williams 2019; locality barrier: Chen et al. 2020. Meta-complexity: Hirahara 2018; Liu, Pass 2020. NOT gates: Markov;
Fischer; Amano, Maruoka; Sung, Tanaka; Jukna; Jukna, Lingas. Slice functions (monotone bounds transfer to unrestricted
circuits): Berkowitz; Valiant 1986; Wegener; Hiltgen, Paterson 1995.

**Watch (2026-11-24, raised by tractability).** There are two different `PEqualNP.Kernel` circuit
kernels: `lean/PEqualNP/Kernel/Circuit.lean` (root project) and `one-not/lean/PEqualNP/Kernel/Circuit.lean`
(the 951 kernel, which the 951 modules depend on). Tractability proposed to coord: drop the root
one and merge `one-not/lean` into `lean/`. Until coord decides, do not build new work on the root
`Kernel`.

**Rules.** A row is "checked": no `sorry`, only `propext`, `Classical.choice`, `Quot.sound`.
Open statements are `Prop` definitions. Physics premises never enter a Lean statement. Old
repositories are frozen as they are; new work lands here. Models: avoid Fable runs, a few are
acceptable; Sonnet is fine. Never run `lake update`.


## SPHERE OF FIELDS (SEATED 2026-11-25: Fable S1 theory, Opus S2 analytic proof, Sonnet S3 literature) (Addison, 2026-11-25: "we can sketch a sphere out of this, if each monqwensor field is complex enough, put some infinity of them around a sphere")

The precise mathematics is a field attached to every point of a sphere: a section of a bundle over S². Two real joins to test, theory first:
- **Hopf fibration / Bloch sphere.** Pure qubit states are the points of S²; the unit quaternions S³ = SU(2) fibre over S² with circle fibres. This joins the hypercomplex layer (quaternions), the qubit and KAK work, and the sphere picture in one standard object.
- **Hairy ball / Poincaré–Hopf.** Every continuous tangent field on S² vanishes somewhere (the zeros' indices sum to χ(S²) = 2). In Deleuze.lean's terms (a problem = a vector field, the actual = its zeros), every problem posed on the sphere has an actual solution, by topology alone. That is a theorem, not a rhyme, and it is the first place the philosophy files would meet real topology.
- Lean is last: Mathlib may lack the hairy ball theorem and Brouwer, so this stays `paper` until a statement is final.
- Extensions to follow (theory first): Poincaré–Hopf; Adams 1962 (the maximal number of independent vector fields on S^{n−1} is the Radon–Hurwitz number ρ(n), so S¹, S³, S⁷ are parallelizable exactly because of ℂ, ℍ, 𝕆, joining the hypercomplex layer); Hopf invariant one; Lefschetz; Brouwer and Borsuk–Ulam; Milnor's analytic proof (1978); combinatorial versions (Sperner, Tucker) and their complexity: finding a Sperner/Brouwer point is PPAD-complete (Papadimitriou 1994), a real link from the sphere back to complexity classes.
- **OPEN (S2 Opus, hairy ball via Milnor 1978).** Mathlib (this pin) has no hairy ball and no Brouwer; it has the change-of-variables formula (`integral_image_eq_integral_abs_det_fderiv_smul`). Checked in `lean/PEqualNP/Worlds/HairyBall.lean`: `norm_add_smul_of_tangent` (x + t·w lies on the sphere of radius ‖x‖√(1+t²)) and `not_polynomial_sqrt_pow_of_odd` ((1+t²)^{n/2}, n odd, is no polynomial near 0; `not_polynomial_sqrt_pow_three` for S²). Gap: for a C¹ unit tangent field v on S^{n−1} (extended homogeneously), (a) f_t = id + t·v is injective on the annulus A = {1 ≤ ‖x‖ ≤ 2} for small t (Lipschitz) and maps it ONTO the scaled annulus √(1+t²)·A (needs an open-closed / degree argument on the connected sphere, n ≥ 2); (b) vol f_t(A) = ∫_A det(I + t·Dv) is a polynomial in t; (c) conclude no such v for n odd; (d) continuous-to-smooth approximation (Weierstrass, cited). (a) is the hard step.
- Team now (Addison: "2 fables an opus and a sonnet is plenty"): S1 Fable (sphere theory), F1' Fable (k = 1 class point lemma, theory first), S2 Opus, S3 Sonnet.

## PAUSED 2026-11-25 ~03:30 (Addison: "im a bit worried about usage ... all subprocesses should die")
All seats stopped. Partial work kept: compute/funsearch/ (untested FunSearch loop), one-not/tools/tensor/{cache,dag}.py, lean/PEqualNP/Philosophy/Spinoza.lean (checked, 0ec029c). Not started or not pushed: monqwensor, hyperfinite, hypercomplex, Buddhist, the rest of the emotion framework (Freud, Lacan, Dependence, Arabic/Greek/Stoic strands). Each card keeps its full brief; reopen any by seating one line.
