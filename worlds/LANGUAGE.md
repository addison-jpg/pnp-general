# Languages: what P vs NP is in language terms, and what it is not

Seat: language unification (Fable), 2026-11-25. Source of the task, Addison: "make sure the goal is up up up, in reference to what pnp is formally. if side efforts at language unification would help, take a serious fable stab at it", then "it means checking work on mapping language, because i know it exists", then "we should consider that at this level human language may be somewhat interchangeable with coding language."

Nothing here says P vs NP is proved, near, or helped. This note restates the question in logic and maps where languages of different kinds sit. Each line below is marked as one of: **checked** (a Lean theorem in this repository), **theorem (literature)** (with read status), **measured**, or **interpretation** (ours, no proof).

Read status as in [`LITERATURE.md`](../LITERATURE.md): TXT, ABS, TLDR, MEM, CITED. In this seat nothing was read in full. "search summary" means a tool's summary of search results or of a fetched page.

## 0. Prior art first (this map is mostly not ours)

| Work | What it maps | What it covers | Status |
|---|---|---|---|
| Fagin 1974 | logic ↔ complexity | NP = properties definable in existential second-order logic (∃SO) | MEM |
| Immerman 1982, 1986; Vardi 1982 | logic ↔ complexity | on ordered finite structures, P = first-order logic with least fixed points, FO(LFP) | MEM |
| Immerman, *Descriptive Complexity* (1999); Libkin, *Elements of Finite Model Theory* (2004); Grädel et al., *Finite Model Theory and Its Applications* (2007) | textbooks | the whole table: FO = AC0 with BIT, FO(TC) = NL, FO(LFP) = P, ∃SO = NP, SO = PH, FO(PFP) = PSPACE; Grädel: SO-Horn = P; Abiteboul–Vianu: FO(LFP) = FO(PFP) iff P = PSPACE | MEM (no book opened) |
| Senellart, `descriptive-complexity` (Lean 4, Mathlib v4.36.0, Apache 2.0); Senellart and Gnatenko, arXiv 2609.18261 (2026) | the same, in Lean | a library on Mathlib's `ModelTheory`: classes defined by logics, 73 completeness results by first-order reductions, NL = coNL, Abiteboul–Vianu, an internal `lfpDefinable_iff_mem_PTIME`, bridges to `Turing.FinTM2`. The page's summary says the string-level capture theorems (Fagin, Immerman–Vardi, Lax archive entries by Toruńczyk) enter the machine half as hypotheses; I could not confirm this from the source | search summary and fetched page summary; source code not read |
| Montague 1970–73; Lambek 1958 (categorial grammar, later pregroups) | natural language → logic | a fragment of English translated compositionally into typed logic; grammar as a type calculus | MEM |
| Joshi 1985; Shieber 1985 | natural language → Chomsky scale | natural-language syntax is beyond context-free (Swiss German cross-serial dependencies) and within "mildly context-sensitive" classes, which are recognised in polynomial time. A 2026 *Computational Linguistics* article disputes the Shieber argument | MEM; Shieber and the dispute: search summary |
| Coecke, Sadrzadeh, Clark, arXiv 1003.4394 (2010), DisCoCat; lambeq | grammar → vector spaces | a functor from a pregroup grammar to vector spaces: the meaning of a sentence is a contraction of word tensors, drawn as a string diagram or tensor network | ABS (search summary) |
| Mikolov et al. 2013 (arXiv 1309.4168); Conneau et al. 2017 (arXiv 1710.04087); Schönemann 1966 | language ↔ language, as vector spaces | a linear, later orthogonal (Procrustes, closed form by SVD), map from one language's word vectors onto another's; assumes the two spaces are nearly isometric | search summary of secondary sources; arXiv numbers from memory, unverified |
| Curry–Howard (Curry 1934, Howard 1969) | proofs ↔ programs | a proof of a proposition is a program of the matching type; Lean is built on it | MEM |
| Shannon 1948; Kolmogorov 1965 | strings ↔ description length | a probabilistic model gives a code of length −log p; shortest descriptions in two universal languages differ by a constant | MEM |

**What this repository's Lean file builds on.** Mathlib's `Turing.FinTM2` and this repository's `P`, `NP` (`lean/PEqualNP/Defs/Base.lean`), nothing else. It does not reuse Mathlib's `FirstOrder.Language` (its formulas have no fixed point constructor) and does not reuse Senellart's library (a new dependency needs `lake update`, which is forbidden here). So `Descriptive.lean` is a small second copy of known definitions. Its only use is that the equivalence is stated against the same `P` and `NP` as every other statement in this repository. If the dependency rule changes, the right move is to import the library and delete most of the file.

## 1. Checked

File: [`lean/PEqualNP/Worlds/Descriptive.lean`](../lean/PEqualNP/Worlds/Descriptive.lean). No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` only. Build: `cd lean && lake build PEqualNP.Worlds.Descriptive`.

Definitions (not theorems; a wrong definition would make the theorems empty, so they are listed):

- `Struc`: a finite structure with universe {0, …, n−1} and the order of ℕ. `Vocab`: a list of arities.
- `Fml`: one syntax with =, <, relation atoms, ¬, ∨, ∧, ∃, ∀ and `lfp`. `Holds`: satisfaction. `IsFO`: no `lfp`. `WF σ`: atoms fit σ and every `lfp` body is positive in its bound variable.
- `FODef`, `LFPDef`, `ESODef`: the properties definable in FO, FO(LFP), ∃SO. `enc`: a structure as a binary string (its truth tables). `encLang σ Q`: the language of the encodings of Q.
- `Fagin`, `ImmermanVardi`: the two capture theorems as `Prop`s. **Not proved here.**

Theorems:

| Name | Statement | Uses |
|---|---|---|
| `p_eq_np_iff_lfp_eq_eso` | `Fagin → ImmermanVardi → (P = NP ↔ LogicsCoincide)`: granted the two capture theorems, this repository's P = NP holds exactly when FO(LFP) and ∃SO define the same properties of finite ordered structures | both capture theorems as hypotheses |
| `enc_wordStruc`, `encLang_wordProp` | the adapter: a binary string is the structure with one unary relation, and its encoding is the string itself, so every language is `encLang` of a property | nothing |
| `eso_subset_np` | ∃SO ⊆ NP: the guessed relations are the witness, of polynomial length (`tablePoly`) | ONE unproved premise, `FOModelCheckingInP` |
| `fagin_of_halves` | `Fagin` follows from `FOModelCheckingInP` and the hard half NP ⊆ ∃SO | both as hypotheses |
| `holds_mono`, `lfp_isLeast`, `lfpSet_le` | for a positive body, the `lfp` constructor denotes a fixed point of the body, below every closed set (Knaster–Tarski) | nothing |
| `lfpDef_esoDef` | granted both capture theorems, FO(LFP) ⊆ ∃SO; this is P ⊆ NP (L-lib-010) | both capture theorems |
| `single_instance` | a claim about one fixed structure defines at most one string | nothing |

**What was tried and where it stopped.** The cheap direction ∃SO ⊆ NP was done down to one premise. `FOModelCheckingInP` says a first-order sentence can be evaluated in polynomial time on a structure given as two table strings. It is true and standard. Proving it here means building a formula evaluator on `Turing.FinTM2` with nested loops over tuples; the library has composition, pairing and transducers (`Library/Machines`) but no loop over a counter of polynomial range driven by a formula. That machine was not built. FO(LFP) ⊆ P was not attempted; it needs the same evaluator plus an iteration bounded by n^k stages.

**Limits of what is checked.** (1) `Fagin` and `ImmermanVardi` are hypotheses. That my `Prop`s are faithful statements of the textbook theorems is interpretation, not checked: the encoding has no size prefix (so the statements are restricted to vocabularies with a relation of positive arity, `Pos`), free variables are read as 0, and empty structures are allowed. (2) Two sanity examples were run and not committed: the sentence "some position carries a 1" holds of the word 01 and fails on 00. (3) `p_eq_np_iff_lfp_eq_eso` is two rewrites once the adapter is in place. It is a restatement.

## 2. The honest map

From formal languages up to natural ones. For each link: theorem or analogy.

**a. Strings.** A language is a set of binary strings; P and NP are sets of languages (`Defs/Base.lean`). This is the level at which P vs NP is stated.

**b. Logics.** A logic is a language for describing properties. Link a ↔ b: **theorem (literature)**, Fagin and Immerman–Vardi; **checked** here only as the implication in section 1. The measure changes: time on a machine becomes the kind of quantifier needed to say the property. That is the sense in which complexity is a property of description.

**c. Lean.** A language of statements and proofs. Link to b: Lean's logic contains all the logics above, and a Lean statement about `P` and `NP` is a statement about level a. Link by **theorem**: Curry–Howard, and the kernel's check. What a Lean theorem means in words is **interpretation** every time.

**d. asteroid.** A `.ath` claim speaks about fixed circuits: a finite structure (points, gates, wires) and numbers computed from it. `forall cubes` ranges over the subsets of the points (2^n cases, `cube_count`); `forall states` over pairs of disjoint subsets (3^n, `state_count`); `claim forall c in W` over a finite corpus. In logical terms a claim is a sentence with bounded quantifiers, at most universal quantification over sets of points (monadic second order), evaluated on ONE finite structure of fixed size. Its truth is decided by running through the cases, which is what `decide +kernel` does. It defines no infinite family, so it has a truth value and a checking cost but no growth rate, and no place among P, NP, FO(LFP) or ∃SO (**checked**, `single_instance`: such a claim fixes at most one string). The step from "true on these circuits" to "true for every n" is a Lean theorem with a real ∀, never an asteroid claim. Placement in logic: **interpretation** plus the one lemma.

**e. Natural languages: syntax.** Link to a: **theorem (literature)**, with a contested premise. If natural-language syntax is mildly context-sensitive (Joshi; Shieber), its string sets are recognised in polynomial time, so they are in P and, by Immerman–Vardi, FO(LFP)-definable on word structures. That places the grammar of a language, not its meaning.

**f. Natural languages: meaning.** Montague and categorial grammar map a fragment of English into logic (**theorem** for the fragment, by construction). DisCoCat maps grammar to tensor contractions. Embedding alignment maps one language's vectors onto another's by an orthogonal matrix. These are real maps with theorems inside them (functoriality; the Procrustes closed form). None has a theorem that connects it to P vs NP.

**g. Natural languages: description length (the Qwen measurements).** Measured in [`ath_prompts/measure/results.md`](../ath_prompts/measure/results.md): on 10 prompts, Addison's text is shorter than formal rewrites (236 against 267 Qwen tokens) and more surprising to Qwen2.5-0.5B (6.0 against 4.6 nats per token). Link by **theorem**: the summed surprisal is the length of a code for the text under that model (Shannon). Link by **analogy only**: reading that code length as "information in the prompt". It depends on the model; a 0.5B model's surprisal reflects its own gaps, and the known higher perplexity on African American English (Blodgett et al. 2016) is model bias, not content. The register, AAVE and translation runs are OPEN in [`boards/tasks/ath-prompt-quant.md`](../boards/tasks/ath-prompt-quant.md); nothing is claimed about them here.

**Where description length does meet P vs NP by theorem.** Two places, neither ours. (1) Descriptive complexity, level b. (2) Kolmogorov complexity and meta-complexity: [`routes.md`](routes.md) section 5 (Liu–Pass; MCSP). The Qwen numbers are neither: a model's code length is not Kolmogorov complexity, and a prompt is one string, not a family.

**DisCoCat and this repository's tensor networks.** Both are drawn as tensor networks and both live in compact closed categories. That is a shared notation and a shared category: **analogy**. No statement here or in the literature read transfers a result between sentence meaning and the quantum-gravity codes in `lean/PEqualNP/QuantumGravity`. Worth one Sonnet line only if someone states a concrete claim to test.

**One-line summary of the map.** Strings ↔ logics: theorem. Logics ↔ Lean: theorem (kernel), meaning by interpretation. Lean ↔ asteroid: theorem per claim, finite instances only. Formal ↔ natural syntax: theorem with a contested empirical premise. Formal ↔ natural meaning: maps exist for fragments. Natural ↔ description length: a code length under one model. The last three do not touch P vs NP.

## 3. Thesis: "at this level human language may be somewhat interchangeable with coding language"

Tested in parts.

**True in these senses.**

- As strings. A language model reads a prompt and a program as token sequences from one vocabulary and assigns both a probability. At that level they are the same kind of object, and the Qwen instrument can measure both with one number. **Measured** for prompts; the comparison with code was not run.
- Proofs and programs. Curry–Howard: a proof is a program. **Theorem (literature)**, and the working basis of Lean.
- English into logic. Montague-style translation and semantic parsing turn sentences of a fragment into formulas. **Theorem for the fragment**; engineering beyond it.
- As instructions. An informal line and a formal one can cause the same action. This is what this repository does every day; it is a fact about practice, **not a theorem**.

**False in these senses.**

- Semantics. A program has one meaning fixed by its language definition. A sentence has none fixed: it is ambiguous, and its meaning depends on the speaker, the context and the reader. No theorem fixes the meaning of "up up up".
- Grammar. Programming languages are designed to be parsed without ambiguity (deterministic context-free, plus typing). Natural languages are ambiguous and sit at mildly context-sensitive by the usual account.
- Checking. A Lean statement can be checked by a kernel. An English sentence cannot; only a formalisation of it can, and the choice of formalisation is a human act.
- Dialects. Every Lean file is equally readable to the checker. A language model reads Standard English better than AAVE or scene text, so "interchangeable" holds less well exactly where the board notes say models are weak.

**The chain in this repository, with this task as the example.**

| Step | Text | Lost | Added |
|---|---|---|---|
| prompt | "make sure the goal is up up up, in reference to what pnp is formally" | nothing yet | — |
| board line | "TAKEN: language unification (Fable): descriptive complexity (Fagin, Immerman–Vardi) as Props against the repository's P and NP" | the open direction ("up up up" could have meant circuits, proof complexity, or any other route); the tone; the demand to keep the goal high | a choice of field, two named theorems, an owner |
| Lean statement | `Fagin → ImmermanVardi → (P = NP ↔ LogicsCoincide)` | everything not about ordered finite structures; all of natural language | exact definitions: an encoding, a syntax, a semantics, the restriction `Pos`; each is a decision the prompt did not make |
| checked proof | the kernel accepts it | nothing | certainty that the statement follows from the definitions, and nothing about whether the definitions are the intended ones |

So the interchange is real in one direction and lossy: each step down removes ambiguity by choosing, and the choices are not in the prompt. Going back up (reading a Lean theorem as an English claim) adds meaning that the kernel did not check. The thesis holds as "both are strings a model can act on" and fails as "both mean something fixed". **Interpretation**, apart from the table's two quoted texts and the Lean statement.

## 4. What this does and does not say about P vs NP

- It restates it. On ordered finite structures, P = NP exactly when FO(LFP) = ∃SO; here that equivalence is checked relative to the two capture theorems as hypotheses.
- It does not move it. No lower bound, no separation, no new technique. Separating FO(LFP) from ∃SO on ordered structures is the same problem; the known inexpressibility tools (Ehrenfeucht–Fraïssé games, locality) work without an order and fail with one (MEM).
- It does not connect to this repository's circuit bounds. Those are linear bounds on functions in P in a restricted model ([`routes.md`](routes.md)); nothing here changes that distance.
- The natural-language measurements say nothing about P vs NP. They concern how tasks are stated to agents.
