# Beauvoir routed at quantum gravity's sets, nodes and edges (seat BQG, 2026-11-25)

Asked for by Addison: "best route imo is to attack beauvoir specifically routed at quantum gravity set/node/edge".

Lean file: [`lean/PEqualNP/Philosophy/BeauvoirQG.lean`](../lean/PEqualNP/Philosophy/BeauvoirQG.lean). It builds with Mathlib only, with no `sorry`. `#print axioms` on every theorem named below gives at most `propext`, `Classical.choice`, `Quot.sound`.

This note has three parts, and the line between them is the point of the note.

- Part 1 is mathematics checked by Lean. It is true whatever one thinks of Beauvoir.
- Part 2 is interpretation. None of it is checked, and none of it can be.
- Part 3 lists what failed, what does not fit, and what was not done.

Nothing here is a claim about what Beauvoir, Hegel or Barrès meant. Nothing is a claim about physical spacetime. Nothing bears on P versus NP. No source was re-read in this session (see `LITERATURE.md`, section M6).

## Part 1. What is checked

### 1a. Two parties in a pure state (matrices over ℂ, any finite dimensions)

A pure state of two parties is its amplitude matrix `M`. The first party's reduced state is `M Mᴴ` (`selfState`). The second's is `Mᴴ M` up to a transpose (`otherState`).

| Theorem | Statement |
|---|---|
| `moments_symm` | `tr (M Mᴴ)^k = tr (Mᴴ M)^k` for every `k ≥ 1`. Purity and all integer Rényi entropies agree on the two sides. |
| `schmidt_rank_symm` | The two reduced states have the same rank. |
| `entropy_symm` | The von Neumann entropy `∑ -λ log λ` over eigenvalues is the same for `M Mᴴ` and `Mᴴ M`. This is `S(A) = S(B)`. The proof uses Mathlib's `charpoly_mul_comm'`, not a Schmidt decomposition. |
| `sum_minor_sq` | `∑ |2×2 minor of M|² = 2 ((tr ρ)² − tr ρ²)` with `ρ = M Mᴴ` (Lagrange's identity). |
| `pure_iff_product` | `tr ρ² = (tr ρ)²` if and only if `M = u ⊗ v`. A party's reduced state is pure exactly when the joint state is a product. |

### 1b. Three parties

The state is written as the amplitude matrix of the cut "(first, second) against third".

| Theorem | Statement |
|---|---|
| `couple_entropy_eq_third` | `S(AB) = S(C)` for a pure three-party state. An instance of `entropy_symm`. |
| `monogamy_of_pure_pair` | If the reduced state of (first, second) is pure, the reduced state of (first, third) is a product `σ ⊗ τ`. |
| `ghz_pair_separable` | For `|000⟩ + |111⟩`, the reduced state of two parties is `|00⟩⟨00| + |11⟩⟨11|`, a sum of two product states. |
| `ghz_couple_mixed` | For the same state, the reduced state of a pair is not pure. |

### 1c. Nodes and edges: minimal cuts of a weighted graph

`cut w S` is the weight separated by a set of nodes `S`. `rt w bdy A` is the least cut among sets that agree with `A` on the boundary nodes. These are sums of natural numbers; no quantum state appears.

| Theorem | Statement |
|---|---|
| `rt_compl` | A boundary region and its complement have the same value. |
| `rt_submodular` | `rt(A ∪ B) + rt(A ∩ B) ≤ rt(A) + rt(B)`. This is strong subadditivity for minimal cuts. |
| `rt_monogamy` | For pairwise disjoint `A`, `B`, `C`: `rt(A) + rt(B) + rt(C) + rt(ABC) ≤ rt(AB) + rt(BC) + rt(AC)`. This is monogamy of mutual information. The proof is one inequality per edge (`edge_monogamy`, 64 cases). |
| `no_network_has_ghz_entropies` | No weighted graph gives seven equal nonzero values for `A`, `B`, `C`, `AB`, `BC`, `AC`, `ABC`. |
| `schmidt_rank_le_bond`, `schmidt_rank_le_cut` | If `M = L R` factors through a bond space made of `|E|` edges of dimension `D`, the Schmidt rank is at most `D^|E|`. |
| `bell_bond_saturates` | The identity matrix (one maximally entangled pair per bond index) attains the bound. |

### 1d. Partial orders (causal sets)

`Spacelike m x` means incomparable. `Beyond m x` means no element is above both.

| Theorem | Statement |
|---|---|
| `spacelike_of_beyond`, `beyond_symm` | `Beyond` implies `Spacelike`, and is symmetric. Any partial order. |
| `beyond_mono` | If `m`, `x` have no common upper bound, neither do any `m' ≥ m`, `x' ≥ x`. Any partial order. |
| `frame_beyond_iff_spacelike` | On a Fisher frame (linear past) the two relations coincide. |
| `barbarian_iff_beyond`, `recognise_iff_not_beyond` | On a Fisher frame, `Beauvoir.Barbarian` is `Beyond`, and `Beauvoir.Recognise` is its negation. |
| `lightcone_spacelike_meet`, `lightcone_not_frame` | In `ℕ × ℕ` with the product order, `(1,0)` and `(0,1)` are spacelike and meet at `(1,1)`. So this order does not have linear past. |
| `directed_no_beyond`, `frame_directed_total` | In a directed order nothing is `Beyond` anything. A directed Fisher frame is a chain. |
| `causal_order_from_links` | In a locally finite order, `<` is the transitive closure of the covering relation. This is Mathlib's `lt_iff_transGen_covBy`, restated. |

## Part 2. What is interpretation

Each item names the checked theorem it leans on. The step from the theorem to the sentence is ours.

1. **Self and other as two tensor factors.** Treating two persons as two subsystems of one pure state is a modelling decision. It is a different model from `Beauvoir.lean`, which treats the other as an unchosen branch of one tree. The two models are not derived from each other.
2. **Mutual constitution.** `entropy_symm` and `moments_symm` say the two reduced states are mixed to the same degree. Read: what the self lacks when taken alone is exactly what the other lacks when taken alone. This is our reading of Hegel's mutual recognition and of Beauvoir's "opposition of self and other".
3. **Ambiguity.** `pure_iff_product` says a party is a definite pure state on its own only if it is unrelated to the other. Read: a self in relation is not a self-sufficient thing. Calling this Beauvoir's ambiguity is our label; `Beauvoir.ambiguity` in the tree model is a different statement.
4. **"To will oneself free is to will others free."** `UNIFY.md` recorded that the tree model has no theorem for this. If one reads entropy as openness, `entropy_symm` says the self's openness equals the other's. This is a suggestion, not a result: entropy is not freedom, and nothing in the Lean says so.
5. **The triad of *She Came to Stay*.** Françoise, Pierre and Xavière as three subsystems. `monogamy_of_pure_pair` reads: a couple that is one closed whole leaves the third uncorrelated with either. `ghz_pair_separable` reads: in a three-way bond of GHZ type, no two share entanglement once the third is ignored. `couple_entropy_eq_third` reads: the couple is exactly as open to the third as the third is to the couple.
6. **The epigraph.** "Each consciousness seeks the death of the other." In this model, discarding the other (the partial trace) leaves the self mixed whenever the two were entangled (`pure_iff_product`). Read: removing the other does not return the self to itself. This echoes Hegel's point that the struggle to the death defeats itself. See Part 3, item 3, for why the echo is weak.
7. **Networks.** In holographic tensor networks the entropy of a boundary region is a minimal cut (Ryu and Takayanagi; Pastawski, Yoshida, Harlow and Preskill). Under that cited premise, `rt_compl` is `S(A) = S(B)` on nodes and edges, and `rt_monogamy` says correlations in such a network are always monogamous: what one party shares with two others separately never exceeds what it shares with them together. `no_network_has_ghz_entropies` then says the GHZ-type triangle of item 5 cannot be drawn on any such network.
8. **The barbarians and the horizon.** `barbarian_iff_beyond` identifies the tree model's barbarian with "no common future". In a general causal set that is stricter than spacelike separation. Read: the barbarian is not merely someone elsewhere, but someone with whom no later meeting exists. `beyond_mono` is then the permanence of that separation.

## Part 3. What failed, what does not fit, what was not done

1. **The Coffman–Kundu–Wootters inequality is not proved.** It needs the concurrence of mixed two-qubit states (Wootters' formula, through eigenvalues of `ρ ρ̃`). Only the extreme case (`monogamy_of_pure_pair`) and one state (GHZ) are checked. The W state was not checked.
2. **Symmetric entropy cannot tell recognition from domination.** `entropy_symm` holds for every pure state of two parties. So it holds for master and slave as well as for equals. It is a constraint, not a model of recognition. It also fails as soon as a third party is present: in a three-party pure state `S(A)` and `S(B)` differ in general (standard fact, not checked here). Only `S(AB) = S(C)` survives.
3. **A partial trace is not a death.** The partial trace ignores the other. An actual measurement or removal of the other can leave the self in a pure state. So item 6 of Part 2 supports "ignoring the other does not purify the self", and does not support a statement about killing. The ending of the novel is not modelled.
4. **The min-cut theorems are not connected to quantum states in Lean.** `rt` is defined on graphs. That it equals an entanglement entropy for HaPPY states is cited, not proved. The only link checked is the upper bound `schmidt_rank_le_cut`, and it assumes the factorisation `M = L R` that a cut of a tensor network provides; the contraction of a general network is not formalised. The repository's stabilizer core (L-qg-140 to 149) is not used.
5. **Persons as boundary regions of a graph** has no support beyond the analogy. Monogamy of mutual information is a property of holographic states, not of quantum states in general, and nothing suggests relations between persons are "holographic".
6. **Barbarian as spacelike does not survive in causal sets.** In the tree model, incomparable moments never meet (`Beauvoir.no_recognition_between_barbarians`). In a causal set with diamonds they do (`lightcone_spacelike_meet`). The tree is a causal set only of a special kind (`lightcone_not_frame`). The direction "the barbarian is the region outside one's causal past and future" therefore loses its permanence. What survives is the stricter relation `Beyond`.
7. **Overlap.** `beyond_mono` and the diamond example are close to `Unify.permanence_iff_no_reconciliation` and `Unify.diamond_reconciles`, which hold in any partial order. The new content of section 1d is small. `causal_order_from_links` is a Mathlib lemma under a physics name.
8. **Local finiteness** (what makes a partial order a causal set) is used only in `causal_order_from_links`. No causal-set dynamics, sprinkling, or dimension estimate is touched.
9. **No source was opened in this session.** The novel, the essay and the physics papers are cited from memory. The epigraph is quoted as the scholarship gives it.
10. **"Almost the entirety of known mathematics"** is not addressed. This file uses linear algebra, finite sums and order theory.

## Sources

Read status and bibliographic details are in `LITERATURE.md`, section M6. Beauvoir's works are in copyright; they are cited and not copied.
