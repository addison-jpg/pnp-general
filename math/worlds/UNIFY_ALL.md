# What joins the programs: theorems, analogies, rhymes that fail

Seat: cross-program unification (Fable), 2026-11-25. Programs: circuits (one-NOT, several-NOT, the payment Hall
condition), quantum gravity (counting, CTCs, CKW), logic and language (the Lawvere spine, descriptive complexity),
philosophy (frames, the DAG, Beauvoir at QG), and the three levels.

Words. **checked** = a Lean theorem in [`lean/PEqualNP/Worlds/Unify.lean`](../lean/PEqualNP/Worlds/Unify.lean) or a
named file (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`). **tested** = computed by
[`unify_rank.py`](unify_rank.py). **paper** = argued here. **cited** = a published theorem quoted from memory, not
reopened in this seat. A theorem name in a program's vocabulary is a reading; the Lean statement is about finite sets,
numbers and functions and nothing else.

Nothing here proves P ≠ NP or P = NP, brings it nearer, or proves BottomPay or `no_minCE`. The joins below are
elementary. Their use is that they say exactly which parts of the programs are one statement and which are not.

**Status of the circuit side when this was written (LIT2, commit 7816443).** The point lemma is false for general
families (AG(2,8) without verticals: a 261-line point program against base 448), so PHC@0 for all point programs is
false; the target "at least base gates for every number of NOT gates" is false on large planes (cited: Wegener 1987
§6.7 with Singer circulants; LIT2's derivation, not in Lean). One NOT gate is open; BottomPay and the two-set forms are
not refuted. No join below rests on the point lemma or on "every k". Join A1 states what the refutation means.

---

## Part 1. Theorem-level joins

### A1. One potential for counting and for payment: the truncation (checked; tested)

Candidate (a) asked for one statement about a rank function on gates with base, Knill's count and PHC as instances.
There is one, and it also says where they part.

**Definitions** (`Unify.lean`, Part A). `E` a finite set of gates (payers, gate positions). A potential is
`f : Finset E → ℕ`. `Lip c f`: adding gates raises `f` by at most `c` each. The truncation
`trunc c f A = min over B ⊆ A of f(B) + c·|A ∖ B|`.

| Theorem | Statement | Reading |
|---|---|---|
| `lip_count` | `Lip c g → g A ≤ g ∅ + c·|A|` | the bounded-increment count, the one shape shared by every bound below |
| `trunc_lip`, `trunc_le`, `le_trunc`, `trunc_mono` | `trunc c f` is below `f`, has increments ≤ `c`, is the **largest** such potential, and is monotone when `f` is | the best count obtainable from `f` at rate `c` |
| `trunc_eq_iff` | `trunc c f A = f A ↔ ∀ B ⊆ A, f A ≤ f B + c·|A ∖ B|` | the **split condition**: the Edmonds / Nash-Williams inequality, with no matroid in it |
| `trunc_eq_of_lip` | `Lip c f → trunc c f = f` | **counting case**: additivity over gates is automatic |
| `lip_sum` | a sum of `W` unit-increment potentials is only `Lip W` | **where additivity is lost**: one gate can serve every set |
| `unsplit_of_partition`, `count_of_partition` | monotone unit-increment `r_w`, pairwise disjoint parts `P_w ⊆ A` with `r_w(P_w) = r_w(A)` ⟹ the split condition for `Σ_w r_w` at `A`, and `Σ_w r_w(A) ≤ |A|` | **necessity of PHC for arbitrary rank-like functions**; no matroid axiom |
| `count_of_unsplit` | split condition at `A` and `f ∅ = 0` ⟹ `f A ≤ c·|A|` | PHC@0 ⟹ point lemma (U1 §2.2) is the case `B = ∅` |

**Instances.**

* *Base for one set* (`one-not/lean`: `FlipLemma`, `Or4ManyNot`, `OrSystemManyNot`; checked there): `c = 1`, `r_w` =
  merges on `S_w`. `lip_count` is the bound, and it is explicit.
* *PHC* (U1 §1, F1 Lemma D): `c = 1`, `f = Σ_w r_w`, or F1's `f(J) = Σ_w (|K_w| − c_w(J))`. The equivalent form of PHC
  in U1 §1 and the deletion form of Lemma D are both literally `trunc 1 f E = f E` (`trunc_eq_iff`; paper: matching
  the symbols). F1's checked `deletion_of_forestPay` (`one-not/lean/.../Open/PHC.lean`) is the instance of
  `unsplit_of_partition` for hypergraphic ranks; the general form here was not in the repository. The converse
  (split condition ⟹ disjoint bases) is Edmonds 1965 / Nash-Williams 1966 for matroid ranks (cited; not in Lean).
* *Counting* (`MetaComplexity.L002` Shannon; `QuantumGravity/Open/ApproxCount.lean` Knill; `KnillParam15.lean`,
  `KAKParam.lean` L119 with 16k, 15k+1, 9k+3n+1): the potential is a log-count or a parameter dimension of the set
  of **all** circuits on `k` positions. It is `Lip c` by construction (a product of counts, a sum of dimensions), so
  `trunc_eq_of_lip` applies: nothing to split. Reading only: the Lean statements of L115 to L119 are about Haar
  measure and are not derived from `lip_count`.

**So the one statement is:** *gates ≥ (trunc c f)(E) / c, and the truncation equals `f` exactly when the split
condition holds.* Counting bounds have it for free and name no hard object. The base bound names its object and has
to prove it. U1 §5 said "PHC is exactly the missing additivity" in prose; `trunc_eq_iff` against `trunc_eq_of_lip` is
that sentence as a theorem.

**What the LIT2 refutation is, in these terms** (paper). A program with fewer lines than base violates the conclusion
of `count_of_unsplit`, so the split condition fails at `B = ∅`: the truncation is strictly below `f`. The potential
`f = Σ_w merges` is still valid, but its increment per gate is not 1. By `lip_sum` it can be as large as the number
of sets a gate serves, and a circuit with NOT gates can make gates that serve many sets at once (cited: Wegener 1987
§6.7, negations are powerful for Boolean convolution). The honest lower bound from this potential is `f(E) / lip(f)`,
and `lip(f)` grows with the instance. That NOT gates help at scale on these sums is the same fact as "the split
condition fails at scale".

**Tested on stored data** (`python3 -I math/worlds/unify_rank.py one-not/data/witnesses/*.json
one-not/data/witnesses/nonlocal/general*.json`; 21 circuits, 0 to 6 NOT gates, n ≤ 14; every subset of payers,
621,808 in all; 16 s). Instance: U1 §2.3 at the single point 0, potential `f` of Lemma D.

| quantity | result |
|---|---|
| split condition `trunc 1 f E = f E = Σ need` | holds on 21 of 21 |
| `trunc 1 f` submodular (it should be a matroid rank, by Edmonds) | 0 violations |
| largest jump of `f` from one gate (`lip`) | between 2 and 6; never 1 |

So on every stored circuit one gate does merge for more than one pair at a time (the count `f(E)/lip` alone would
give between a half and a sixth of base), and the split condition still holds. These are small instances; LIT2 shows
it cannot hold for all large ones when NOT gates are free.

### B1. Diagonal and counting are one argument at three prices (checked; the complexity reading is cited)

Candidate (b). Both engines prove "this table of devices misses a function". `Unify.lean`, Part B:

| Theorem | Statement | Price of the witness | Reach |
|---|---|---|---|
| `diag_explicit` (from `Lateral/Lawvere.lean::no_row_of_fixed_point_free`) | for every `e : A → A → Bool`, `fun a => !(e a a)` is no row | one evaluation of one device per point | devices indexed by the points |
| `diag_of_private`, `private_reach` | one private point per device gives an explicit missed function; needs `|D| ≤ |A|` | one evaluation per point | at most as many devices as inputs |
| `halve_not_mem` | fewer than `2^m` devices on `m` points: `halve m S ∉ S`, where `halve` sets each value to the minority value among the surviving devices | **a count over all devices** per point | the full counting range `|D| < 2^m` |
| `count_exists` | `|D| < 2^|A|` ⟹ some function is no device | none: no witness | `|D| < 2^|A|` |

The join is `halve_not_mem`: counting made explicit **is** a diagonal, one that kills half of the devices per point
instead of one, and pays for it by counting devices. Finite Cantor (`|A| < 2^|A|`) is the one statement both prove.

**Where each program sits** (reading).

* Diagonal: `math/lateral/` (Cantor, Russell, no computable enumeration, Camus); the time hierarchy theorems (cited:
  Hartmanis, Stearns 1965), the only proved infinite ladder on the worlds map.
* Counting: Shannon `L002`; Knill `ApproxCount`, L116; L119 in all three forms; L115 (the ball volume that the count
  is compared with).
* Neither: the base bound, `Or4ManyNot`, `FlipLemma`, BottomPay. These are potential arguments about one named
  function (A1 with `c = 1`), the family of gate elimination and of monotone methods.

**Why counting never gives explicit hardness, and why the diagonal relativizes** (cited; stated, not proved here).

1. Counting compares all devices with all functions. With `2^{O(s log s)}` circuits of size `s` on `n` inputs and
   `2^n` inputs, private points run out at once (`private_reach`): the diagonal at one input length reaches only
   polynomially many devices in the input count, counting reaches all. That is why the diagonal is a tool against
   uniform machines (countably many, each met at its own input length) and not against circuits.
2. Naming the function counting promises is the range avoidance problem (cited: Korten 2021). The halving witness
   needs a majority count over all devices at each point. This is how the known explicit bounds above NP are
   obtained: Kannan 1982 (Σ2 ∩ Π2 has no circuits of size n^k) and the near-maximal bounds for S2E (cited: Chen,
   Hirahara, Ren 2024; Li 2024). The witness lands in the class that can do the counting, which is above NP. This
   is the gap `halve_not_mem` shows in miniature: explicit, at the price of a count.
3. The diagonal uses the devices only through their input/output table: `diag_explicit` is uniform in `e`. Any
   argument of that kind holds with an oracle added to both sides, and there are oracles with P = NP and with
   P ≠ NP (cited: Baker, Gill, Solovay 1975; L-lib-061, L-lib-062 in this repository are the checked rows). So it
   cannot decide the question. Algebrization extends the obstacle (cited: Aaronson, Wigderson 2009).
4. The third engine, potentials on a named function, is neither. Its obstacles are different: gate elimination has
   given only linear bounds for general circuits (cited; about 3.1n), monotone bounds do not transfer because
   negations help (cited: Razborov 1985 and Tardos 1988 for the gap; Wegener 1987 §6.7 for these very sums, via
   LIT2), and a potential that is efficiently computable and holds for most functions is ruled out for strong
   bounds if pseudorandom functions exist (cited: Razborov, Rudich 1997). Whether the payment potential is "natural"
   in that sense was not examined here.

This is a map of where the difficulty is. It is the standard picture; only the four Lean rows are new to the
repository.

### C1. Views embed in families; families do not embed in views (checked)

Candidate (c): is there one poset of "views" with the non-injectivity theorems as arrows, descriptive complexity
included? Half yes, half no, and the no is the informative half. `Unify.lean`, Part C.

* A **view** of `X` is an equivalence relation (what a projection forgets). A **family** is a set of properties of
  `X` (what a logic or a class can say). `viewOf F`: points no property of `F` separates. `famOf r`: properties that
  respect `r`.
* `view_family_galois`: `r ≤ viewOf F ↔ F ⊆ famOf r`.
* `viewOf_famOf`: `viewOf (famOf r) = r`. **Every view is a family.** The repository's non-injectivity theorems live
  here, as strict arrows in the lattice of views: `one-not/lean/PEqualNP/Philosophy/Bridge.lean::PhiT_not_injective`,
  `corners_not_injective` (slack table → Φ), `Deleuze.lean::actual_not_injective`,
  `Philosophy/Unify.lean::collapse_iff_injective`. The levels (finite → polynomial → limit) are views. Their
  formalization as projections belongs to the methods seat (`lean/PEqualNP/Methods/`), not to this file.
* `viewOf_eq_bot`, `same_view_of_singletons`, `family_not_determined`: any two families that contain every singleton
  have the same view, equality. **Not every family is a view.**
* `p_np_same_view`: if every one-string language is in P (standard; a hypothesis here) then P and NP induce the same
  view of binary strings whether or not P = NP.

So the logics of descriptive complexity (`Worlds/Descriptive.lean`: FO, FO(LFP), ∃SO) are families, not views: on
finite structures every one of them already separates all points (cited: each finite structure is fixed up to
isomorphism by one first-order sentence). "The language seen through a logic" loses nothing pointwise; what differs
is which infinite sets of points are definable. P versus NP is a question about two families with the same view. It
is not a non-injectivity statement, and no theorem about what a projection forgets can bear on it. The poset of
views has content for the levels and none for P versus NP.

### D1. The payment rank is not a min-cut function (checked; tested)

Candidate (d), the part that is a theorem. `Unify.lean`, Part D, with `Philosophy/BeauvoirQG.lean`.

* `par`: the rank of three parallel payers (three gates that can each make the same one merge). `par_mono`,
  `par_submodular`, `par_unit`: it is a monotone, submodular, unit-increment rank.
* `par_not_mmi`: it violates monogamy of mutual information, `r(a)+r(b)+r(c)+r(abc) ≤ r(ab)+r(bc)+r(ac)` (4 ≤ 3).
* `parallel_payers_not_cut`: no weighted graph, boundary and three disjoint regions have these seven min-cut
  values. It is `BeauvoirQG.no_network_has_ghz_entropies` at `k = 1`: the seven numbers are the four-party GHZ
  entropies, and min-cuts obey `rt_mmi`.

Tested (`unify_rank.py`, same 21 circuits, 3,982 triples of payers): the Lemma D potential violates the monogamy
inequality in 13 of 21 circuits (293 triples); its unit truncation (the matroid union rank) in 2 of 21 (2 triples).

What is shared is one level down and is standard: matroid ranks, Shannon entropies (cited: Fujishige 1978) and min-cut
functions (`rt_submodular`) are all submodular. What is not shared is monogamy. Payment ranks sit with GHZ-type
correlation (many payers holding the same merge), which is exactly what a network of cuts cannot hold.

---

## Part 2. Structural analogies (labelled; no theorem claimed)

* **CKW monogamy and PHC as "one unit split between several".** `QuantumGravity/Open/CKW.lean::ckw`:
  `τ_AB + τ_AC ≤ τ_{A|BC}` for every pure three-qubit state. PHC: each gate pays for at most one set. The shape
  matches the *trivial* half of PHC only. CKW is a constraint that every state satisfies; its payment counterpart is
  `unsplit_of_partition` (every partition obeys the count). The content of PHC is the converse, an existence
  statement (some partition reaches the count), and the CKW counterpart of that would be realizability: every pair
  of tangles with sum ≤ `τ_{A|BC}` occurs. For three qubits that looks easy on paper (W-class states
  `a|100⟩ + b|010⟩ + c|001⟩` give `τ_AB = 4a²b²`, `τ_AC = 4a²c²`, `τ_{A|BC} = 4a²(b² + c²)`, equality with any
  ratio), not checked. Tangle is not an entropy and not a rank; no map carries one inequality to the other.
* **Shannon, Knill, L119 and base as "bounded increment per gate".** A1 makes the shared part a theorem
  (`lip_count`) and it is thin. The measure-theoretic content of L115 to L119 and the combinatorial content of the
  flip lemma are unrelated.
* **Levels as projections and logics as projections.** The first is a view (C1). The second is a family. The common
  word "projection" covers a quotient in one case and a sublattice of definable sets in the other.
* **The DAG frame (`Philosophy/DAG.lean`, `Philosophy/Unify.lean::permanence_iff_no_reconciliation`) and the split condition.**
  Both say "a loss is permanent iff no later join recovers it" in a lattice. In the DAG it is a statement about a
  partial order of states; in A1 the tight sets of the split condition form a lattice (F1 remark b). Same algebra
  (meets and joins), no common theorem.
* **Lawvere in philosophy (`Lateral/CamusInstance.lean`) and in complexity (B1).** One checked spine, two modelling
  choices. The spine is the join; the readings are not.
* **Ryu–Takayanagi min-cut and matroid partition as min–max theorems.** Max-flow min-cut and Edmonds' partition
  theorem are both instances of polymatroid intersection (cited: Edmonds 1970). True in the literature, at a level of
  generality where nothing specific to either program survives. D1 shows the two rank functions are different.

---

## Part 3. Rhymes that fail, and why

| Rhyme | Why it fails | Evidence |
|---|---|---|
| "Each gate adds at most one, so gates ≥ base" as one law for circuits and quantum counting | The increment is 1 per gate **per set**; summed over sets it is not bounded (`lip_sum`). True for one set, false for families at scale | LIT2 (AG(2,8), 261 < 448); `lip` 2 to 6 on all 21 stored circuits |
| PHC for every number of NOT gates as the unifier of one-NOT and several-NOT | PHC@0 for all point programs is false (Lemma D at `J = ∅`), and "every k" is false on large planes. What survives: one NOT (open), two-set forms (not refuted) | LIT2; commit 7816443 |
| Payment is monogamous like entanglement | Monogamy of mutual information fails for payment ranks; three parallel payers are the GHZ pattern, which no cut network realises | `par_not_mmi`, `parallel_payers_not_cut`; 293 triples in 13 stored circuits |
| CKW "is" the payment Hall condition | Opposite logical direction (a constraint on all states against the existence of a partition); tangle is neither rank nor entropy | Part 2, first item |
| Counting bounds say which unitary or function is hard | They compare a class with a space; the witness costs a count over the class | `count_exists` against `halve_not_mem`; L119 names no unitary |
| The diagonal can separate circuit classes at one input length | Private points: at most as many devices as inputs | `private_reach` |
| P versus NP is about what a projection forgets (levels, Bridge, "the virtual") | P and NP have the same view; they differ as families | `p_np_same_view`, `same_view_of_singletons` |
| Descriptive complexity is a fourth level above finite, polynomial, limit | Logics separate all finite structures; they are not coarser views of anything in the level chain | C1 |
| One category containing all four programs | The honest common structure is "monotone functions on a finite Boolean lattice, some submodular". Everything specific (matroid, measure, fixed point, quotient) lies outside it | Parts 1 and 2 |

---

## Unfinished (stopped here for the repository refactor)

* `p_np_same_view` carries the hypothesis "every one-string language is in P". Standard; not proved against
  `Defs/Base.lean`'s `P`.
* The counting instances of A1 are readings. No Lean theorem derives a statement of L002, L116 or L119 from
  `lip_count`. A dimension-of-image potential for products of two-qubit gates would make the L119 instance literal.
* The converse of `unsplit_of_partition` (Edmonds' matroid partition theorem) is cited. Mathlib has matroids and no
  matroid union.
* CKW realizability for W-class states (Part 2) is a paper computation, not checked.
* The LIT2 reading in A1 (the truncation is strictly below `f` on AG(2,8)) was not computed: 261 lines is far above
  the script's cap of 20 payers. `count_of_unsplit` gives it from LIT2's count.
* `unify_rank.py` uses one instance form (single point 0, wire classes). BottomPay's instance at `1_Q` was not rerun
  in the truncation form.
* Whether the payment potential is a natural property in the Razborov–Rudich sense: not examined.
* Citations in B1 are from memory (MEM), none reopened; rows were not added to `LITERATURE.md`.

OPEN lines for Fables are on BOARD.md under FLAGSHIP.

## Reproduce

```
cd lean && PATH=$HOME/.elan/bin:$PATH nice -n 19 lake build PEqualNP.Worlds.Unify
python3 -I math/worlds/unify_rank.py one-not/data/witnesses/*.json one-not/data/witnesses/nonlocal/general*.json
```
