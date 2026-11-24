Serves C4, T6 (task beyond-one-not)

# Beyond one NOT gate: the next rungs, what the tools reach, where it stops

Research agent of main, 2026-11-24. Words used: **paper** = proved here on paper, not in Lean; **tested** = ran, counts given;
**open** = a statement nobody has proved or refuted. Nothing here says that P versus NP is settled or close.
Program: [`asteroid/programs/beyond_one_not.ath`](../asteroid/programs/beyond_one_not.ath). Scripts:
`one-not/tools/beyond_one_not/`. Data: `one-not/data/beyond_one_not/`.

## Answer in five lines

1. Yes. One NOT gate is rung 1: an exact LINEAR bound (`gates ≥ base`) in a model far weaker than all circuits. The rungs above it are `BoolSumNot t` (Lean: `General/BoolSum.lean`), all open for t ≥ 2; rung 1 itself still has one open step (`no_minCE`).
2. What exists now reaches three things above rung 1: exact finite data (no circuit below `base` with ANY number of NOT gates on five small systems, 0 hits in 2.25 million hunt moves at t = 2, 3, 99), one small lemma that holds on every rung (S3a below, paper), and one weak bound that holds on every rung (S5, paper).
3. No saving was seen at any t. NOT gates cost: the smallest circuits met with t NOT gates that cannot be removed have base + 2 (t = 1), base + 3 (t = 2, SAT seat) and base + 3 (t = 3) gates.
4. Every argument that treats the 2^t worlds one at a time is void at t = ⌈log₂(n+1)⌉ (the worlds can be the n + 1 weight levels) and is already below n at t = 1 on the designs computed (W1 = 2, 6, 16 against base 14, 39, 84). A bound has to count ACROSS worlds; for t = 1 that is the certificate game, and nobody has its t-world form.
5. The top rung on dense designs (`base` ≈ n^{3/2}) would be a superlinear bound for all circuits. None is known for any explicit function (best about 3.1 n), and this route gives no reason to expect one without a new idea. The first step to take is S3 (the flip-classes count), because its first half is certain and cheap and its second half is one clean statement.

## The five statements

Notation: S_1 … S_m ⊆ {1 … n}, |S_w| ≥ 2, |S_v ∩ S_w| ≤ 1; `base` = Σ(|S_w| − 1); a circuit has fan-in-2 AND and OR gates and NOT gates, every gate counted, output w = OR of S_w. A **zero point** of S is an input Z with Z ∩ S = ∅. A **face** of a circuit with t NOT gates is the monotone circuit got by replacing each NOT gate by a constant (2^t faces).

| Rank | Name | Statement | Status | Value | Chance | Cost |
|---:|---|---|---|---|---|---|
| 1 | S3 `FlipClasses.local` (a), `FlipClasses.count t` (b) | (a) at every zero point of every set, at least \|S\| − 1 flip classes; (b) at least `base` flip classes in all | (a) paper, any t; (b) open, tested | (b) is `BoolSumNot t` for every t | (a) 1; (b) unknown, may fail for large t | (a) low; (b) high |
| 2 | S5 `Worlds.worldBound` | #AND/OR gates ≥ the largest base(Q, R) of a subcube on which the NOT outputs are constant | paper, any t; weak | defines the t-world game; shows what one world cannot give | 1 | low |
| 3 | S1 `BoolSum.BoolSumNot 2` | two NOT gates save nothing | open; exact on 5 small systems | first rung above the Theorem | needs rung 1 closed first | high |
| 4 | S2 `BoolSum.BoolSumNotFree t`, `BoolSumNotSave f` | #AND/OR gates ≥ base (NOT gates free); fallback gates ≥ base − f(t) | open; tested; tight at t = 3 | the right normal form of every rung | as S1 | high |
| 5 | S4 `BoolSum.BoolSumNotLog` | rung ⌈log₂(n+1)⌉ on designs, and what it would give for all circuits | open; not expected from this route | the ceiling | very low | — |

### S3. The flip-classes count (do this first)

**Definition.** For a wire g, a set S and a zero point Z of S, D(g) = {u ∈ S : g(Z + e_u) ≠ g(Z)}. g is a **flip gate** if |D(g)| ≥ 2 for some S and Z. A **flip class** is a set of flip gates with the same function up to complement (g, NOT g and copies are one class). This is the registry entry "C4 count (flip classes)" (`one-not/tools/search/conjectures.py`, main's Sonnet A).

**(a) `FlipClasses.local` (paper; every number of NOT gates).** For every correct circuit, every set S and every zero point Z of S, at least |S| − 1 flip classes have |D| ≥ 2 at (S, Z).
*Proof.* D depends only on the class. An input has |D| ≤ 1. A NOT gate has the class of its input. For g = a AND b or a OR b, a change of g needs a change of a or b, so D(g) ⊆ D(a) ∪ D(b). Go through the wires in order and keep a graph on S in which every D met so far lies inside one connected component. When a wire starts a new class with |D| ≥ 2 it is an AND or OR gate; add one edge from D(a) to D(b) (if both are non-empty) and D(g) lies inside one component. The output has D = S, so the graph is connected on S: at least |S| − 1 edges, one per class. ∎
For one set this is no more than "a fan-in-2 circuit that depends on k inputs has k − 1 gates". What it adds: it is a statement about the counting family, it holds on every rung including all circuits, and it isolates the open part.

**(b) `FlipClasses.count t` (open).** A correct circuit with at most t NOT gates has at least `base` flip classes. Since classes ≤ AND/OR gates ≤ gates, (b) gives `BoolSumNot t` and S2. By (a), (b) is a statement about SHARING only: can one class serve two sets (at their zero points) often enough to push the total below Σ(|S_w| − 1)? In Hall's form: the sets of classes C(w) = {classes with |D| ≥ 2 for S_w} have, for every family W of sets, |∪_{w∈W} C(w)| ≥ Σ_{w∈W}(|S_w| − 1). For t = 0 this is the proof of Wegener and Mehlhorn; for t = 1 the OR-only count is the Theorem's route; the any-gate count that ignores the falling direction is refuted from t = 4 (`Cex.generalWitnessCountBelowBase`), and flip classes are exactly tight there (6 = 6).

**Literature.** Wegener 1987 Thm 6.2, Mehlhorn 1979 (TXT / CITED, LITERATURE A, C4 table): the monotone count. Nothing printed states (b) (LITERATURE C4 table: Jukna and Sergeev 2013 §7 ask the question; Blum TR24-179 names the target).

**Experiment E3.** (a): 0 failures on 18 corpus circuits and 39,363 random-walk circuits with up to 6 NOT gates (least margin 0: the lemma is tight). (b): hunts with at most 2 and 3 NOT gates, 125,616 and 134,042 mutations, 0 counterexamples, least margin 0; the old any-gate count at t = 2, 3: 137,880 and 146,714 mutations, 0 counterexamples.

**Next.** (a) into Lean (short: the graph argument over a gate list); then `flipclasses` as an asteroid term with a kernel form, and (b) run exhaustively on two triples at base + 1 and base + 2 gates (`enum_small.c` already lists those circuits: 10,350 and 1,454,812).

### S5. The 2^t worlds and the world bound

**Definition.** Let the NOT gates be N_1 … N_t in circuit order. The **world** of an input x is the vector of their outputs at x. In a fixed world the input of the next NOT gate is a monotone function of x, so every world is a convex set of inputs (an intersection of up-sets and down-sets), and the worlds are the leaves of a depth-t decision tree of monotone functions. On its world the circuit equals one face. For t = 1 this is the two-world split of the Theorem (Amano and Maruoka, Fact 3: h, C0, C1).

**`Worlds.worldBound` (paper; every t).** #AND/OR gates(C) ≥ max base(Q, R) over the subcubes (points of Q fixed to 1, of R fixed to 0) that lie inside one world.
*Proof.* On such a subcube the face is a monotone circuit computing the restricted Boolean sum (sets S_w ∖ R for S_w ∩ Q = ∅), which still has pairwise intersections ≤ 1; rung 0 (`bound_of_noNot`, checked) gives base(Q, R) gates. ∎
The subcubes are asteroid's mixed states, so "mixed slack" is already the right object: the world bound is `mslack ≥ 0` of one face at one state inside its world.

**How weak it is.** For t = 1 the worst NOT input gives exactly W1 = max over x of min(b1(x), b0(x)), b1(x) = base with the points of x set to 1, b0(x) = base with the points outside x set to 0 (b1 falls, b0 rises, so the best cut is a threshold). Computed (E5): Fano 2 of 14, PG(2,3) 6 of 39, PG(2,4) 16 of 84: below n each time. A rough count (random x; not proved) puts W1 near n log n on a plane of order q, against base ≈ n^{3/2}. With weight bands as worlds the bound is 0 at t = 2 on every system with n ≤ 7, and 0 at t = ⌈log₂(n+1)⌉ for every system: the worlds can be the n + 1 weight levels, and a level contains no subcube with two free points.

**What the certificate game becomes.** For t = 1 the Theorem does not lose anything, so its proof counts gates ACROSS the two worlds: a gate that merges two atoms of a set in one world is charged once, wherever it is used. For t worlds the missing statement is: the sets of merge gates of the 2^t faces, each on its world, have a union of size ≥ base. S3(b) is that statement written without worlds (a flip class is a merge seen from either side). The mixed step would be: at a state (Q, R) meeting several worlds, some paying step keeps the summed mixed slack; nobody has stated it for t ≥ 2, and asteroid cannot say it (WISH 3).

**Literature.** Amano and Maruoka (TXT, 1998 version): 2^{t+1} − 1 monotone functions; Blais et al. (TXT): parity of O(2^t) monotone functions; Jukna and Lingas (TXT): multiplicative loss. All lose a factor that grows like 2^t; none gives an additive count.

**Experiment E5.** #AND/OR gates ≥ worldbound on 19 of 19 corpus circuits with at least one NOT gate (it is a theorem; the test is of the code). The circuits use 2 of 2 worlds (t = 1), 3 of 4 and 4 of 8 (the hunted t = 2, 3 circuits), 8 of 16, 32, 64 (the many-NOT files).

### S1. `BoolSumNot 2`: two NOT gates save nothing

**Statement.** `PEqualNP.General.BoolSum.BoolSumNot 2` (the definition exists): at most two NOT gates ⇒ gates ≥ base. C4g(2) of the front page.

**Literature.** No printed result for one or two NOT gates on Boolean sums (LITERATURE C, C4 table; Korshunov 2003 NOT read). Sung and Tanaka (ABS): removing one NOT gate can cost exponentially for some functions, so "t + 1 from t" is not a formality.

**Experiment E1 (exact) and E2 (hunt).** `enum_small.c` enumerates EVERY circuit with at most S gates and any number of NOT gates in a normal form that loses nothing (no constant wire, no repeated function). No correct circuit with at most base − 1 gates exists for: two triples {012, 034} (base 4), triangle of triples (6), two 4-sets (6), star of three triples (6), Pasch (8). At exactly base gates every correct circuit has 0 NOT gates (54, 2,430, 2,430 circuits on two triples, triangle, star). On two triples a NOT gate that is read first appears at base + 2 (3,510 circuits); two read NOT gates do not appear up to base + 2. This agrees with the SAT seat (task c4g-two-not-gates: UNSAT at base − 1 with ≤ 2 NOT gates up to the Fano plane; minimum base + 3 with exactly two non-cancelling NOT gates) and is independent of it (enumeration, all sizes below base, any number of NOT gates). Hunt: 739,410 mutations at t ≤ 2 and 767,717 at t ≤ 3, 0 circuits below base.

**How far.** A proof needs rung 1 first. The two-world proof uses that one of the two worlds contains the zero point 0 with all its atoms or pays for it; with four convex worlds a set's zero point and its atoms can lie in three worlds. Honest estimate: not reachable before `no_minCE` is closed; the finite data can be pushed (Fano at all sizes below 14 is not done: the SAT run excludes exactly 13).

### S2. The savings function and the NOT-free form

**Statement.** `BoolSumNotFree t`: at most t NOT gates ⇒ #AND/OR gates ≥ base (NOT gates not counted). Fallback `BoolSumNotSave f`: gates ≥ base − f(t). Conjectured f = 0.

**What the right f is.** (i) Observed: f = 0, and NOT gates cost. (ii) The count behind the Theorem counts OR gates, and flip classes count AND/OR gates, so both routes prove the NOT-free form or nothing: the NOT-free form is the natural statement. It is TIGHT with NOT gates that cannot be removed: `dm3` (x0 ∨ x1 as NOT(NOT x0 AND NOT x1)) has 3 NOT gates, no correct face, no repeated function, and exactly base = 6 AND/OR gates. (iii) The literature's accountings: Morizumi, Tarui, Iwama lose 1 gate per NOT (TXT; parity, not sums); Amano and Maruoka and Blais et al. lose a factor about 2^t. With a factor-2^t loss the bound base / 2^t on a design is superlinear only while 2^t < √n, that is t < ½ log₂ n: half way to the Markov rung. With an additive loss c·n per NOT gate, base − c·n·t stays superlinear up to t = o(√n), past the top rung; no such accounting is known. (iv) Induction on t by fixing inputs until the first NOT input is constant does not work: for a threshold-like NOT input the fixing destroys a constant fraction of base (this is W1 above).

**Experiment E4.** Hunt with margin (#AND/OR gates − base), at most 2 and 3 NOT gates: 477,525 and 504,203 mutations, 0 below base, least margin 0. Least (gates − base) among circuits with exactly t NOT gates, no correct face, no repeated function: t = 1: 4 by hunt, 2 by enumeration (read NOT gate; faces not checked there); t = 2: 6 by hunt (weak), 3 by the SAT seat; t = 3: 3 (`dm3`).

### S4. t growing with n: the top of the ladder on dense designs

**Statement.** `BoolSumNotLog`: for the point-line sum of a projective plane of order q (n = q² + q + 1 inputs and outputs, base = n·q), every circuit with at most ⌈log₂(n+1)⌉ NOT gates has at least base gates. **Consequence (paper, needs a multi-output form of `Fischer.stage1`, which is checked for one output):** a circuit with s gates becomes a circuit with NOT gates only at the inputs (n of them) and 2s + n + 2 gates, so `BoolSumNot n` gives s ≥ (base − n − 2)/2 for ALL circuits; with an inverter of size O(n log n) using ⌈log₂(n+1)⌉ NOT gates (Beals, Nishino, Tanaka 1998; search result NOT read) the same from rung ⌈log₂(n+1)⌉ up to O(n log n).

**Numbers.** (base − n − 2)/2 exceeds 3.1 n from q = 8 (n = 73, base 584) and 5 n from q = 13 (n = 183). No search at n ≤ 8 touches this.

**Literature.** Markov; Fischer (checked in Lean, T6). Jukna 2004 (IPL 89; abstract only via the author's page, search result): explicit monotone multi-output functions in P need superpolynomial size with fewer than log n − O(log log n) NOT gates, so strong bounds ARE provable almost up to the Markov rung for some functions, by monotone methods, and stop there. Li and Yang 2022 (TXT): 3.1 n is the best bound for all circuits.

**Experiment.** Hunt with at most 99 NOT gates: 747,308 mutations, 0 below base. E1 is for any number of NOT gates, so on the five small systems the top rung is exact: general circuits do not beat base there.

**How far.** Not provable with what exists and not expected from this route. The statement may be false: for general (not rectangle-free) matrices cancellation beats OR by almost a factor n (Find et al.; Boyar and Find, TXT), and nobody knows whether it helps on rectangle-free ones.

## Experiments run

One process at a time; every hunt is hill climbing (finding nothing proves nothing).

| # | For | Command (repo root) | Result |
|---|---|---|---|
| E1 | S1, S4 | `gcc -O2 -o enum_small one-not/tools/beyond_one_not/enum_small.c; ./enum_small N S "SETS"` (8 runs, `enum_small.log`) | exhaustive, any number of NOT gates: 0 correct circuits with ≤ base − 1 gates on two triples (run to S = 6), triangle of triples (S = 5), two 4-sets (5), star of three triples (5), Pasch (7); at base gates all correct circuits have 0 NOT gates (54; 2,430; 2,430); two triples at base + 2: 1,454,812 correct, 3,510 with every gate read and 1 NOT gate, 0 with every gate read and 2. One run stopped at 60 s without result ({01234, 056}, S = 7) |
| E2 | S1, S4 | `python3 -I one-not/tools/search/hunt.py "Theorem: gates >= base" 45 T 11`, T = 2, 3, 99 (`hunts.log`) | 739,410 / 767,717 / 747,308 mutations, 0 counterexamples, least margin 0 |
| E3 | S3 | `python3 -I one-not/tools/beyond_one_not/experiments.py local 40 1`; `hunt.py "C4 count (flip classes)" 45 T 11`; `hunt.py "C4 count (any-gate witnesses)" 45 T 11`, T = 2, 3 | lemma (a): 0 failures on 18 + 39,363 circuits; (b): 125,616 / 134,042 mutations, 0 counterexamples; any-gate count: 137,880 / 146,714, 0 |
| E4 | S2 | `experiments.py notfree 30 T 1`, T = 2, 3; `experiments.py worlds 60 1 1`, `worlds 80 2 1`, `worlds 80 3 1` | NOT-free hunt: 477,525 / 504,203 mutations, 0 below base; least gates − base with t NOT gates, no correct face, no repeated function: 4, 6, 3 for t = 1, 2, 3 (files `essential_t*_seed1.json`) |
| E5 | S5 | `python3 -I one-not/tools/beyond_one_not/worldbound.py systems`; `… circuits` (`worldbound.log`) | W1: two triples 1 of 4, triangle 2 of 6, two 4-sets 2 of 6, Pasch 2 of 8, Fano 2 of 14, PG(2,3) 6 of 39, PG(2,4) 16 of 84; weight bands give 0 at t = 2 for all n ≤ 7; world bound holds on 19 of 19 circuits |
| P | all | `python3 -m asteroid run asteroid/programs/beyond_one_not.ath` (and `--no-lean`) | exit 0; 23 claims true; 4 kernel theorems, 3 restated in the project's definitions; 5 hunts of 6 s with ≤ 2, 3 NOT gates, no counterexample; 30 s without Lean, about 45 s with |

No counterexample circuit was found, so nothing was added to `one-not/data/witnesses/nonlocal/`.

## What the tools cannot do yet (most important first)

1. **Flip classes as a term with a kernel form**: `flipclasses(c)`, `claim forall sets forall zeros localflip(c) >= 0`, and a soundness theorem to a project definition (today only `margin["C4 count (flip classes)"]`, Python).
2. **A Lean form for `gates(c) >= base(c)` and `hypsB` with the NOT limit as a parameter t** (today `hypsB` fixes at most one NOT gate, so a hunt hit at t = 2 would be a formal counterexample to nothing; it should refute `BoolSumNot t`).
3. **Worlds**: `worlds(c)`, `live(c)`, `faces(c)`, `forall worlds mslack(c, world)`; the summed mixed slack over the worlds meeting a state.
4. **Arithmetic in terms and exact filters**: `gates(c) - nots(c)`, `corpus … where nots = T`, implication `nots(c) <= 2 -> …`, a `savings(W, t)` function.
5. **Exhaustive enumeration as a verb** (`enumerate SYSTEM upto S maxnot T`), with the kernel checking the "no circuit" answer for the smallest system.
6. **Designs as built-in systems** (`design(q)`) and a hunt that works above n = 8.
7. A circuit named `tt` breaks the generated Lean module (name clash); renamed `twotri` here.

## Barriers

- **Which rungs are below the barriers.** Up to t = log n − O(log log n) superpolynomial bounds for explicit monotone multi-output functions are proved by monotone methods (Jukna 2004, abstract only), so no barrier forbids strong bounds there. The count used here reads the inside of the circuit at Boolean points (zero points and atoms) and uses fan-in 2 (D(g) ⊆ D(a) ∪ D(b)); it does not survive a gate of large fan-in, so it is not a relativizing argument, and it is a property of one family of functions and of the circuit, not a large constructive property of truth tables, so the natural-proofs theorem (T8, `L-lib-086`) does not apply to it as stated. Being outside the hypotheses of the three barrier theorems is not evidence that the route works.
- **Where it stops, by t.** (i) One world at a time: below n at t = 1 on the designs computed, 0 at t = ⌈log₂(n+1)⌉ (S5). (ii) Any accounting that loses a factor 2^t: superlinear on designs only for t < ½ log₂ n (S2). (iii) An exact count across worlds (S3b): no loss, but its truth at t ≈ log n is the statement that all circuits need ≈ n^{3/2}/2 gates on designs.
- **The density barrier (boards/ladder.md 13:17, notes/note-3).** Gate elimination pays a constant per input, so it is linear by construction; a superlinear bound for all circuits needs a new idea exactly at density n^{1+ε}. The same shows here in two ways: the per-set lemma S3a certifies |S_w| − 1 classes for one set and says nothing about two sets, and the world bound is below n. The whole content of a superlinear bound is the cross-set, cross-world sharing statement, and at the top rung that statement is as hard as a superlinear bound for an explicit function in all circuits, which has been open since the 1970s.
- **What this is not.** `BoolSumNot t` for all t would be a bound of order n^{3/2} for one explicit multi-output function. The Millennium statement needs a superpolynomial bound for an NP problem. The ladder gives the first from the top rung and nothing toward the second.
