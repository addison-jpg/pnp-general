# B5: S3(b), the flip-class Hall condition across sets

Seat B5 (Opus), task board `boards/tasks/open-many-not.md`. Words: **checked** = Lean accepted it;
**paper** = proved here, not in Lean; **exact SAT** = a solver answered UNSAT on a stated finite
instance (computer-assisted, not kernel-checked); **tested** = ran on data. Nothing here settles P versus NP.

Files: `B5_flip_hall.py` (Hall on stored circuits), `B5_thin_slp.py` (the function-level SAT, section 4),
`B5_triple_sat.py` (the earlier, narrower SAT for triples), `one-not/lean/PEqualNP/W951/Open/FlipHall.lean`.

## 0. Answer

1. No break. On every stored circuit with at most 24 inputs, including the C4w counterexamples t4, t5, t6
   and the 10-gate `general_count_below_base_min`, the Hall condition holds on every subfamily. The t4..t6
   circuits are tight (6 classes for base 6, no class shared between the two sets).
2. **Proved (paper, with the core in Lean):** S3(b), Hall form, for every system of at most two sets of size
   at most 3, for every circuit with any number of NOT gates and any number of gates.
3. **Proved by exact SAT, for every circuit (any size, any number of NOT gates):** S3(b) in Hall form on
   every subfamily of two triples (shared point or disjoint), triple + 4-set (both ways), star44 (the system
   of the t = 4 break), tri3, star3, tri4, q4, Pasch (section 4 lists runs and controls). These are
   statements about Boolean functions only; no circuit size bound enters.
4. **The smallest exact missing statement** (section 5): the *thin-basis lemma*: a family `W` of ORs cannot
   be computed by `base(W) − 1` binary AND/OR lines over `W`-thin functions. It implies S3(b) for every
   number of NOT gates and every circuit size, and its one-set case is S3(a).

## 1. The statement and two remarks

For a set `S` and a zero point `Z` of `S` (`Z ∩ S = ∅`): `D_S(g, Z) = {u ∈ S : g(Z + e_u) ≠ g(Z)}`.
`C(w)` = the classes (wire functions up to complement) with `|D_{S_w}(g, Z)| ≥ 2` for some zero point `Z`
of `S_w`. A function is **`S`-thin** if `|D_S| ≤ 1` at every zero point of `S`; **`W`-thin** if `S`-thin for
every `S ∈ W`.

**S3(b), Hall form.** For every family `W`: `|⋃_{w∈W} C(w)| ≥ base(W) = Σ_{w∈W}(|S_w| − 1)`.

*Remark 1 (Hall form = (b) on subsystems).* Dropping the outputs not in `W` leaves a correct circuit for `W`,
whose flip classes are exactly `⋃_{w∈W} C(w)`. So Hall form for all `W` is (b) for every subsystem.

*Remark 2 (scale).* Classes ≤ AND/OR gates. S3(b) with no bound on t, on projective planes
(`base ≈ n^{3/2}`), is a superlinear lower bound for all circuits for an explicit function, open since the
1970s. A proof for all systems at all t is not expected; every result below is for fixed small systems, or
a reduction.

*Remark 3 (outputs are private; checked).* The output of `T` is `S`-thin when `|S ∩ T| ≤ 1`
(`FlipHall.dset_orS_le`): at a zero point of `S`, only a point of `S ∩ T` can flip `OR(T)`. So the output
class of `w` lies in `C(w)` and in no other `C(v)`. Hall therefore holds with `|W|` on the right, and exactly
for sets of size 2; it reduces to the *non-output* classes `X(w) = C(w) \ {out_w}`: Hall ⟺
`|⋃ X(w)| ≥ Σ (|S_w| − 2)` for every `W`.

## 2. Attack on the stored instances

`python3 -I one-not/research/open/B5_flip_hall.py FILE.json …` computes `C(w)` for each set (bit-parallel,
every wire, every zero point) and the least Hall margin over all subfamilies.

| circuit | n | gates | NOT | base | per-set \|C(w)\| | classes | shared | Hall min |
|---|---:|---:|---:|---:|---|---:|---:|---:|
| general_count_below_base_min (C4w, 10 gates) | 7 | 10 | 4 | 6 | 3, 3 | 6 | 0 | 0 |
| general_count_below_base_t4 | 7 | 67 | 4 | 6 | 3, 3 | 6 | 0 | 0 |
| general_count_below_base_t5 | 7 | 52 | 5 | 6 | 3, 4 | 7 | 0 | 0 |
| general_count_below_base_t6 | 7 | 65 | 6 | 6 | 3, 7 | 10 | 0 | 0 |
| fano_formula | 7 | 17 | 1 | 14 | 2 ×7 | 14 | 0 | 0 |
| pasch_s14_heavy_atmostone | 6 | 14 | 1 | 8 | 2 ×4 | 8 | 0 | 0 |
| ess_rand_clean_744 | 5 | 9 | 1 | 5 | 1, 3, 1, 3 | 6 | 2 | 0 |
| see_gap_n5 | 5 | 11 | 1 | 5 | 2, 5, 2 | 7 | 2 | 1 |
| tri_all_5593 | 6 | 15 | 1 | 8 | 6 ×4 | 14 | 6 | 4 |
| other 10 files in `one-not/data/witnesses/` (n ≤ 9) | | | 0–1 | | | | | ≥ 2 |

Larger stored circuits (one NOT gate each, the refuted-step rows), all subfamilies:

| circuit | n | sets | base | classes | Hall min |
|---|---:|---:|---:|---:|---:|
| twin_tree_and2 / _or2 / _maj3 | 14 | 5 | 15 | 21 | 5 |
| twin_tree_e0 | 14 | 5 | 15 | 23 | 5 |
| twin_tree_f2step / twin_tree_N_f2step | 14 | 5 | 15 | 21 | 5 |
| twin_tree_k5_c3 | 22 | 7 | 25 | 35 | 6 |
| match_c_k7 / match_s_k7 | 16 | 11 | 23 | 40 | 0 (at a pair) |
| match_c_k11 (n = 24), match_c_k16 (n = 34) | | | | | not run (n = 24 did not finish in 10 min; 34 too large) |

The C4w break (witness count 5 < base 6 at t = 4) does not carry over to flip classes: the falling
merges that the witness count misses are exactly counted as classes, and the two sets share none.

## 3. Two sets of size at most 3 (paper; core checked)

**Theorem.** Let the system have at most two sets, each of size at most 3 (pairwise intersection ≤ 1).
Every correct circuit, with any number of NOT gates, satisfies S3(b) in Hall form.

*Proof.* By Remark 3 only two triples `S, T` need an argument, and Hall can only fail if
`X(S) = X(T) = {Y}` for one class `Y` (each `X` is non-empty by S3(a)). Then at every zero point of `S` the
classes with `|D| ≥ 2` are `out_S` and `Y` only (S3(a) needs two), and the same for `T`.

Let `g` be the first wire whose function is `±OR(S)`. It is not an input (`|D| ≤ 1`) and not a NOT gate (its
input would have the class earlier), so `g = A op B` with `A, B` earlier wires or constants, neither of class
`out_S`. At every zero point `D(g) = S ⊆ D(A) ∪ D(B)`, so one of `A, B` has `|D| ≥ 2` there and has class `Y`.
Both cannot (then `g ∈ {Y, ¬Y, 0, 1}`), so say `A ∈ ±Y` and `B` is `S`-thin. Now:

* (`FlipHall.const_on_face`) if `±OR(S) = A op B`, `B` is `S`-thin, `|S| ≥ 2` and `A ∉ ±OR(S)`, then `A`
  is constant on the zero face `F_S`. The four cases of (op, sign) put `A` constant on `F_S` or constant
  off `F_S`; in the second case `D(A) ∈ {∅, S}` at each zero point, `B` cannot cover `S` alone, so
  `D(A) = S` everywhere and `A = ±OR(S)`, excluded.
* (`FlipHall.no_sole_partner`) then `T`'s first output wire is `(±A) op' B'` with `B'` `T`-thin; at the
  all-zero point `Z₀ ∈ F_S ∩ F_T`, every `u ∈ T \ S` keeps `Z₀ + e_u` inside `F_S`, where `A` is constant, so
  `D_T(A, Z₀) ⊆ S ∩ T` and `|T| ≤ |S ∩ T| + 1 ≤ 2`, a contradiction. ∎

Lean: `one-not/lean/PEqualNP/W951/Open/FlipHall.lean` (functions `(Fin n → Bool) → Bool`; axioms propext,
Classical.choice, Quot.sound): `dset_orS_le`, `cover`, `off_face`, `const_on_face`, `no_sole_partner`. The
step from a circuit to "first wire of the class = `A op B` with `B` thin" (the paragraph above) is paper;
`FlipLemma.Concrete` has the wire semantics it would use.

## 4. The thin straight-line program, and exact SAT on small systems

**Relaxation (paper).** Fix `W` and let `K = ⋃_{w∈W} C(w)`. A wire whose class is not in `K` is `W`-thin.
The first wire of a class in `K` is an AND/OR gate (not an input, not a NOT gate) whose inputs are each
`W`-thin, a constant, or `±` the first wire of an earlier class in `K`; every output is `±` such a first
wire. So a Hall violation on `W` gives a **straight-line program of `base(W) − 1` lines
`F_i = L_i op_i R_i`, each `L_i, R_i` an arbitrary `W`-thin function or `±F_j` (`j < i`), with every
`OR(S_w)`, `w ∈ W`, equal to some `±F_i`.** No circuit size and no NOT count enters: thin functions are
free. `B5_thin_slp.py` encodes exactly this (truth tables as variables, one CNF per family) and asks
CaDiCaL. UNSAT on `W` ⇒ no circuit at all violates Hall on `W`.

Controls: with `base(W)` lines (`--control`) every family tested is SAT (two3, dis3, one4, tri3 … as run).

| system (n) | sets | families tested | result |
|---|---|---:|---|
| two3 (5; +2 free inputs) | 012, 034 | 3 | all UNSAT |
| dis3 (6; +1) | 012, 345 | 3 | all UNSAT |
| two43 (6; +1) | 0123, 045 | 3 | all UNSAT |
| dis43 (7) | 0123, 456 | 3 | all UNSAT |
| dis44 (8) | 0123, 4567 | 3 | all UNSAT (1.6 s) |
| star44 (7; +1), the t = 4 break | 0123, 0456 | 3 | all UNSAT (3.6 s) |
| tri3 (6) | 013, 124, 025 | 7 | all UNSAT |
| star3 (7) | 012, 034, 056 | 7 | all UNSAT |
| tri4 (6) | 0134, 125, 02 | 6 | all UNSAT |
| q4 (6) | 0123, 045, 14, 25 | 12 | all UNSAT |
| Pasch (6) | 012, 034, 135, 245 | 15 | all UNSAT (full family 213 s); control SAT on all 15 |
| star5 (9), two 5-sets | 01234, 05678 | 3 | single sets UNSAT; the pair did not finish (stopped after about 20 min) |
| Fano (7), up to relabelling | 7 lines | — | not run (queued behind star5, stopped) |

So on each of these systems **every** circuit, with any number of NOT gates and of any size, has at least
`base` flip classes (hence at least `base` AND/OR gates), on every subsystem. For star44 this extends the
exhaustive `--fclasses` SAT (s ≤ 8) to all sizes; for Pasch it gives 8 AND/OR gates for all circuits, where the
partition bound (B4) gives 5.

## 5. The smallest exact missing statement

**Thin-basis lemma (open).** For every family `W` of sets (pairwise intersections ≤ 1), no straight-line
program of `base(W) − 1` binary AND/OR lines over `W`-thin functions (and `±` earlier lines) has every
`OR(S_w)`, `w ∈ W`, among `±` its lines.

* It implies S3(b) (Hall form) for every circuit, every number of NOT gates (section 4).
* Its one-set case is S3(a): `Core.core` already allows any leaves with `|D| ≤ 1`, which is what thin means.
* It is a statement about Boolean functions only: NOT gates, circuit size and the cost of the thin
  functions have disappeared. What remains is exactly the sharing question: a line can have `|D| ≥ 2` for
  several sets, at different zero points.
* Section 3 proves it when every set has size ≤ 3 and `|W| = 2`; section 4 checks it on the listed families.
* The first families not settled: Fano (7 triples, n = 7, 13 lines), two 5-sets, AG(2,3). The proof of
  section 3 uses that a triple's partner is constant on the zero face; for a 4-set the first output wire
  is `A op B` with `|D(A)| + |D(B)| ≥ 4` split 2 + 2 or 3 + 1 at different zero points, and the face
  argument has to run down a depth-2 tree. That case analysis (the 4-set step) is the next lemma.

## 6. Reproduce

```
python3 -I one-not/research/open/B5_flip_hall.py one-not/data/witnesses/nonlocal/*.json one-not/data/witnesses/*.json
python3 -I one-not/research/open/B5_thin_slp.py star44            # violation search: all UNSAT
python3 -I one-not/research/open/B5_thin_slp.py star44 --control  # base(W) lines: all SAT
python3 -I one-not/research/open/B5_thin_slp.py two3 --free=2     # extra inputs outside every set
cd one-not/lean && lake build PEqualNP.W951.Open.FlipHall
```
