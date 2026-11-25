# Cosmos from the whole downward: Friedmann, orbits, and the measure problem

What this is: the flat Friedmann equation, Kepler orbits, and a toy of the multiverse measure problem, checked with exact fractions. What this is not: a new result in cosmology, or a way to compute probabilities in eternal inflation. Labels: **fact** (cited, with read status), **checked-finite** (exact, exhaustive over a stated finite set, rerunnable), **checked-infinite** (a finite check plus a written reduction), **tested** (floating point or measured inputs), **join**, **analogy**, **open**. Every number below was printed and asserted by `check.py` (`python3 -I cosmos/check.py`, under one second, Fraction arithmetic, standard library only; sympy is not installed and not used).

## 1. The Friedmann equation, flat case

H² = (8πG/3) ρ, with H = a′/a. One component scales as ρ ∝ a^(−3(1+w)).

- Try a = t^p. Then H = p/t and the powers of t match iff 3p(1+w) = 2. So p = 2/(3(1+w)) for w ≠ −1. The algebra is in the docstring of `check.py`.
- Matter (w = 0): a ∝ t^(2/3). Radiation (w = 1/3): a ∝ t^(1/2).
- Checked-finite: for 112 rational w in (−1, 3], the monomial algebra gives H² a^(3(1+w)) = p², a constant. It is also evaluated at rational times t = u^den(p), u ∈ {2, 3, 5, 1/2, 7/3}, exactly.
- Checked-infinite: the same for every w > −1, by the written reduction.
- Cosmological constant (w = −1): a = e^(Ht). Checked-finite: the series coefficients satisfy (k+1)c_(k+1) = H c_k to order 40, for 4 rational H.

## 2. Deceleration

q = −a a″/a′².

- One component: q = (1+3w)/2. Checked-finite on the same 112 values of w. For e^(Ht), q = −1 (series to order 40).
- Matter plus Λ: q = 0 exactly at a³ = Ω_m/(2Ω_Λ). Checked-finite on a rational grid of four Ω_m: q > 0 before, q < 0 after.
- Tested: finite differences of a(t) for Ω_m = 0.315 put the sign change at a = 0.612628, as the formula does.

## 3. The age of the universe (tested)

t0 = (2 / (3 H0 √Ω_Λ)) asinh(√(Ω_Λ/Ω_m)) for flat Λ-CDM without radiation.

- Fact: the formula appears in this form, or in equal arctanh and log forms, in several reviews (search result only; e.g. arXiv:2103.15825, arXiv:0801.0552).
- Fact: Planck 2018 gives H0 = 67.4 ± 0.5 km/s/Mpc and Ω_m = 0.315 ± 0.007 (Planck Collaboration, A&A 641, A6 (2020), arXiv:1807.06209; search result only).
- Computed: t0 = 13.796 Gyr by the closed form, the same by quadrature, and a(t0) = 1. The published value is about 13.8 Gyr (from memory; the search did not show the paper's age line).

## 4. Orbits: gravity as inevitability

A body is bound iff E = v²/2 − GM/r < 0.

- Checked-finite: on a grid of 1944 rational states (μ = 1, coordinates in steps of 1/2, |r| rational), e² is computed from the eccentricity vector. For every state with h ≠ 0, e² < 1 iff E < 0 and e² = 1 iff E = 0. Counts: 368 bound, 32 parabolic, 1376 open, 168 radial (h = 0, all with e² = 1).
- Checked-infinite: e² = 1 + 2Eh²/μ² (written in the docstring); the grid confirms it state by state.
- Analogy: `gravity.ath` shows every escape route in an essay returns. Here every state with negative energy closes. Same shape of argument, different objects.

## 5. The measure problem, in a toy

Universes are the positive integers. The property is "even".

- Ordering A: 1, 2, 3, … The frequency among the first N is ⌊N/2⌋/N → 1/2.
- Ordering B: blocks (4k−3, 4k−1, 2k): 1, 3, 2, 5, 7, 4, … It lists every positive integer once. The frequency is ⌊N/3⌋/N → 1/3.
- Checked-finite: both formulas, with error at most 2/(3N), for every N ≤ 3000. Universe 2k sits at place 3k (k ≤ 12; in `fingerprints.json`).
- Checked-infinite: the limits, by the bounds written in the docstring.
- Same set, same property, two answers. The answer depends on the cutoff.
- Fact: in eternal inflation the number of observers is infinite, so relative frequencies depend on how the infinity is regulated; the regulator is called a measure (Freivogel, "Making predictions in the multiverse", arXiv:1105.0244; search result only).
- **Open**: which measure is right. Exact probability in asteroid makes finite probability claims checkable. It does not make the infinite measure problem tractable.

## 6. In asteroid

`cosmos.ath` runs `check.py`, reads the place sequence, and states the two cutoffs at N = 6 as finite distributions: P(even) = 1/2 under A and 1/3 under B (checked-finite: the support is exactly the six universes). The new lines (`dist`, `claim prob`, `claim expect`, product) are in `asteroid/ext_prob.py` and `asteroid/SPEC.md`.

## 7. A postmodern history of the universe, along time

Source: Addison, 2026-11-25 (ontology/SOURCES.md). Reading, not proved.

- Fact (search result only): Lyotard, *La Condition postmoderne* (1979; English 1984) defines the postmodern, simplifying to the extreme, as incredulity toward metanarratives.
- Reading: the standard cosmological history (one line from the Big Bang to now) is a metanarrative. Read with Lyotard, history need not be one line.
- The repo's position: a history can be a DAG with branches that rejoin (`DAG.lean`), not one line. The measure toy (section 5) shows that the "probability of a history" depends on the ordering.
- If this held, what would propagate to the multiverse: only claims whose hypotheses hold there (the transport rule, `homestuck/BASE.md` section 5). A claim that holds in every ordering and every branch needs no chosen history, so it is exactly the kind that crosses.
- Checked-finite (`cosmos/invariant.py`): for n ≤ 7 universes, over all orderings and all properties, a property's frequency is the same at every cutoff in every ordering iff it holds everywhere or nowhere. Example on the toy: "n² mod 4 is 0 or 1" holds for every universe, so its frequency is 1 at every cutoff N ≤ 3000 in both orderings A and B. Evenness does not cross: 1/2 against 1/3.
- Open: whether any non-trivial physical statement is history-independent in this sense.
