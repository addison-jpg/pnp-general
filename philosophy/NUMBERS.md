# Attacks on irrational and imaginary numbers, with physics motivations

`core/ontology/FIELDS.md` proposes treating "just about everything" as a continuous field. Continuity in the strict sense needs the real numbers, and quantum theory uses the complex numbers. This file collects the strongest attacks on both, says what physics adds, and computes what can be computed (`numbers.py`, every case exhaustive, exact arithmetic). Labels: **checked-finite**, **cited** (from memory unless a read status is given), **reading** (analogy, mine), **open**.

## 1. Irrational numbers

**The attacks.**
- The Pythagorean crisis: the diagonal of a unit square has no ratio of whole numbers. Checked-finite here for every denominator up to 20,000 (`numbers.py` part 2). The proof for all denominators is the classical parity argument (cited).
- Kronecker: whole numbers are given, everything else is made (attributed remark, 1886; cited). Brouwer's intuitionism (thesis 1907; cited): a real number exists only as far as it is constructed, digit by digit.
- Ultrafinitism: numbers too large to write down have no clear meaning (cited as a position, not to one source).

**What physics adds (supports the attack).**
- A bounded region of space with bounded energy holds finitely much information (Bekenstein, 1981; cited). A typical real number has infinitely many independent digits. So no finite piece of the world can store one.
- Chaos makes this a working problem, not a metaphysical one. The doubling map x -> 2x mod 1 brings digit k+1 of the start to the front after k steps (checked-finite, every dyadic start with up to 14 digits, part 3). A chaotic system reads out ever-finer digits of its initial condition. Gisin (Erkenntnis, 2021; abstract read only) argues from this that physics should use numbers with finite information, and that the future is then genuinely open.
- Cantor's diagonal: the reals cannot be listed. Its finite form is checked here: every list of n strings of length n misses its flipped diagonal (all lists, n <= 4, part 1).

**What survives of the reals.** Calculus, continuity and the extension method of `FIELDS.md` all need R. The attack does not remove them as tools. It says a claim about all reals is infinite and needs a proof, and a physical quantity is known only to finitely many digits. That is exactly the labelling rule of this repository: Q-checks are checked-finite; claims over R need Lean or a written reduction.

## 2. Imaginary numbers

**The attacks.**
- The name: Descartes called them imaginary (*La Géométrie*, 1637; cited), as a dismissal.
- The reply in mathematics (Wessel 1799, Argand 1806, Gauss; cited): i is a quarter turn. Checked-finite here: a + bi -> [[a, -b], [b, a]] is an exact copy of the complex numbers inside real 2x2 matrices on every Gaussian integer with |a|, |b| <= 6, and i goes to a rotation J with J^2 = -I (part 4). Nothing imaginary is needed to define them.

**What physics adds (defeats the stronger attack).**
- The weak attack ("complex numbers are just pairs of reals") is true, as part 4 shows. The strong attack ("quantum theory could use real numbers only") was tested. Renou and colleagues (*Nature* 600, 2021; cited from memory, not re-read) showed that quantum theory over the reals, with independent sources in a network, predicts different correlations from standard quantum theory. Experiments reported in 2022 (cited, not read) agreed with the complex theory. So for quantum physics the complex structure is not optional bookkeeping.

## 3. The reading

- Irrationals: physics sides with the attack. Real numbers are an idealisation; physics touches finitely many digits, and chaos shows why that matters.
- Imaginaries: physics sides with the numbers. They are geometry (a rotation), and quantum theory needs them in a testable way.
- For this repository: compute on Q, prove on R, and treat the complex numbers as rotations when exact arithmetic is needed. Reading, not a result.

## Open

1. Re-read Renou et al. 2021 and the 2022 experiments, and record read status.
2. A small exact model of the real-versus-complex network test (the state and measurements are finite-dimensional), if one can be stated exactly.
3. Gisin's finite-information numbers as a data type for asteroid's continuous extension (`FIELDS.md`), with what survives.
