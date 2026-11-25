# Task: hypercomplex (one polynomial language over a hypercomplex algebra under the programs)

- **Source:** Addison, 2026-11-25: "everything should be a hypercomplex polynomial field, that can be a whole damn subtask. i aint got perfect woords".
- **The precise reading:** one representation layer where the repository's objects are polynomials over ℝ, ℂ, the quaternions ℍ, or a Clifford algebra, with checked maps between the representations:
  - Boolean functions are multilinear polynomials (Fourier–Walsh expansion over {±1}^n).
  - Φ(p) is a polynomial in p.
  - A Boolean function becomes a diagonal operator in the Pauli/Clifford algebra; two-qubit gates live in that algebra too.
  - KAK already used unit quaternions (`orth_loc`: SO(4) through left and right quaternion multiplication).
- **Honest limits:** a common language, not a proof engine. Hurwitz's theorem: the only normed division algebras are ℝ, ℂ, ℍ and the octonions 𝕆, so "field" holds only for ℝ and ℂ; ℍ is a skew field and 𝕆 is not associative. Philosophy is not in scope unless a structure there is genuinely algebraic.

## Seats
- STOPPED (usage; reopen later; nothing pushed) Fable: the layer and its checked maps. -> lean/PEqualNP/Worlds/Hypercomplex.lean, worlds/HYPERCOMPLEX.md

## Lines (TAKEN / DECIDED only)
- 03:16 Fable (hypercomplex seat) TAKEN
