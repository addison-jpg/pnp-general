# Task: ident-induction

- **Statement:** IDENT for a MinCE: there are inputs u, v in a common set S_w such that identifying them (x_v := x_u)
  keeps the system (1,1)-disjoint with distinct sets and makes at least one gate redundant (constant, input copy,
  duplicate, or dead) on the face x_u = x_v. Base drops by exactly 1, so a MinCE would give a smaller one: IDENT for
  MinCE => `no_minCE`. Variant IDENT+: also delete the outputs of colliding sets D, needing freed gates >= 1 + d(D).
- **Why new:** every dead induction (DEAD_ENDS family E) restricts an input to a CONSTANT; identification moves
  along the diagonal x_u = x_v (not a subcube) and always drops base by exactly 1.
- **Data (tested, not checked):** one-not/research/front612-lateral/. Plain IDENT 9,089 / 9,089 where an admissible
  pair exists; 18,899 circuits have none (dense systems: K4, fixh16, triples). IDENT+ 18,899 / 18,899, but 16,894 of
  those are plain output deletion (excluded for MinCE); identification is needed on 2,005.
- **Next:** (1) test on minimal-like circuits (R1-R6 reduced; SAT Fano 66; c3_norewire_corpus); (2) paper: (kill)
  from the first merge gate joining u, v; (adm) from MinCE facts or a choice of (u, v); (3) Lean: input substitution.
- **Done when:** a paper proof of IDENT (or IDENT+) for MinCE, or a minimal-like counterexample.
- **Owner:** open (proposed by front612, 2026-11-24).
