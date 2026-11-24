# scaffold Fable agent: constructive attack on free-choice FracMatch (Nov 24 04:55)
Status: REFUTATION FAILED. No circuit with L* > 1; nothing against 951. Best L* 0.50 after ~5,000 valid
nsets-BAD neighbours (hill-climb with non-saturating overload objective from cx1/cx2/cx3/v1); v1.json (AND-cut + U-only
W-chain, s=26, BAD) has L* 0.316.
Constraints any counterexample must meet (hand proofs unless noted):
1. Output privacy: o_S counted by S in every test system and by no other set (0 violations / 1,541 circuits) => size-2 sets
   irrelevant; graphs cannot refute FracMatch; triples need 1 non-output gate, quads 2.
2. L*=1 forced sets cannot be pushed above 1 (their gates are <= OR(T), never counted by another set's (z=0, unit) system).
3. (z=0, units) is always Good => a counterexample violates Hall there; N-hidden AND-cut forced.
4. Monotone circuits satisfy Hall at z=0 => junk alone never helps; sharing must be hidden behind N.
5. One-world families die (all h <= OR(S); or all hard sets avoid a common minterm M). h = OR(H), >= 3 sets: fat atoms separate pairs.
6. Two quads, h = a1∨a2∨b1∨b2: "corner" systems always give a full matching (non-rigorous; 38,199 mutated circuits, 0 failures).
Why: each gadget hides its chain in one world; the set moves its zero point to the other world where the chain is pure;
sharing it needs free elements outside H, which hand the other set a corner system.
Untested lead: h with non-singleton mutually absorbing minterms (e.g. h = pq ∨ rs) and >= 3 sets of size >= 3 (one >= 4,
given T1) with cyclically incompatible separations.
Full: scaffold-951 work/notes951/fable_fracmatch_attack.md + scripts/fable_attack/.
