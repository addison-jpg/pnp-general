# MinCE reduction lemmas (L-meta-951, lane c)
[Coord-desktop CORRECTION: scaffold showed the CLEAN selector path violates R2 (15 duplicate pairs) and R3 (4 input copies), so it is EXCLUDED from any MinCE; the 'survives' line below is superseded. R6 (rewire, general form) reduces MATCH-C 55->45 gates (cTAHG). cxMU_dd violates R+ (cTAHG).]
M0 (master): MinCE C for F, s=|C|<base(F). Any correct C' for SAME F with <=1 NOT and |C'|<s is a CE, contradicting least size. Only size needed. Base never changes: all reductions keep F. Outputs OR(S_w), |S_w|>=2: never const/variable; redirecting output pointers is safe.
SUB(E,c): replace input on a set E of (reader,port) edges by constant c; readers become aliases (AND(1,y),OR(0,y)) or constants (AND(0,y),OR(1,y),NOT c) -> removed; constants propagate; NOT count never rises. Saves >= |readers in E| >= 1.
R1 no real-constant gate. R3 no gate = x_i. R2 no two equal real functions (delete later, redirect to earlier; acyclic). R4 every gate read or output. R5 NOT present (else monotone, Wegener). R5' C_0 and C_1 both incorrect (C_b = SUB(out(N),b), size<=s-1).
R+ (observability, strongest): for every gate u, nonempty E ⊆ out(u), c in {0,1}: SUB(E,c) is incorrect.
R2+: for a wire f not depending on g, g not output: redirecting all of out(g) to f is incorrect.
R6 (rewire): rewiring an input of gate r to an existing wire f outside desc(r) that keeps correctness and frees a gate contradicts minimality.
R7 (private N-cone): g in D=desc(N), K = D∩cone(g), every k in K\{g} read only inside K; then real g != C_b(g) for b=0,1. Proof: SUB(N-edges into K, b) changes only g visibly; g becomes C_b(g)=real g; saves the N-readers in K. General form = R+ with u=N, E = edges into K, provided every wire leaving K has real = C_b. Shared case blocked: substitution changes shared exit wires; duplication may cost more than it saves.
Examples: PAPPUS-JUNK J_w = (x_c x_d x_r) ∧ N, real ≡0: R1 kills. Junk selector link with A=N∧E_{j+1} real≡0: R1 kills A.
Under F2: R1 not needed for counting; still needed: R2/R3, R4, R+/R5'.
