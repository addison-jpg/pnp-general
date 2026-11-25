# research: lower-bound tools for MONOTONE circuits computing PARTIAL functions (front §11 lifted form, coord ask)

Marked: READ = I read the statement/proof text; CITED = known from secondary source only.

1. READ. Sokolov, "Dag-like communication and its applications", ECCC TR16-202 (CSR 2017). EXACT characterization, works for
   partial functions:
   - Def 2.3: for disjoint U, V ⊆ {0,1}^n with ∀x∈U, y∈V ∃i x_i=1 ∧ y_i=0: MonBit_{U,V} = {(x,y,i) : x_i = 1, y_i = 0}.
   - Def 2.1 (boolean communication game, also Pudlák-Hrubeš): DAG H, out-degree <= 2, A : H×U → {0,1}, B : H×V → {0,1};
     v valid for (x,y) iff A(v,x) > B(v,y); root valid on all U×V; a valid inner node has a valid child; a valid leaf is labelled
     by a correct answer. Size = |H|. Equivalently each node carries a rectangle R_h ⊆ U×V with R_h ⊆ R_h' ∪ R_h'' (children).
   - Thm 3.2: a boolean communication game for MonBit_f of size S exists IFF a monotone circuit for f of size S exists
     (Lemma 2.2 direction: circuit DAG reversed, A(e,u) = gate value on u; converse builds f_h with f_h(U_h)=1, f_h(V_h)=0).
     The proof only uses U and V, so it holds verbatim for partial f (U = required ones, V = required zeros).
   Use for 951 (lifted form): fix h; output w must be 1 on U_w = {(x,y): o_w(x)=1, y∨h(x)=1} and 0 on
   V_w = {(x,y): o_w(x)=0, y∧h(x)=0}. A shared multi-root game (one root per w, rectangles U_w×V_w) is exactly a monotone
   multi-output circuit for the partial sums. Lower bound = adversary that keeps a valid path alive; Wegener's c = a∨b step is a
   rectangle argument (two zeros a,b whose join is a one). Gives a Lean-friendly target: 'every game for the lifted rectangles
   has >= base-1 inner nodes' (leaves = inputs, not counted).
2. READ. Razborov's fusion method (Jukna BFC §20.3, Lemma 20.6, Razborov STOC 1989; Karchmer 1993): uses only U = f^{-1}(0)
   and the condition f(F(x)) = 1, so it extends to partial functions, BUT it lower-bounds the number of AND gates C_∧(f).
   For Boolean sums optimal monotone circuits have no AND gates (Cor 6.1), so it measures the wrong thing for 951.
3. READ. Wegener 1987: partial functions appear as 'partially defined' (Def 1.1, Ch.2) and the merging function M_n (Def 2.1 Ch.6,
   a partial function: only on two sorted halves), whose monotone complexity Θ(n log n) is proved by elimination (§6.4). The
   replacement rules (§6.5, Mehlhorn-Galil 1976) are stated for total monotone f; Exercise 12 (p.215): g replaceable by 0 iff
   ∀t∈PI(g) ∀ monom t': t t' ∈ PI(f) - for a partial f this becomes a condition on U only, not proved in the book.
4. Not found: any Nechiporuk/Mehlhorn-type bound for Boolean sums WITH don't-care sets, in English, Russian (WebSearch) or
   RIMS sources. Monotone extensions of partially defined Boolean functions (Boros-Ibaraki-Makino) study DNF size, not circuits.
