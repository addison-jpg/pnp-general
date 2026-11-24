# fj_fable.md — attack on CONJECTURE FJ (restart-safe log). Code: w9/fj/ (fjall.py = one SAT call per system for ALL h; enumrun.py)
Tags: PROVED (paper, by me, not second-checked) / CHECKED (code) / CONJECTURE / REFUTED.
Notation: M monotone circuit over (x,y); F_w outputs; g^0 = g(.,0) <= g^1 = g(.,1); o_w = OR(S_w); d_w = |S_w|-1; base = Σ d_w;
z_w = 1 outside S_w; p_w(x) := F_w(x with S_w:=0, 1) (monotone, independent of S_w) = "false-positive part" of world 1: F_w^1 = o_w ∨ p_w.

## F1 PROVED: h-free form of FJ (h is determined by the circuit; valid h form an interval)
M is FJ-valid for h  <=>  for all w,x:  F_w(x,0) <= o_w(x) <= F_w(x,1),  h(x)=1 => F_w(x,0)=o_w(x),  h(x)=0 => F_w(x,1)=o_w(x)
 <=> M(x, ¬h(x)) = o(x) for all x ("one FREE antitone oracle input").   [F^0<=o follows: h(x)=0 gives F^0(x)<=F^1(x)=o(x).]
Let E1 = {x : some F_w(x,1) ≠ o_w(x)}, E0 = {x : some F_w(x,0) ≠ o_w(x)}. A monotone h is valid iff E1 ⊆ {h=1} ⊆ E0^c. Hence
 (a) valid h's = the interval [H_min, H_max], H_min = 1_{↑E1} = OR_w p_w, H_max = 1 - 1_{↓E0};
 (b) FJ <=> (FJ'') every monotone M with F_w^0 <= o_w <= F_w^1 and  F_w'(x,0) >= o_w'(x) ∧ p_w(x)  for ALL pairs (w,w') has >= base gates.
 (c) "finite family of extreme h": none is needed — h can be existentially quantified inside ONE SAT instance (h(x) = 2^n extra variables with
     monotonicity clauses). fjall.py does this: FJ for a system is decided for ALL h by one call.
 Consequence of the oracle form: every 951 argument that works with real functions and never uses "h is a wire before N" transfers to FJ;
 arguments that toggle x_v and say "no wire changes" do NOT transfer verbatim (y = ¬h(x) may change) and need F^0 <= o <= F^1 instead.

## F2 CHECKED (fjall.py/enumrun.py; all h at once, UNSAT at base-1 gates)
 all 63 iso classes of (1,1)-disjoint systems with n <= 5, base <= 7 (2 s total); Pasch (2 s); {0123},{045},{146},{256} (n=7, base 9; 51 s);
 K4; {0123}+4 pairs through 4.   n <= 6, base <= 9 (454 classes): see below.
