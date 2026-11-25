import PEqualNP.Defs.General

/-!
# Fischer's construction, part 1: straight-line circuit building and dual rail

Infrastructure for building circuits with sharing (gate lists to which gates are appended, each
gate reading earlier wires), and the dual-rail translation (Markov 1958, Fischer 1975): given the
negations of the inputs as wires, a circuit of AND, OR and NOT gates with `s` gates is simulated
by `2 s` AND/OR gates computing every wire together with its negation.

Main results:
* `dual_correct`: the dual-rail translation on top of any gate list providing constants and the
  negated inputs.
* `stage1`: `SIZE s ⊆ SIZENot (fun n => 2 * s n + n + 2) (fun n => n)`.
-/

namespace PEqualNP.General.Fischer

open PEqualNP.CircuitLowerBounds

/-! ### Evaluation of gate lists -/

/-- One evaluation step: append the value of gate `g`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The wire values of a gate list on input `x`. -/
def run (x : List Bool) (gs : List Gate) : List Bool := gs.foldl step x

/-- The value of wire `i`. -/
def V (gs : List Gate) (x : List Bool) (i : ℕ) : Bool := (run x gs).getD i false

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run x C.gates := rfl

theorem eval_eq (C : Circuit) (x : List Bool) : C.eval x = V C.gates x C.output := rfl

theorem run_append (x : List Bool) (gs hs : List Gate) :
    run x (gs ++ hs) = run (run x gs) hs := List.foldl_append

theorem run_nil (x : List Bool) : run x [] = x := rfl

theorem run_single (w : List Bool) (g : Gate) :
    run w [g] = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem run_eq_append (x : List Bool) (gs : List Gate) : ∃ y, run x gs = x ++ y := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    obtain ⟨y, hy⟩ := ih (step x g)
    refine ⟨[g.op.eval (g.inputs.map fun i => x.getD i false)] ++ y, ?_⟩
    change run (step x g) gs = _
    rw [hy, step, List.append_assoc]

theorem length_run (x : List Bool) (gs : List Gate) :
    (run x gs).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run (step x g) gs).length = _
    rw [ih, step]; simp; omega

theorem getD_append_left' (a b : List Bool) (i : ℕ) (h : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem V_append (gs hs : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length + gs.length) :
    V (gs ++ hs) x i = V gs x i := by
  unfold V
  rw [run_append]
  obtain ⟨y, hy⟩ := run_eq_append (run x gs) hs
  rw [hy, getD_append_left']
  rw [length_run]; exact h

theorem V_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    V (gs ++ [g]) x (x.length + gs.length) = g.op.eval (g.inputs.map (V gs x)) := by
  unfold V
  rw [run_append, run_single]
  have hl : (run x gs).length = x.length + gs.length := length_run x gs
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

theorem V_input (gs : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    V gs x i = x.getD i false := by
  have := V_append [] gs x i (by simpa using h)
  simpa [V, run] using this

/-! ### Admissible gates and NOT counting -/

/-- An admissible gate: AND, OR or NOT of fan-in at most two. -/
def GoodG (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

open Classical in
/-- The number of NOT gates. -/
noncomputable def nots (gs : List Gate) : ℕ := (gs.filter fun g => g.op = GateOp.not).length

theorem nots_append (a b : List Gate) : nots (a ++ b) = nots a + nots b := by
  simp [nots, List.filter_append]

theorem nots_nil : nots [] = 0 := rfl

theorem nots_and (l : List ℕ) : nots [⟨GateOp.and, l⟩] = 0 := by simp [nots]
theorem nots_or (l : List ℕ) : nots [⟨GateOp.or, l⟩] = 0 := by simp [nots]
theorem nots_not (l : List ℕ) : nots [⟨GateOp.not, l⟩] = 1 := by simp [nots]

/-- `gs'` extends `gs` by admissible gates, `k` of them NOT gates. -/
def Ext (gs gs' : List Gate) (k : ℕ) : Prop :=
  ∃ hs, gs' = gs ++ hs ∧ (∀ g ∈ hs, GoodG g) ∧ nots hs = k

theorem Ext.refl (gs : List Gate) : Ext gs gs 0 := ⟨[], by simp, by simp, rfl⟩

theorem Ext.trans {a b c : List Gate} {k l : ℕ} (h1 : Ext a b k) (h2 : Ext b c l) :
    Ext a c (k + l) := by
  obtain ⟨h, rfl, hg, hn⟩ := h1
  obtain ⟨h', rfl, hg', hn'⟩ := h2
  refine ⟨h ++ h', by simp, ?_, by rw [nots_append, hn, hn']⟩
  intro g hgm
  rcases List.mem_append.1 hgm with hh | hh
  · exact hg g hh
  · exact hg' g hh

theorem Ext.V {gs gs' : List Gate} {k : ℕ} (h : Ext gs gs' k) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) : Fischer.V gs' x i = Fischer.V gs x i := by
  obtain ⟨hs, rfl, -, -⟩ := h
  exact V_append gs hs x i hi

theorem Ext.length {gs gs' : List Gate} {k : ℕ} (h : Ext gs gs' k) :
    gs.length ≤ gs'.length := by
  obtain ⟨hs, rfl, -, -⟩ := h
  simp

theorem Ext.snoc_and (gs : List Gate) (l : List ℕ) (hl : l.length ≤ 2) :
    Ext gs (gs ++ [⟨GateOp.and, l⟩]) 0 :=
  ⟨_, rfl, by simp [GoodG, hl], nots_and l⟩

theorem Ext.snoc_or (gs : List Gate) (l : List ℕ) (hl : l.length ≤ 2) :
    Ext gs (gs ++ [⟨GateOp.or, l⟩]) 0 :=
  ⟨_, rfl, by simp [GoodG, hl], nots_or l⟩

theorem Ext.snoc_not (gs : List Gate) (l : List ℕ) (hl : l.length ≤ 2) :
    Ext gs (gs ++ [⟨GateOp.not, l⟩]) 1 :=
  ⟨_, rfl, by simp [GoodG, hl], nots_not l⟩

theorem Ext.snoc (gs : List Gate) (g : Gate) (hg : GoodG g) : Ext gs (gs ++ [g]) (nots [g]) :=
  ⟨_, rfl, by simpa using hg, rfl⟩

/-- `gs'` extends `gs`. -/
def Pre (gs gs' : List Gate) : Prop := ∃ hs, gs' = gs ++ hs

theorem Pre.V {gs gs' : List Gate} (h : Pre gs gs') (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) : Fischer.V gs' x i = Fischer.V gs x i := by
  obtain ⟨hs, rfl⟩ := h
  exact V_append gs hs x i hi

theorem Pre.refl (gs : List Gate) : Pre gs gs := ⟨[], by simp⟩

theorem Pre.trans {a b c : List Gate} (h1 : Pre a b) (h2 : Pre b c) : Pre a c := by
  obtain ⟨h, rfl⟩ := h1
  obtain ⟨h', rfl⟩ := h2
  exact ⟨h ++ h', by simp⟩

theorem Ext.pre {gs gs' : List Gate} {k : ℕ} (h : Ext gs gs' k) : Pre gs gs' := by
  obtain ⟨hs, rfl, -, -⟩ := h
  exact ⟨hs, rfl⟩

theorem pre_append (gs hs : List Gate) : Pre gs (gs ++ hs) := ⟨hs, rfl⟩

theorem V_map_pre {gs gs' : List Gate} (h : Pre gs gs') (x : List Bool) (l : List ℕ)
    (hl : ∀ i ∈ l, i < x.length + gs.length) : l.map (Fischer.V gs' x) = l.map (Fischer.V gs x) :=
  List.map_congr_left fun i hi => h.V x i (hl i hi)

/-! ### Blocks of gates -/

/-- Append the gates `g 0, …, g (Q - 1)`. -/
def hBlk (g : ℕ → Gate) (gs : List Gate) : ℕ → List Gate
  | 0 => gs
  | q + 1 => hBlk g gs q ++ [g q]

theorem hBlk_length (g : ℕ → Gate) (gs : List Gate) (Q : ℕ) :
    (hBlk g gs Q).length = gs.length + Q := by
  induction Q with
  | zero => rfl
  | succ q ih => simp [hBlk, ih]; omega

theorem hBlk_pre (g : ℕ → Gate) (gs : List Gate) {q Q : ℕ} (h : q ≤ Q) :
    Pre (hBlk g gs q) (hBlk g gs Q) := by
  induction Q with
  | zero => obtain rfl : q = 0 := by omega
            exact Pre.refl _
  | succ Q ih =>
    rcases Nat.lt_or_ge q (Q + 1) with h' | h'
    · exact (ih (by omega)).trans (pre_append _ _)
    · obtain rfl : q = Q + 1 := by omega
      exact Pre.refl _

theorem hBlk_ext (g : ℕ → Gate) (gs : List Gate) (c : ℕ) (hg : ∀ q, GoodG (g q))
    (hn : ∀ q, nots [g q] = c) (Q : ℕ) : Ext gs (hBlk g gs Q) (c * Q) := by
  induction Q with
  | zero => simpa [hBlk] using Ext.refl gs
  | succ Q ih =>
    have := ih.trans (Ext.snoc (hBlk g gs Q) (g Q) (hg Q))
    rw [hn Q] at this
    simpa [hBlk, Nat.mul_succ] using this

theorem V_hBlk (g : ℕ → Gate) (gs : List Gate) (x : List Bool) {q Q : ℕ} (hq : q < Q)
    (hin : ∀ i ∈ (g q).inputs, i < x.length + gs.length) :
    V (hBlk g gs Q) x (x.length + gs.length + q) = (g q).op.eval ((g q).inputs.map (V gs x)) := by
  rw [(hBlk_pre g gs (show q + 1 ≤ Q by omega)).V x _ (by rw [hBlk_length]; omega)]
  have h1 : V (hBlk g gs (q + 1)) x (x.length + gs.length + q) =
      (g q).op.eval ((g q).inputs.map (V (hBlk g gs q) x)) := by
    have := V_snoc (hBlk g gs q) (g q) x
    rw [hBlk_length] at this
    rw [← Nat.add_assoc] at this
    exact this
  rw [h1, V_map_pre (hBlk_pre g gs (Nat.zero_le q)) x _ hin]
  rfl

/-- Append, for `q < Q`, the pair `a_q = AND (A q)`, `o_q = OR (O q, a_q)`. -/
def pairBlk (n : ℕ) (A : ℕ → List ℕ) (O : ℕ → ℕ) (gs : List Gate) : ℕ → List Gate
  | 0 => gs
  | q + 1 => pairBlk n A O gs q ++
      [⟨GateOp.and, A q⟩, ⟨GateOp.or, [O q, n + (pairBlk n A O gs q).length]⟩]

theorem pairBlk_length (n : ℕ) (A : ℕ → List ℕ) (O : ℕ → ℕ) (gs : List Gate) (Q : ℕ) :
    (pairBlk n A O gs Q).length = gs.length + 2 * Q := by
  induction Q with
  | zero => rfl
  | succ q ih => simp [pairBlk, ih]; omega

theorem pairBlk_pre (n : ℕ) (A : ℕ → List ℕ) (O : ℕ → ℕ) (gs : List Gate) {q Q : ℕ}
    (h : q ≤ Q) : Pre (pairBlk n A O gs q) (pairBlk n A O gs Q) := by
  induction Q with
  | zero => obtain rfl : q = 0 := by omega
            exact Pre.refl _
  | succ Q ih =>
    rcases Nat.lt_or_ge q (Q + 1) with h' | h'
    · exact (ih (by omega)).trans (pre_append _ _)
    · obtain rfl : q = Q + 1 := by omega
      exact Pre.refl _

theorem pairBlk_ext (n : ℕ) (A : ℕ → List ℕ) (O : ℕ → ℕ) (gs : List Gate)
    (hA : ∀ q, (A q).length ≤ 2) (Q : ℕ) : Ext gs (pairBlk n A O gs Q) 0 := by
  induction Q with
  | zero => exact Ext.refl gs
  | succ Q ih =>
    have h1 := Ext.snoc_and (pairBlk n A O gs Q) (A Q) (hA Q)
    have h2 := Ext.snoc_or (pairBlk n A O gs Q ++ [⟨GateOp.and, A Q⟩])
      [O Q, n + (pairBlk n A O gs Q).length] (by simp)
    simpa [pairBlk] using (ih.trans h1).trans h2

theorem V_pairBlk (n : ℕ) (A : ℕ → List ℕ) (O : ℕ → ℕ) (gs : List Gate) (x : List Bool)
    (hx : x.length = n) {q Q : ℕ} (hq : q < Q) (hA : ∀ i ∈ A q, i < n + gs.length)
    (hO : O q < n + gs.length + 2 * q) :
    V (pairBlk n A O gs Q) x (n + gs.length + 2 * q + 1) =
      (V (pairBlk n A O gs Q) x (O q) || (A q).all (V gs x)) := by
  subst hx
  have hp := pairBlk_pre x.length A O gs (show q + 1 ≤ Q by omega)
  rw [hp.V x _ (by rw [pairBlk_length]; omega), hp.V x _ (by rw [pairBlk_length]; omega)]
  set st := pairBlk x.length A O gs q with hst
  have hl : st.length = gs.length + 2 * q := pairBlk_length _ _ _ _ _
  have e : pairBlk x.length A O gs (q + 1) =
      (st ++ [⟨GateOp.and, A q⟩]) ++ [⟨GateOp.or, [O q, x.length + st.length]⟩] := by
    simp [pairBlk, hst]
  rw [e]
  have i1 : x.length + gs.length + 2 * q + 1 = x.length + (st ++ [(⟨GateOp.and, A q⟩ : Gate)]).length := by
    simp [hl]; omega
  rw [i1, V_snoc, (pre_append (st ++ [(⟨GateOp.and, A q⟩ : Gate)])
    [(⟨GateOp.or, [O q, x.length + st.length]⟩ : Gate)]).V x _ (by simp [hl]; omega)]
  have h2 : V (st ++ [(⟨GateOp.and, A q⟩ : Gate)]) x (x.length + st.length) = (A q).all (V gs x) := by
    rw [V_snoc, V_map_pre (pairBlk_pre x.length A O gs (Nat.zero_le q)) x _ (by simpa [pairBlk] using hA)]
    simp [GateOp.eval, List.all_map, pairBlk]
  simp only [List.map, h2, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id]

theorem V_pair_fst (st : List Gate) (p q : Gate) (x : List Bool) :
    V (st ++ [p, q]) x (x.length + st.length) = p.op.eval (p.inputs.map (V st x)) := by
  have e : st ++ [p, q] = (st ++ [p]) ++ [q] := by simp
  rw [e, V_append _ _ x _ (by simp), V_snoc]

theorem V_pair_snd (st : List Gate) (p q : Gate) (x : List Bool) :
    V (st ++ [p, q]) x (x.length + st.length + 1) =
      q.op.eval (q.inputs.map (V (st ++ [p]) x)) := by
  have e : st ++ [p, q] = (st ++ [p]) ++ [q] := by simp
  have i : x.length + st.length + 1 = x.length + (st ++ [p]).length := by simp; omega
  rw [e, i, V_snoc]

/-! ### Dual rail -/

/-- Where the positive copy of wire `k` of the simulated circuit lives, after `j` of its gates. -/
def posR (n B f j k : ℕ) : ℕ := if k < n then k else if k < n + j then B + 2 * (k - n) else f

/-- Where the negated copy of wire `k` of the simulated circuit lives, after `j` of its gates. -/
def negR (n B t : ℕ) (neg : ℕ → ℕ) (j k : ℕ) : ℕ :=
  if k < n then neg k else if k < n + j then B + 2 * (k - n) + 1 else t

/-- The two AND/OR gates simulating gate number `j` of the simulated circuit. -/
def dualG (n B t f : ℕ) (neg : ℕ → ℕ) (j : ℕ) (g : Gate) : List Gate :=
  match g.op, g.inputs with
  | GateOp.and, l => [⟨GateOp.and, l.map (posR n B f j)⟩, ⟨GateOp.or, l.map (negR n B t neg j)⟩]
  | GateOp.or, l => [⟨GateOp.or, l.map (posR n B f j)⟩, ⟨GateOp.and, l.map (negR n B t neg j)⟩]
  | GateOp.not, [] => [⟨GateOp.and, []⟩, ⟨GateOp.or, []⟩]
  | GateOp.not, a :: _ => [⟨GateOp.or, [negR n B t neg j a]⟩, ⟨GateOp.or, [posR n B f j a]⟩]
  | _, _ => [⟨GateOp.and, []⟩, ⟨GateOp.and, []⟩]

/-- The dual-rail simulation of the first `j` gates of `cg`, appended to `gs`. -/
def dualSt (n t f : ℕ) (neg : ℕ → ℕ) (cg gs : List Gate) : ℕ → List Gate
  | 0 => gs
  | j + 1 => dualSt n t f neg cg gs j ++
      dualG n (n + gs.length) t f neg j (cg.getD j ⟨GateOp.and, []⟩)

theorem dualG_ext (n B t f : ℕ) (neg : ℕ → ℕ) (j : ℕ) (g : Gate) (st : List Gate)
    (hg : g.inputs.length ≤ 2) :
    (dualG n B t f neg j g).length = 2 ∧ Ext st (st ++ dualG n B t f neg j g) 0 := by
  obtain ⟨op, l⟩ := g
  simp only at hg
  have key : ∀ a b : Gate, GoodG a → GoodG b → nots [a] = 0 → nots [b] = 0 →
      Ext st (st ++ [a, b]) 0 := by
    intro a b ha hb na nb
    have := (Ext.snoc st a ha).trans (Ext.snoc (st ++ [a]) b hb)
    rw [na, nb] at this
    simpa using this
  rcases op with _ | _ | _ | m | _ <;> simp only [dualG]
  · exact ⟨rfl, key _ _ (by simp [GoodG, hg]) (by simp [GoodG, hg]) (nots_and _) (nots_or _)⟩
  · exact ⟨rfl, key _ _ (by simp [GoodG, hg]) (by simp [GoodG, hg]) (nots_or _) (nots_and _)⟩
  · rcases l with _ | ⟨a, l⟩
    · exact ⟨rfl, key _ _ (by simp [GoodG]) (by simp [GoodG]) (nots_and _) (nots_or _)⟩
    · exact ⟨rfl, key _ _ (by simp [GoodG]) (by simp [GoodG]) (nots_or _) (nots_or _)⟩
  · exact ⟨rfl, key _ _ (by simp [GoodG]) (by simp [GoodG]) (nots_and _) (nots_and _)⟩
  · exact ⟨rfl, key _ _ (by simp [GoodG]) (by simp [GoodG]) (nots_and _) (nots_and _)⟩

theorem dualG_length (n B t f : ℕ) (neg : ℕ → ℕ) (j : ℕ) (g : Gate) :
    (dualG n B t f neg j g).length = 2 := by
  obtain ⟨op, l⟩ := g
  rcases op with _ | _ | _ | m | _ <;> simp only [dualG] <;> try rfl
  rcases l with _ | ⟨a, l⟩ <;> rfl

theorem any_map_not (l : List ℕ) (c : ℕ → Bool) :
    (l.map fun k => !c k).any id = !((l.map c).all id) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.any_cons, List.all_cons, ih, id]; cases c a <;> rfl

theorem all_map_not (l : List ℕ) (c : ℕ → Bool) :
    (l.map fun k => !c k).all id = !((l.map c).any id) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.any_cons, List.all_cons, ih, id]; cases c a <;> rfl

theorem V_dualG (n B t f : ℕ) (neg : ℕ → ℕ) (j : ℕ) (g : Gate) (st : List Gate) (x : List Bool)
    (hx : x.length = n) (c : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hp : ∀ k, posR n B f j k < n + st.length ∧ V st x (posR n B f j k) = c k)
    (hn : ∀ k, negR n B t neg j k < n + st.length ∧ V st x (negR n B t neg j k) = !c k) :
    V (st ++ dualG n B t f neg j g) x (n + st.length) = g.op.eval (g.inputs.map c) ∧
      V (st ++ dualG n B t f neg j g) x (n + st.length + 1) = !g.op.eval (g.inputs.map c) := by
  subst hx
  obtain ⟨op, l⟩ := g
  have mp : ∀ l : List ℕ, (l.map (posR x.length B f j)).map (V st x) = l.map c := by
    intro l; rw [List.map_map]; exact List.map_congr_left fun k _ => (hp k).2
  have mn : ∀ (a : Gate) (l : List ℕ),
      (l.map (negR x.length B t neg j)).map (V (st ++ [a]) x) = l.map fun k => !c k := by
    intro a l; rw [List.map_map]
    exact List.map_congr_left fun k _ => by
      simp only [Function.comp]
      rw [V_append _ _ x _ (hn k).1]; exact (hn k).2
  have mp' : ∀ (a : Gate) (l : List ℕ),
      (l.map (posR x.length B f j)).map (V (st ++ [a]) x) = l.map c := by
    intro a l; rw [List.map_map]
    exact List.map_congr_left fun k _ => by
      simp only [Function.comp]
      rw [V_append _ _ x _ (hp k).1]; exact (hp k).2
  simp only at hop
  rcases hop with rfl | rfl | rfl
  · simp only [dualG]
    rw [V_pair_fst, V_pair_snd, mp, mn]
    simp only [GateOp.eval, List.map_cons, List.map_nil]
    exact ⟨trivial, any_map_not l c⟩
  · simp only [dualG]
    rw [V_pair_fst, V_pair_snd, mp, mn]
    simp only [GateOp.eval, List.map_cons, List.map_nil]
    exact ⟨trivial, all_map_not l c⟩
  · rcases l with _ | ⟨a, l⟩
    · simp only [dualG]
      rw [V_pair_fst, V_pair_snd]
      simp [GateOp.eval]
    · simp only [dualG]
      rw [V_pair_fst, V_pair_snd]
      have h1 : [negR x.length B t neg j a].map (V st x) = [!c a] := by simp [(hn a).2]
      have h2 : [posR x.length B f j a].map (V (st ++ [⟨GateOp.or, [negR x.length B t neg j a]⟩]) x)
          = [c a] := by simpa using mp' ⟨GateOp.or, [negR x.length B t neg j a]⟩ [a]
      rw [h1, h2]
      simp [GateOp.eval]

theorem posR_lt {n B f j k : ℕ} (h : k < n + j) : posR n B f (j + 1) k = posR n B f j k := by
  unfold posR; split_ifs <;> omega
theorem posR_eq {n B f j : ℕ} : posR n B f (j + 1) (n + j) = B + 2 * j := by
  unfold posR; split_ifs <;> omega
theorem posR_gt {n B f j k : ℕ} (h : n + j < k) : posR n B f (j + 1) k = f := by
  unfold posR; split_ifs <;> omega
theorem negR_lt {n B t neg j k} (h : k < n + j) : negR n B t neg (j + 1) k = negR n B t neg j k := by
  unfold negR; split_ifs <;> omega
theorem negR_eq {n B t neg j} : negR n B t neg (j + 1) (n + j) = B + 2 * j + 1 := by
  unfold negR; split_ifs <;> omega
theorem negR_gt {n B t neg j k} (h : n + j < k) : negR n B t neg (j + 1) k = t := by
  unfold negR; split_ifs <;> omega

theorem getD_of_le (l : List Bool) (k : ℕ) (h : l.length ≤ k) : l.getD k false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- Correctness of the dual-rail simulation. -/
theorem dual_spec (n t f : ℕ) (neg : ℕ → ℕ) (cg gs : List Gate) (x : List Bool)
    (hx : x.length = n)
    (hcg : ∀ g ∈ cg, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (ht : t < n + gs.length) (hvt : V gs x t = true)
    (hf : f < n + gs.length) (hvf : V gs x f = false)
    (hneg : ∀ i < n, neg i < n + gs.length ∧ V gs x (neg i) = !x.getD i false) :
    ∀ j ≤ cg.length, (dualSt n t f neg cg gs j).length = gs.length + 2 * j ∧
      Pre gs (dualSt n t f neg cg gs j) ∧
      ∀ k, (posR n (n + gs.length) f j k < n + (dualSt n t f neg cg gs j).length ∧
        V (dualSt n t f neg cg gs j) x (posR n (n + gs.length) f j k) =
          (run x (cg.take j)).getD k false) ∧
       (negR n (n + gs.length) t neg j k < n + (dualSt n t f neg cg gs j).length ∧
        V (dualSt n t f neg cg gs j) x (negR n (n + gs.length) t neg j k) =
          !(run x (cg.take j)).getD k false) := by
  intro j hj
  induction j with
  | zero =>
    refine ⟨rfl, Pre.refl _, fun k => ?_⟩
    simp only [dualSt, List.take_zero, run_nil, posR, negR, Nat.add_zero]
    by_cases hk : k < n
    · simp only [hk, ite_true]
      refine ⟨⟨by omega, V_input gs x k (by omega)⟩, (hneg k hk).1, (hneg k hk).2⟩
    · simp only [hk, ite_false]
      rw [getD_of_le x k (by omega)]
      exact ⟨⟨hf, hvf⟩, ht, hvt⟩
  | succ j ih =>
    obtain ⟨hlen, hpre, hk⟩ := ih (by omega)
    set B := n + gs.length
    set st := dualSt n t f neg cg gs j with hst
    have hjl : j < cg.length := by omega
    set g := cg[j] with hg
    have hgd : cg.getD j ⟨GateOp.and, []⟩ = g := by
      simp [List.getD_eq_getElem?_getD, hg, List.getElem?_eq_getElem hjl]
    have hst1 : dualSt n t f neg cg gs (j + 1) = st ++ dualG n B t f neg j g := by
      simp only [dualSt, hgd]; rfl
    set cw := run x (cg.take j) with hcw
    have hcwl : cw.length = n + j := by
      rw [hcw, length_run, List.length_take]; omega
    have hcw1 : run x (cg.take (j + 1)) =
        cw ++ [g.op.eval (g.inputs.map fun i => cw.getD i false)] := by
      rw [List.take_succ_eq_append_getElem hjl, run_append, run_single]
    have hgop := hcg g (List.getElem_mem hjl)
    have hl2 := dualG_length n B t f neg j g
    have hpre1 : Pre st (st ++ dualG n B t f neg j g) := pre_append _ _
    have hvals := V_dualG n B t f neg j g st x hx (fun i => cw.getD i false) hgop
      (fun k => (hk k).1) (fun k => (hk k).2)
    have hBst : B + 2 * j = n + st.length := by rw [hlen]; omega
    rw [hst1]
    refine ⟨by simp [hlen, hl2]; omega, hpre.trans hpre1, fun k => ?_⟩
    have hlen1 : (st ++ dualG n B t f neg j g).length = gs.length + 2 * (j + 1) := by
      simp [hlen, hl2]; omega
    rw [hcw1]
    rcases Nat.lt_trichotomy k (n + j) with h | rfl | h
    · rw [posR_lt h, negR_lt h, getD_append_left' _ _ _ (by omega)]
      obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hk k
      refine ⟨⟨by rw [hlen1]; rw [hlen] at a1; omega, by rw [hpre1.V x _ (by omega), a2]⟩,
        by rw [hlen1]; rw [hlen] at b1; omega, by rw [hpre1.V x _ (by omega), b2]⟩
    · rw [posR_eq, negR_eq, hBst]
      have e : (cw ++ [g.op.eval (g.inputs.map fun i => cw.getD i false)]).getD (n + j) false =
          g.op.eval (g.inputs.map fun i => cw.getD i false) := by
        rw [← hcwl]; simp [List.getD_eq_getElem?_getD]
      rw [e, hvals.1, hvals.2]
      refine ⟨⟨by rw [hlen1, hlen]; omega, rfl⟩, by rw [hlen1, hlen]; omega, rfl⟩
    · rw [posR_gt h, negR_gt h, getD_of_le _ _ (by simp; omega)]
      have p1 : Pre gs (st ++ dualG n B t f neg j g) := hpre.trans hpre1
      refine ⟨⟨by rw [hlen1]; omega, by rw [p1.V x _ (by omega), hvf]⟩,
        by rw [hlen1]; omega, by rw [p1.V x _ (by omega), hvt]; rfl⟩

theorem dual_ext (n t f : ℕ) (neg : ℕ → ℕ) (cg gs : List Gate)
    (hcg : ∀ g ∈ cg, g.inputs.length ≤ 2) :
    ∀ j ≤ cg.length, Ext gs (dualSt n t f neg cg gs j) 0 := by
  intro j hj
  induction j with
  | zero => exact Ext.refl gs
  | succ j ih =>
    have hjl : j < cg.length := by omega
    have hgd : cg.getD j ⟨GateOp.and, []⟩ = cg[j] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
    have := (ih (by omega)).trans (dualG_ext n (n + gs.length) t f neg j cg[j]
      (dualSt n t f neg cg gs j) (hcg _ (List.getElem_mem hjl))).2
    have e : dualSt n t f neg cg gs (j + 1) = dualSt n t f neg cg gs j ++
        dualG n (n + gs.length) t f neg j (cg.getD j ⟨GateOp.and, []⟩) := rfl
    rw [e, hgd]; simpa using this

theorem dualSt_length (n t f : ℕ) (neg : ℕ → ℕ) (cg gs : List Gate) (j : ℕ) :
    (dualSt n t f neg cg gs j).length = gs.length + 2 * j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [dualSt, ih, dualG_length]; omega

/-- The dual-rail circuit simulating `C` on top of the gate list `gs`, which provides the
constants `true` (wire `t`), `false` (wire `f`) and the negated inputs (wires `neg i`). -/
def dualCircuit (n t f : ℕ) (neg : ℕ → ℕ) (C : Circuit) (gs : List Gate) : Circuit :=
  ⟨dualSt n t f neg C.gates gs C.gates.length, posR n (n + gs.length) f C.gates.length C.output⟩

/-- Stage 1 (dual rail, general form): given wires for `true`, `false` and the negated inputs,
a NOT-free extension by `2 * C.size` gates computes `C`. -/
theorem dual_correct (n t f : ℕ) (neg : ℕ → ℕ) (C : Circuit) (gs : List Gate)
    (hC : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (ht : t < n + gs.length) (hf : f < n + gs.length) (hneg : ∀ i < n, neg i < n + gs.length)
    (hval : ∀ x : List Bool, x.length = n →
      V gs x t = true ∧ V gs x f = false ∧ ∀ i < n, V gs x (neg i) = !x.getD i false) :
    Ext gs (dualCircuit n t f neg C gs).gates 0 ∧
      (dualCircuit n t f neg C gs).size = gs.length + 2 * C.size ∧
      ∀ x : List Bool, x.length = n → (dualCircuit n t f neg C gs).eval x = C.eval x := by
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg; simpa using (hC g hg).1
  refine ⟨dual_ext n t f neg C.gates gs (fun g hg => (hC g hg).2) _ le_rfl, ?_, ?_⟩
  · simp only [Circuit.size, dualCircuit, dualSt_length]
  · intro x hx
    obtain ⟨hvt, hvf, hvn⟩ := hval x hx
    obtain ⟨-, -, hk⟩ := dual_spec n t f neg C.gates gs x hx hop ht hvt hf hvf
      (fun i hi => ⟨hneg i hi, hvn i hi⟩) _ le_rfl
    rw [eval_eq, dualCircuit]
    simp only
    rw [(hk C.output).1.2, List.take_length]
    rfl

open Classical in
theorem good_of_ext {gs : List Gate} {k : ℕ} (h : Ext [] gs k) :
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) ∧ (gs.filter fun g => g.op = GateOp.not).length = k := by
  obtain ⟨hs, rfl, hg, hn⟩ := h
  exact ⟨fun g hm => hg g (by simpa using hm), by simpa [nots] using hn⟩

/-- The prefix of the stage-1 circuit: `true`, `false`, then the `n` negated inputs. -/
def negPrefix (n : ℕ) : List Gate :=
  hBlk (fun i => ⟨GateOp.not, [i]⟩) [⟨GateOp.and, []⟩, ⟨GateOp.or, []⟩] n

theorem negPrefix_length (n : ℕ) : (negPrefix n).length = n + 2 := by
  simp [negPrefix, hBlk_length]; omega

theorem negPrefix_ext (n : ℕ) : Ext [] (negPrefix n) n := by
  have h0 : Ext [] [⟨GateOp.and, []⟩, ⟨GateOp.or, []⟩] 0 := by
    simpa using (Ext.snoc_and [] [] (by simp)).trans (Ext.snoc_or [⟨GateOp.and, []⟩] [] (by simp))
  have := h0.trans (hBlk_ext (fun i => ⟨GateOp.not, [i]⟩) _ 1 (fun q => by simp [GoodG])
    (fun q => nots_not _) n)
  simpa [negPrefix] using this

theorem negPrefix_val (n : ℕ) (x : List Bool) (hx : x.length = n) :
    V (negPrefix n) x n = true ∧ V (negPrefix n) x (n + 1) = false ∧
      ∀ i < n, V (negPrefix n) x (n + 2 + i) = !x.getD i false := by
  subst hx
  have hp : Pre [⟨GateOp.and, []⟩, ⟨GateOp.or, []⟩] (negPrefix x.length) :=
    hBlk_pre _ _ (Nat.zero_le x.length)
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · rw [hp.V x _ (by simp)]
    simpa [GateOp.eval] using V_pair_fst [] ⟨GateOp.and, []⟩ ⟨GateOp.or, []⟩ x
  · rw [hp.V x _ (by simp)]
    simpa [GateOp.eval] using V_pair_snd [] ⟨GateOp.and, []⟩ ⟨GateOp.or, []⟩ x
  · have := V_hBlk (fun i => ⟨GateOp.not, [i]⟩) [⟨GateOp.and, []⟩, ⟨GateOp.or, []⟩] x hi
      (by simp; omega)
    simp only [List.length_cons, List.length_nil] at this
    rw [negPrefix, this]
    simp [GateOp.eval, V_input _ x i hi]

/-- **Stage 1** (Markov's dual rail): `n` NOT gates (one per input) suffice, at the price of
doubling the size. -/
theorem stage1 (s : ℕ → ℕ) :
    SIZE s ⊆ SIZENot (fun n => 2 * s n + n + 2) (fun n => n) := by
  intro L hL n
  obtain ⟨C, hC, hs, hd⟩ := hL n
  obtain ⟨hext, hsize, heval⟩ := dual_correct n n (n + 1) (fun i => n + 2 + i) C (negPrefix n) hC
    (by rw [negPrefix_length]; omega) (by rw [negPrefix_length]; omega)
    (fun i hi => by rw [negPrefix_length]; omega)
    (fun x hx => negPrefix_val n x hx)
  obtain ⟨hg, hn⟩ := good_of_ext ((negPrefix_ext n).trans hext)
  refine ⟨dualCircuit n n (n + 1) (fun i => n + 2 + i) C (negPrefix n), hg, ?_, by simpa using hn.le, ?_⟩
  · rw [hsize, negPrefix_length]; simp only [Circuit.size] at hs ⊢; omega
  · intro x hx
    rw [heval x hx]
    exact hd x hx

end PEqualNP.General.Fischer
