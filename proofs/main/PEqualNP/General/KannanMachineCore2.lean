import PEqualNP.General.KannanMachineCore1

/-!
# Polynomial-time string programs for the circuit check: evaluating a coded circuit

`cpt_circEval`: the value of the circuit `decGates w B C` (with output index read from the bits
after the gates) on a point `p` is polynomial-time computable from unary `w`, unary `B`, the
code `C` and the point. One gate is evaluated with two table lookups; the wires are built by
iterating the gate step `B` times.
-/

namespace PEqualNP.General.Kannan.Core

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.CircuitLowerBounds

/-! ### One gate -/

/-- The value of the gate coded by `f` on the wires `V`. -/
def gv (w : ℕ) (f V : List Bool) : Bool :=
  (decGate w f).op.eval ((decGate w f).inputs.map fun i => V.getD i false)

theorem gv_eq (w : ℕ) (f V : List Bool) : gv w f V =
    (let a := f.getD 0 false
     let b := f.getD 1 false
     let p1 := (f.drop 2).headD false
     let v1 := V.getD (bv ((f.drop 3).take w)) false
     let p2 := ((f.drop 3).drop w).headD false
     let v2 := V.getD (bv ((((f.drop 3).drop w).drop 1).take w)) false
     if a then !(if p1 then v1 else if p2 then v2 else false)
     else if b then (p1 && v1) || (p2 && v2) else (!p1 || v1) && (!p2 || v2)) := by
  have e1 : (f.drop 2).drop 1 = f.drop 3 := by simp [List.drop_drop]
  have e2 : f.drop (3 + w) = (f.drop 3).drop w := by simp [List.drop_drop]
  simp only [gv, decGate, decSlot, e1, e2]
  cases (f.getD 0 false) <;> cases (f.getD 1 false) <;>
    cases ((f.drop 2).headD false) <;> cases (((f.drop 3).drop w).headD false) <;>
    simp [decOp, GateOp.eval]

/-- The gate value as a flag, from the flags of its parts. -/
def gateFl (Fa Fb P1 V1 P2 V2 : List Bool) : List Bool :=
  if Fa = [] then
    (if Fb = [] then
      (if P1 = [] then (if P2 = [] then [true] else V2)
       else (if V1 = [] then [] else (if P2 = [] then [true] else V2)))
     else
      (if P1 = [] then (if P2 = [] then [] else V2)
       else (if V1 = [] then (if P2 = [] then [] else V2) else [true])))
  else
    (if P1 = [] then (if P2 = [] then [true] else (if V2 = [] then [true] else []))
     else (if V1 = [] then [true] else []))

theorem gateFl_fl (a b p1 v1 p2 v2 : Bool) :
    gateFl (fl a) (fl b) (fl p1) (fl v1) (fl p2) (fl v2) =
      fl (if a then !(if p1 then v1 else if p2 then v2 else false)
        else if b then (p1 && v1) || (p2 && v2) else (!p1 || v1) && (!p2 || v2)) := by
  cases a <;> cases b <;> cases p1 <;> cases v1 <;> cases p2 <;> cases v2 <;> rfl

theorem cpt_gateFl {Fa Fb P1 V1 P2 V2 : List Bool → List Bool} (ha : CPT Fa) (hb : CPT Fb)
    (h1 : CPT P1) (h2 : CPT V1) (h3 : CPT P2) (h4 : CPT V2) :
    CPT (fun s => gateFl (Fa s) (Fb s) (P1 s) (V1 s) (P2 s) (V2 s)) := by
  unfold gateFl
  exact cpt_flS ha
    (cpt_flS hb
      (cpt_flS h1 (cpt_flS h3 (cpt_K _) h4) (cpt_flS h2 (cpt_K _) (cpt_flS h3 (cpt_K _) h4)))
      (cpt_flS h1 (cpt_flS h3 (cpt_K _) h4) (cpt_flS h2 (cpt_flS h3 (cpt_K _) h4) (cpt_K _))))
    (cpt_flS h1 (cpt_flS h3 (cpt_K _) (cpt_flS h4 (cpt_K _) (cpt_K _)))
      (cpt_flS h2 (cpt_K _) (cpt_K _)))

theorem cpt_drop2 {f : List Bool → List Bool} (hf : CPT f) : CPT (fun s => (f s).drop 2) :=
  cpt_congr' (cpt_drop1 (cpt_drop1 hf)) (fun s => by simp [List.drop_drop])

theorem cpt_drop3 {f : List Bool → List Bool} (hf : CPT f) : CPT (fun s => (f s).drop 3) :=
  cpt_congr' (cpt_drop1 (cpt_drop2 hf)) (fun s => by simp [List.drop_drop])

/-- The gate value as a flag. -/
theorem cpt_gv {wu f V : List Bool → List Bool} (hw : CPT wu) (hf : CPT f) (hV : CPT V) :
    CPT (fun s => fl (gv (wu s).length (f s) (V s))) := by
  have ha := cpt_headFl hf
  have hb := cpt_headFl (cpt_drop1 hf)
  have h1 := cpt_headFl (cpt_drop2 hf)
  have h2 := cpt_lookup hV (cpt_takeU hw (cpt_drop3 hf))
  have h3 := cpt_headFl (cpt_dropU hw (cpt_drop3 hf))
  have h4 := cpt_lookup hV (cpt_takeU hw (cpt_drop1 (cpt_dropU hw (cpt_drop3 hf))))
  refine cpt_congr' (cpt_gateFl ha hb h1 h2 h3 h4) (fun s => ?_)
  rw [gateFl_fl, gv_eq]
  congr 2
  · cases f s <;> simp
  · cases h : f s with
    | nil => simp
    | cons a l => cases l <;> simp

/-! ### The wires -/

/-- The wires after the gates `gs`, starting from `V`. -/
def wiresFrom (gs : List Gate) (V : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) V

/-- A flag as a one-bit list. -/
def bitL (F : List Bool) : List Bool := if F = [] then [false] else [true]

@[simp] theorem bitL_fl (b : Bool) : bitL (fl b) = [b] := by cases b <;> rfl

theorem bitL_length (F : List Bool) : (bitL F).length = 1 := by unfold bitL; split <;> rfl

/-- One gate step on the packed state `P (P wu gwu) (P V rest)`. -/
def gStep (s : List Bool) : List Bool :=
  pairB (L s) (pairB (L (R s) ++ bitL (fl (gv (L (L s)).length ((R (R s)).take (R (L s)).length)
    (L (R s))))) ((R (R s)).drop (R (L s)).length))

theorem cpt_gStep : CPT gStep := by
  have hp := cpt_L cpt_I
  have hwu := cpt_L hp
  have hgw := cpt_R hp
  have hst := cpt_R cpt_I
  have hV := cpt_L hst
  have hrest := cpt_R hst
  exact cpt_P hp (cpt_P (cpt_A hV (cpt_flS (cpt_gv hwu (cpt_takeU hgw hrest) hV) (cpt_K _)
    (cpt_K _))) (cpt_dropU hgw hrest))

theorem fl_length (b : Bool) : (fl b).length ≤ 1 := by cases b <;> simp [fl]

theorem gStep_length (s : List Bool) : (gStep s).length ≤ s.length + 4 := by
  have h1 := LR_length s
  have h2 := LR_length (R s)
  have h3 := bitL_length (fl (gv (L (L s)).length ((R (R s)).take (R (L s)).length) (L (R s))))
  unfold gStep
  rw [pairB_length', pairB_length']
  simp only [List.length_append, List.length_drop]
  omega

theorem gStep_iter (w : ℕ) (prm : List Bool) (hw : (L prm).length = w)
    (hg : (R prm).length = 2 + 2 * (1 + w)) : ∀ (B : ℕ) (V rest : List Bool),
    gStep^[B] (pairB prm (pairB V rest)) =
      pairB prm (pairB (wiresFrom (decGates w B rest) V) (rest.drop (B * (2 + 2 * (1 + w))))) := by
  intro B
  induction B with
  | zero => intro V rest; simp [wiresFrom, decGates]
  | succ B ih =>
    intro V rest
    rw [Function.iterate_succ_apply]
    have e : gStep (pairB prm (pairB V rest)) = pairB prm (pairB (V ++
        [gv w (rest.take (2 + 2 * (1 + w))) V]) (rest.drop (2 + 2 * (1 + w)))) := by
      simp only [gStep, L_pairB, R_pairB, hw, hg, bitL_fl]
    rw [e, ih]
    congr 2
    rw [List.drop_drop]; congr 1; ring

/-- The value of the coded circuit with `B` gates of index width `w` on the point `p`. -/
def circEval (w B : ℕ) (C p : List Bool) : Bool :=
  (wiresFrom (decGates w B C) p).getD (bv ((C.drop (B * (2 + 2 * (1 + w)))).take w)) false

theorem circEval_eq (k n : ℕ) (C p : List Bool) :
    circEval (ww k n) (BB k n) C p = (decCirc k n C).eval p := by
  simp only [circEval, Circuit.eval, Circuit.wires, decCirc, wiresFrom, gw]

theorem cpt_circEval {wu bu c p : List Bool → List Bool} (hw : CPT wu) (hb : CPT bu)
    (hc : CPT c) (hp : CPT p) :
    CPT (fun s => fl (circEval (wu s).length (bu s).length (c s) (p s))) := by
  have hgw : CPT (fun s => wu s ++ wu s ++ [true, true, true, true]) :=
    cpt_A (cpt_A hw hw) (cpt_K _)
  have hprm := cpt_P hw hgw
  have hit := cpt_iterGrow cpt_gStep 4 gStep_length hb (cpt_P hprm (cpt_P hp hc))
  have hV := cpt_L (cpt_R hit)
  have hout := cpt_takeU hw (cpt_R (cpt_R hit))
  refine cpt_congr' (cpt_lookup (cpt_L (cpt_R hit)) hout) (fun s => ?_)
  have hl : (wu s ++ wu s ++ [true, true, true, true]).length = 2 + 2 * (1 + (wu s).length) := by
    simp; ring
  rw [gStep_iter (wu s).length _ (by simp) (by rw [R_pairB, hl])]
  simp only [L_pairB, R_pairB, circEval]

end PEqualNP.General.Kannan.Core
