import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.General.KannanDefs

/-!
# Polynomial-time string programs for the circuit check: tools and table lookup

Tools on top of the combinators of `Universal/Prims*`: packed pairs `P a b = pairB a b` with
projections `L`, `R`; iteration with bounded growth (`cpt_iterGrow`); `takeU`/`dropU` by a
unary length; flags (`[true]` for yes, `[]` for no); the parity transducers `ev`; and table lookup
`V.getD (bv bits) false` by repeated halving (`lookupF`).
-/

namespace PEqualNP.General.Kannan.Core

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

/-- Polynomial-time computable on plain bit strings. -/
abbrev CPT (f : List Bool → List Bool) : Prop :=
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f

theorem cpt_congr' {f g : List Bool → List Bool} (h : CPT f) (e : ∀ s, f s = g s) : CPT g := by
  obtain rfl : f = g := funext e
  exact h

theorem cpt_o {f g : List Bool → List Bool} (hf : CPT f) (hg : CPT g) : CPT (fun s => g (f s)) :=
  cpt_comp hf hg

/-! ### Packed pairs -/

def L (s : List Bool) : List Bool := (unpairB s).1
def R (s : List Bool) : List Bool := (unpairB s).2

@[simp] theorem L_pairB (a b : List Bool) : L (pairB a b) = a := by simp [L, unpairB_pairB]
@[simp] theorem R_pairB (a b : List Bool) : R (pairB a b) = b := by simp [R, unpairB_pairB]

theorem pairB_length' (a b : List Bool) : (pairB a b).length = 2 * a.length + 1 + b.length := by
  simp [pairB, un]; omega

theorem LR_length (s : List Bool) : 2 * (L s).length + 1 + (R s).length ≤ s.length + 1 := by
  simp only [L, R, unpairB]
  set t := (s.dropWhile id).tail
  set m := (s.takeWhile id).length
  have h1 : s.length = m + (s.dropWhile id).length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  have h2 : t.length + 1 ≥ (s.dropWhile id).length := by simp [t]; omega
  have h3 : t.length ≤ (s.dropWhile id).length := by simp [t]
  simp only [List.length_take, List.length_drop]
  omega

theorem cpt_L {f : List Bool → List Bool} (hf : CPT f) : CPT (fun s => L (f s)) :=
  cpt_comp hf cpt_unpairB1
theorem cpt_R {f : List Bool → List Bool} (hf : CPT f) : CPT (fun s => R (f s)) :=
  cpt_comp hf cpt_unpairB2
theorem cpt_P {f g : List Bool → List Bool} (hf : CPT f) (hg : CPT g) :
    CPT (fun s => pairB (f s) (g s)) := cpt_pairB2 hf hg
theorem cpt_A {f g : List Bool → List Bool} (hf : CPT f) (hg : CPT g) :
    CPT (fun s => f s ++ g s) := cpt_app2 hf hg
theorem cpt_S {f a b : List Bool → List Bool} (hf : CPT f) (ha : CPT a) (hb : CPT b) :
    CPT (fun s => sel (f s) (a s) (b s)) := cpt_sel hf ha hb
theorem cpt_K (l : List Bool) : CPT (fun _ => l) := cpt_const l
theorem cpt_I : CPT (fun s => s) := cpt_id
theorem cpt_T {f : List Bool → List Bool} (hf : CPT f) : CPT (fun s => (f s).tail) :=
  cpt_comp hf cpt_tail

/-! ### Iteration with bounded growth -/

theorem cpt_iterGrow {g cnt arg : List Bool → List Bool} (hg : CPT g) (c : ℕ)
    (hgl : ∀ s, (g s).length ≤ s.length + c) (hcnt : CPT cnt) (harg : CPT arg) :
    CPT (fun s => g^[(cnt s).length] (arg s)) := by
  have h := cpt_iterB g hg (fun _ => c) c (fun _ => le_rfl) hgl (fun y => by nlinarith)
  refine cpt_congr' (cpt_o (cpt_P harg hcnt) h) (fun s => ?_)
  simp only [unpairB_pairB]

theorem cpt_iterLen' {g cnt arg : List Bool → List Bool} (hg : CPT g)
    (hgl : ∀ s, (g s).length ≤ s.length) (hcnt : CPT cnt) (harg : CPT arg) :
    CPT (fun s => g^[(cnt s).length] (arg s)) := cpt_iterLen hg hgl hcnt harg

/-! ### Transducers -/

theorem cpt_fst {Q : Type} [Fintype Q] (δ : Q → Bool → Q × Option Bool) (fin : Q → Option Bool)
    (q₀ : Q) : CPT (fun s => fstRun δ fin q₀ s) :=
  fst_polyTime _ _ _ δ fin q₀ (fun _ => rfl)

theorem cpt_fstF {Q : Type} [Fintype Q] {f : List Bool → List Bool} (hf : CPT f)
    (δ : Q → Bool → Q × Option Bool) (fin : Q → Option Bool) (q₀ : Q) :
    CPT (fun s => fstRun δ fin q₀ (f s)) := cpt_o hf (cpt_fst δ fin q₀)

theorem fstRun_length_le {Q : Type} (δ : Q → Bool → Q × Option Bool) (q : Q) (l : List Bool) :
    (fstRun δ (fun _ => none) q l).length ≤ l.length := by
  induction l generalizing q with
  | nil => simp [fstRun]
  | cons a l ih =>
    simp only [fstRun, List.length_append, List.length_cons]
    have := ih (δ q a).1
    cases (δ q a).2 <;> simp <;> omega

/-! ### Take and drop by a unary length -/

def tkStep (s : List Bool) : List Bool := pairB (L s ++ (R s).take 1) ((R s).drop 1)

/-- The first symbol (if any). -/
def take1D : Bool → Bool → Bool × Option Bool
  | true, b => (false, some b)
  | false, _ => (false, none)

theorem take1_eq (l : List Bool) : fstRun take1D (fun _ => none) true l = l.take 1 := by
  cases l with
  | nil => rfl
  | cons a l =>
    have : ∀ l : List Bool, fstRun take1D (fun _ => none) false l = [] := by
      intro l; induction l with
      | nil => rfl
      | cons b l ih => simpa [fstRun, take1D] using ih
    simp [fstRun, take1D, this]

theorem cpt_take1 {f : List Bool → List Bool} (hf : CPT f) : CPT (fun s => (f s).take 1) :=
  cpt_congr' (cpt_fstF hf take1D (fun _ => none) true) (fun s => take1_eq _)

theorem cpt_drop1 {f : List Bool → List Bool} (hf : CPT f) : CPT (fun s => (f s).drop 1) :=
  cpt_congr' (cpt_T hf) (fun s => by simp)

theorem cpt_tkStep : CPT tkStep :=
  cpt_P (cpt_A (cpt_L cpt_I) (cpt_take1 (cpt_R cpt_I))) (cpt_drop1 (cpt_R cpt_I))

theorem tkStep_length (s : List Bool) : (tkStep s).length ≤ s.length + 2 := by
  have := LR_length s
  unfold tkStep
  rw [pairB_length']
  simp only [List.length_append, List.length_take, List.length_drop]
  have : min 1 (R s).length ≤ 1 := min_le_left _ _
  omega

theorem tkStep_iter (j : ℕ) : ∀ (acc l : List Bool),
    tkStep^[j] (pairB acc l) = pairB (acc ++ l.take j) (l.drop j) := by
  induction j with
  | zero => intro acc l; simp
  | succ j ih =>
    intro acc l
    rw [Function.iterate_succ_apply]
    simp only [tkStep, L_pairB, R_pairB]
    rw [ih]
    congr 1
    · rw [List.append_assoc]
      congr 1
      cases l with
      | nil => simp
      | cons a l => simp
    · simp [List.drop_drop]

/-- `l.take |a|`. -/
theorem cpt_takeU {a b : List Bool → List Bool} (ha : CPT a) (hb : CPT b) :
    CPT (fun s => (b s).take (a s).length) := by
  have h := cpt_L (cpt_iterGrow cpt_tkStep 2 tkStep_length ha (cpt_P (cpt_K []) hb))
  refine cpt_congr' h (fun s => ?_)
  simp only [tkStep_iter, List.nil_append, L_pairB]

/-- `l.drop |a|`. -/
theorem cpt_dropU {a b : List Bool → List Bool} (ha : CPT a) (hb : CPT b) :
    CPT (fun s => (b s).drop (a s).length) := by
  have h := cpt_iterLen' cpt_tail (fun s => by simp) ha hb
  refine cpt_congr' h (fun s => ?_)
  generalize b s = l
  induction (a s).length generalizing l with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih]
    cases l <;> simp [List.drop_drop]

/-! ### Flags -/

/-- A bit as a flag string. -/
def fl (b : Bool) : List Bool := if b then [true] else []

theorem cpt_flS {f a b : List Bool → List Bool} (hf : CPT f) (ha : CPT a) (hb : CPT b) :
    CPT (fun s => if f s = [] then a s else b s) :=
  cpt_congr' (cpt_S hf ha hb) (fun s => rfl)

/-- The first symbol as a flag. -/
def hfD : Bool → Bool → Bool × Option Bool
  | true, b => (false, if b then some true else none)
  | false, _ => (false, none)

theorem headFl_eq (l : List Bool) : fstRun hfD (fun _ => none) true l = fl (l.headD false) := by
  cases l with
  | nil => rfl
  | cons a l =>
    have : ∀ l : List Bool, fstRun hfD (fun _ => none) false l = [] := by
      intro l; induction l with
      | nil => rfl
      | cons b l ih => simpa [fstRun, hfD] using ih
    cases a <;> simp [fstRun, hfD, this, fl]

theorem cpt_headFl {f : List Bool → List Bool} (hf : CPT f) :
    CPT (fun s => fl ((f s).headD false)) :=
  cpt_congr' (cpt_fstF hf hfD (fun _ => none) true) (fun s => headFl_eq _)

/-- A flag from a decision: `fl (decide (f s ≠ []))` is the first symbol of `[true]` or nothing. -/
theorem cpt_nonempty {f : List Bool → List Bool} (hf : CPT f) :
    CPT (fun s => fl (decide (f s ≠ []))) := by
  refine cpt_congr' (cpt_flS hf (cpt_K []) (cpt_K [true])) (fun s => ?_)
  by_cases h : f s = [] <;> simp [h, fl]

theorem cpt_flAnd {f g : List Bool → List Bool} (hf : CPT f) (hg : CPT g) :
    CPT (fun s => if f s = [] then [] else g s) :=
  cpt_flS hf (cpt_K []) hg

theorem cpt_flOr {f g : List Bool → List Bool} (hf : CPT f) (hg : CPT g) :
    CPT (fun s => if f s = [] then g s else [true]) :=
  cpt_flS hf hg (cpt_K [true])

theorem cpt_flNot {f : List Bool → List Bool} (hf : CPT f) :
    CPT (fun s => if f s = [] then [true] else []) :=
  cpt_flS hf (cpt_K [true]) (cpt_K [])

@[simp] theorem fl_eq_nil (b : Bool) : fl b = [] ↔ b = false := by cases b <;> simp [fl]

/-! ### Halving and lookup -/

/-- Keep every second symbol: `ev false` keeps positions `0, 2, ...`, `ev true` positions
`1, 3, ...`. -/
def evD : Bool → Bool → Bool × Option Bool
  | false, b => (true, some b)
  | true, _ => (false, none)

def ev (q : Bool) (V : List Bool) : List Bool := fstRun evD (fun _ => none) q V

theorem ev_getD : ∀ (V : List Bool) (j : ℕ),
    (ev false V).getD j false = V.getD (2 * j) false ∧
      (ev true V).getD j false = V.getD (2 * j + 1) false := by
  intro V
  induction V with
  | nil => intro j; simp [ev, fstRun]
  | cons a V ih =>
    intro j
    have e0 : ev false (a :: V) = a :: ev true V := by simp [ev, fstRun, evD]
    have e1 : ev true (a :: V) = ev false V := by simp [ev, fstRun, evD]
    rw [e0, e1]
    constructor
    · cases j with
      | zero => simp
      | succ j =>
        rw [List.getD_cons_succ, (ih j).2, show 2 * (j + 1) = (2 * j + 1) + 1 by ring,
          List.getD_cons_succ]
    · rw [(ih j).1, show 2 * j + 1 = 2 * j + 1 by rfl, List.getD_cons_succ]

theorem ev_length (q : Bool) (V : List Bool) : (ev q V).length ≤ V.length :=
  fstRun_length_le _ _ _

theorem cpt_ev (q : Bool) {f : List Bool → List Bool} (hf : CPT f) : CPT (fun s => ev q (f s)) :=
  cpt_fstF hf evD (fun _ => none) q

/-- One halving step of the lookup: the low bit of the index chooses the half. -/
def lkStep (s : List Bool) : List Bool :=
  pairB (sel (hd (R s)) (ev false (L s)) (ev true (L s))) (R s).tail

theorem cpt_lkStep : CPT lkStep :=
  cpt_P (cpt_S (cpt_o (cpt_R cpt_I) cpt_hd) (cpt_ev false (cpt_L cpt_I)) (cpt_ev true (cpt_L cpt_I)))
    (cpt_T (cpt_R cpt_I))

theorem lkStep_length (s : List Bool) : (lkStep s).length ≤ s.length + 1 := by
  have := LR_length s
  unfold lkStep
  rw [pairB_length']
  have h1 : (sel (hd (R s)) (ev false (L s)) (ev true (L s))).length ≤ (L s).length := by
    unfold sel; split
    · exact ev_length _ _
    · exact ev_length _ _
  simp only [List.length_tail]
  omega

/-- The halves chosen by the bits of an index. -/
def sub : List Bool → List Bool → List Bool
  | V, [] => V
  | V, b :: bits => sub (ev b V) bits

theorem sub_getD : ∀ (bits V : List Bool), (sub V bits).getD 0 false = V.getD (bv bits) false := by
  intro bits
  induction bits with
  | nil => intro V; simp [sub, bv]
  | cons b bits ih =>
    intro V
    simp only [sub, bv]
    rw [ih]
    cases b
    · simp only [Bool.toNat_false, add_zero]; exact (ev_getD V _).1
    · simp only [Bool.toNat_true]; exact (ev_getD V _).2

theorem lkStep_iter : ∀ (bits V : List Bool), lkStep^[bits.length] (pairB V bits) = pairB (sub V bits) [] := by
  intro bits
  induction bits with
  | nil => intro V; simp [sub]
  | cons b bits ih =>
    intro V
    rw [List.length_cons, Function.iterate_succ_apply]
    have : lkStep (pairB V (b :: bits)) = pairB (ev b V) bits := by
      simp only [lkStep, L_pairB, R_pairB, List.tail_cons]
      congr 1
      cases b <;> simp [sel, hd]
    rw [this, ih]
    rfl

/-- Table lookup `V.getD (bv bits) false`, as a flag. -/
theorem cpt_lookup {v bits : List Bool → List Bool} (hv : CPT v) (hb : CPT bits) :
    CPT (fun s => fl ((v s).getD (bv (bits s)) false)) := by
  have h := cpt_headFl (cpt_L (cpt_iterGrow cpt_lkStep 1 lkStep_length hb (cpt_P hv hb)))
  refine cpt_congr' h (fun s => ?_)
  simp only [lkStep_iter, L_pairB]
  rw [← sub_getD]
  cases sub (v s) (bits s) <;> rfl

end PEqualNP.General.Kannan.Core
