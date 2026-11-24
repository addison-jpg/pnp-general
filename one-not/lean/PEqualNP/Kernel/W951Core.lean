import PEqualNP.Kernel.Circuit
import PEqualNP.W951.Eval

/-!
# Kernel/W951Core: the total bridge from W951's `List Gate` circuits to `Kernel.Dag`

W951 evaluates `gates : List Gate` by a fold with `List.getD … false` (`W951/Eval.lean`); a read
of a wire that is not below the gate silently reads `false`. The kernel gate `KGate k` has the
same shape (a `GateOp` and a list of inputs, any length) and its inputs may be constants, so the
translation `conv` is total and keeps the operation and the arity: input `j` becomes the wire
`j` if `j < k`, the constant `false` otherwise. Hence the bridge has NO hypothesis:

  `ofList_valN : (ofList gates gates.length).valN x i = val gates x i`   (every list, every `i`).

This file imports only `W951/Eval.lean`, so every other W951 file may import it. It ends with
W951 statements proved through the dag with no extra hypothesis: `mono_val_viaDag`
(`Cases.mono_val`) and `val_mask_viaDag` (`Cone.val_mask`; `lmask` and `LReadClosed` are W951's
`mask` and `ReadClosed`, which are defined later than `Eval`, restated here verbatim).
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open PEqualNP.Outside

/-- W951's list gates. -/
abbrev LGate := PEqualNP.CircuitLowerBounds.Gate

/-- The gate every out-of-range index is read as: `OR []`, the constant `false`. -/
def dflt : LGate := ⟨GateOp.or, []⟩

/-! ## One gate -/

/-- Translate one input index at a position with `k` wires below it: a wire, or (W951's
convention for a dangling read) the constant `false`. -/
def src (k : ℕ) (j : ℕ) : Src k := if h : j < k then Src.wire ⟨j, h⟩ else Src.const false

/-- W951's read: the value of wire `j`, `false` if it is not below the gate. -/
def rd (k : ℕ) (v : Fin k → Bool) (j : ℕ) : Bool := if h : j < k then v ⟨j, h⟩ else false

theorem rd_mono {k : ℕ} {v v' : Fin k → Bool} (h : v ≤ v') (j : ℕ) : rd k v j ≤ rd k v' j := by
  unfold rd
  split
  · exact h _
  · exact le_rfl

theorem eval_src (k : ℕ) (v : Fin k → Bool) (j : ℕ) : (src k j).eval v = rd k v j := by
  unfold src rd
  split <;> rfl

theorem src_eq_wire {k j : ℕ} {a : Fin k} : src k j = Src.wire a ↔ j = a.1 := by
  unfold src
  split
  · next h => simp [Fin.ext_iff]
  · next h => simp only [reduceCtorEq, false_iff]; intro e; exact h (e ▸ a.2)

/-- Translate a list gate at a position with `k` wires below it: same operation, same number
of inputs. Total. -/
def conv (k : ℕ) (g : LGate) : KGate k := ⟨g.op, g.inputs.map (src k)⟩

@[simp] theorem conv_op (k : ℕ) (g : LGate) : (conv k g).op = g.op := rfl

@[simp] theorem conv_inputs_length (k : ℕ) (g : LGate) :
    (conv k g).inputs.length = g.inputs.length := by simp [conv]

@[simp] theorem conv_dflt (k : ℕ) : conv k dflt = KGate.const false := rfl

/-- The translated gate computes what the list gate computes. No hypothesis. -/
theorem conv_eval (k : ℕ) (g : LGate) (v : Fin k → Bool) :
    (conv k g).eval v = g.op.eval (g.inputs.map (rd k v)) := by
  simp only [KGate.eval, conv, List.map_map]
  congr 1
  exact List.map_congr_left fun j _ => eval_src k v j

/-- The translated gate reads exactly the in-range wires the list gate lists. -/
theorem mem_reads_conv {k : ℕ} {g : LGate} {a : Fin k} :
    a ∈ (conv k g).reads ↔ a.1 ∈ g.inputs := by
  rw [KGate.mem_reads]
  simp only [conv, List.mem_map, src_eq_wire]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact hj
  · exact fun h => ⟨a.1, h, rfl⟩

theorem isNot_conv (k : ℕ) {g : LGate} (hg : g.op ≠ GateOp.not) : (conv k g).isNot = false := by
  cases h : (conv k g).isNot
  · rfl
  · exact absurd (KGate.isNot_iff.mp h) hg

/-! ## The whole circuit -/

/-- **The bridge.** Gate `i` of the dag is the translation of list gate `i`. The size `s` is a
free parameter (use `gates.length`) so that `ofList (f gates) gates.length` needs no cast. -/
def ofList {n : ℕ} (gates : List LGate) (s : ℕ) : Dag n s :=
  ⟨fun i => conv (n + i) (gates.getD i dflt)⟩

@[simp] theorem ofList_gate {n : ℕ} (gates : List LGate) (s : ℕ) (i : Fin s) :
    (ofList gates s : Dag n s).gate i = conv (n + i) (gates.getD i dflt) := rfl

/-- Past the end the list fold reads `false`. -/
theorem listVal_ge {n : ℕ} (gs : List LGate) (x : Fin n → Bool) (j : ℕ)
    (hj : n + gs.length ≤ j) : L_meta_951_aux.val gs x j = false := by
  unfold L_meta_951_aux.val
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [L_meta_951_aux.fold_length]; simp; omega)]
  rfl

/-- A gate wire of the list fold is the gate applied to the values of the prefix. -/
theorem listVal_gate {n : ℕ} (gs : List LGate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    L_meta_951_aux.val gs x (n + j) =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => L_meta_951_aux.val (gs.take j) x i) := by
  have htk : gs.take (j + 1) = gs.take j ++ [gs[j]'hj] := List.take_succ_eq_append_getElem hj
  have hl : (gs.take j).length = j := by simp; omega
  have h := L_meta_951_aux.val_append (gs.take (j + 1)) (gs.drop (j + 1)) x (n + j)
    (by rw [htk]; simp; omega)
  rw [List.take_append_drop] at h
  rw [h, htk, L_meta_951_aux.val_snoc, if_pos (by rw [hl])]

/-- **Bridge theorem.** For EVERY list of gates (any operations, any fan-in, any reads), the
dag and the list fold have the same value at every wire index (both are `false` past the
end). -/
theorem ofList_valN {n : ℕ} (gates : List LGate) (x : Fin n → Bool) :
    ∀ i : ℕ, (ofList gates gates.length : Dag n _).valN x i = L_meta_951_aux.val gates x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < n + gates.length
    · rw [Dag.valN_of_lt _ _ hi]
      by_cases hn : i < n
      · have e : (⟨i, hi⟩ : Fin (n + gates.length)) = Fin.castAdd _ ⟨i, hn⟩ := rfl
        rw [e, Dag.val_castAdd]
        have h := L_meta_951_aux.val_append [] gates x i (by simpa using hn)
        rw [List.nil_append] at h
        rw [h, L_meta_951_aux.val_nil]; simp [hn]
      · have hj : i - n < gates.length := by omega
        have e : (⟨i, hi⟩ : Fin (n + gates.length)) = Fin.natAdd n ⟨i - n, hj⟩ :=
          Fin.ext (by simp; omega)
        have hw := listVal_gate gates x (i - n) hj
        rw [show n + (i - n) = i by omega] at hw
        rw [e, Dag.val_natAdd, ofList_gate, hw, conv_eval, List.getD_eq_getElem _ _ hj]
        congr 1
        apply List.map_congr_left
        intro t _
        unfold rd
        have hlen : (gates.take (i - n)).length = i - n := by
          rw [List.length_take]; omega
        split
        · next ht =>
          have ht' : t < i := by simp at ht; omega
          have h1 := ih t ht'
          rw [Dag.valN_of_lt _ _ (by omega)] at h1
          have h2 := L_meta_951_aux.val_append (gates.take (i - n)) (gates.drop (i - n)) x t
            (by rw [hlen]; omega)
          rw [List.take_append_drop] at h2
          rw [← h2, ← h1]
          rfl
        · next ht =>
          exact (listVal_ge _ x t (by rw [hlen]; simp at ht; omega)).symm
    · rw [Dag.valN_of_ge _ _ (by omega), listVal_ge gates x i (by omega)]

/-- The bridge with the size as a free parameter. -/
theorem ofList_valN' {n : ℕ} (gates : List LGate) (s : ℕ) (hs : gates.length = s)
    (x : Fin n → Bool) (i : ℕ) :
    (ofList gates s : Dag n s).valN x i = L_meta_951_aux.val gates x i := by
  subst hs; exact ofList_valN gates x i

/-- The bridge on in-range wires. -/
theorem ofList_val {n : ℕ} (gates : List LGate) (x : Fin n → Bool)
    (w : Fin (n + gates.length)) :
    (ofList gates gates.length : Dag n _).val x w = L_meta_951_aux.val gates x w.1 := by
  rw [← ofList_valN gates x w.1, Dag.valN_val]

/-- A property of all list gates and of `dflt` holds for every `getD`. -/
theorem getD_ind {P : LGate → Prop} {gates : List LGate} (h : ∀ g ∈ gates, P g) (h0 : P dflt)
    (i : ℕ) : P (gates.getD i dflt) := by
  by_cases hi : i < gates.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; exact h0

theorem ofList_notFree {n : ℕ} (gates : List LGate) (s : ℕ)
    (hg : ∀ g ∈ gates, g.op ≠ GateOp.not) : (ofList gates s : Dag n s).NotFree :=
  fun i => isNot_conv _ (getD_ind (P := fun g => g.op ≠ GateOp.not) hg (by simp [dflt]) i)

/-- AND/OR list circuits (any fan-in) translate to monotone dags. -/
theorem ofList_mono {n : ℕ} (gates : List LGate) (s : ℕ)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) : (ofList gates s : Dag n s).Mono :=
  Dag.mono_of_and_or _ fun i =>
    getD_ind (P := fun g => g.op = GateOp.and ∨ g.op = GateOp.or) hg (Or.inr rfl) i

/-- AND/OR/NOT list circuits (any fan-in) translate to dags fit for the sandwich. -/
theorem ofList_monoOffNot {n : ℕ} (gates : List LGate) (s : ℕ)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (ofList gates s : Dag n s).MonoOffNot := by
  intro i hi
  have h := getD_ind (P := fun g => g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    hg (Or.inr (Or.inl rfl)) i
  rcases h with h | h | h
  · exact opMono_of_and_or (Or.inl h)
  · exact opMono_of_and_or (Or.inr h)
  · rw [KGate.isNot_iff.mpr (by exact h)] at hi; exact absurd hi (by simp)

theorem getD_map_dflt (f : LGate → LGate) (hf : f dflt = dflt) (gates : List LGate) (i : ℕ) :
    (gates.map f).getD i dflt = f (gates.getD i dflt) := by
  by_cases h : i < gates.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h,
      List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega), hf]

/-- Two list circuits of the same length are related wirewise (in W951's `ℕ`-indexed form) as
soon as their dags are. -/
theorem listVal_rel_of_dag {n : ℕ} (gs gs' : List LGate) (hlen : gs'.length = gs.length)
    (x y : Fin n → Bool) (R : Bool → Bool → Prop) (hR : R false false)
    (h : ∀ w, R ((ofList gs gs.length : Dag n _).val x w)
      ((ofList gs' gs.length : Dag n _).val y w)) :
    ∀ i, R (L_meta_951_aux.val gs x i) (L_meta_951_aux.val gs' y i) := by
  intro i
  rw [← ofList_valN gs x i, ← ofList_valN' gs' gs.length hlen y i]
  by_cases hi : i < n + gs.length
  · rw [Dag.valN_of_lt _ _ hi, Dag.valN_of_lt _ _ hi]; exact h _
  · rw [Dag.valN_of_ge _ _ (not_lt.mp hi), Dag.valN_of_ge _ _ (not_lt.mp hi)]; exact hR

/-! ## W951 statements through the dag, with no extra hypothesis -/

/-- W951 `Charge.val_ge` / `MergeRun.mr_val_ge`. -/
theorem val_ge_viaDag {n : ℕ} (gs : List LGate) (x : Fin n → Bool) (j : ℕ)
    (hj : n + gs.length ≤ j) : L_meta_951_aux.val gs x j = false := by
  rw [← ofList_valN gs, Dag.valN_of_ge _ _ hj]

/-- W951 `Cases.mono_val`, exact statement (AND/OR gates of ANY fan-in), from `Dag.val_mono`. -/
theorem mono_val_viaDag {n : ℕ} (gs : List LGate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ c, x c = true → y c = true) :
    ∀ i, L_meta_951_aux.val gs x i = true → L_meta_951_aux.val gs y i = true :=
  listVal_rel_of_dag gs gs rfl x y (fun a b => a = true → b = true) id fun w =>
    Bool.le_iff_imp.mp
      (Dag.val_mono _ (ofList_mono gs _ hg) (fun c => Bool.le_iff_imp.mpr (hxy c)) w)

/-- W951's `Cone.mask` (same definition; `Cone.mask K gs` unfolds to this). -/
def lmask (K : Finset ℕ) (gs : List LGate) : List LGate :=
  gs.mapIdx fun k g => if k ∈ K then g else ⟨GateOp.or, []⟩

theorem lmask_length (K : Finset ℕ) (gs : List LGate) : (lmask K gs).length = gs.length := by
  simp [lmask]

/-- W951's `Cone.ReadClosed` (same definition). -/
def LReadClosed (n L : ℕ) (K : Finset ℕ) (gs : List LGate) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length), k ∈ K →
    ∀ i ∈ (gs[k]'hk).inputs, n ≤ i → i < n + L → i - n ∈ K

/-- The wire set of the kernel that corresponds to W951's set `K` of gate indices: all inputs,
and the gates in `K`. -/
def wiresOf (n s : ℕ) (K : Finset ℕ) (w : Fin (n + s)) : Prop := w.1 < n ∨ w.1 - n ∈ K

instance (n s : ℕ) (K : Finset ℕ) : DecidablePred (wiresOf n s K) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

theorem getD_lmask (K : Finset ℕ) (gs : List LGate) (i : ℕ) :
    (lmask K gs).getD i dflt = if i ∈ K then gs.getD i dflt else dflt := by
  by_cases h : i < gs.length
  · rw [List.getD_eq_getElem _ _ (by rw [lmask_length]; exact h), List.getD_eq_getElem _ _ h]
    simp [lmask, List.getElem_mapIdx, dflt]
  · rw [List.getD_eq_default _ _ (by rw [lmask_length]; omega),
      List.getD_eq_default _ _ (by omega)]
    simp

/-- W951's `mask` IS the kernel's `mask`: a syntactic equality of dags. -/
theorem ofList_lmask {n : ℕ} (K : Finset ℕ) (gs : List LGate) (s : ℕ) :
    (ofList (lmask K gs) s : Dag n s) = (ofList gs s).mask (wiresOf n s K) := by
  ext1
  funext i
  rw [ofList_gate, Dag.mask_gate, ofList_gate, getD_lmask]
  have : wiresOf n s K (Fin.natAdd n i) ↔ i.1 ∈ K := by simp [wiresOf]
  by_cases h : i.1 ∈ K
  · simp [h, this]
  · simp [h, this]

/-- W951's `ReadClosed` gives the kernel's `Closed`. -/
theorem closed_of_readClosed {n : ℕ} (K : Finset ℕ) (L : ℕ) (gs : List LGate)
    (hL : gs.length ≤ L) (hcl : LReadClosed n L K gs) :
    (ofList gs gs.length : Dag n _).Closed (wiresOf n gs.length K) := by
  intro i hi a ha
  have hiK : i.1 ∈ K := by simpa [wiresOf] using hi
  rw [ofList_gate, List.getD_eq_getElem _ _ i.2] at ha
  have hmem := mem_reads_conv.mp ha
  by_cases han : a.1 < n
  · exact Or.inl han
  · exact Or.inr (hcl i.1 i.2 hiK a.1 hmem (by omega) (by have := a.2; have := i.2; omega))

/-- W951 `Cone.val_mask`, exact statement (`lmask`/`LReadClosed` unfold to `mask`/`ReadClosed`),
from `Dag.val_mask`: masking with a read-closed set keeps the wires of the set. -/
theorem val_mask_viaDag {n : ℕ} (K : Finset ℕ) (L : ℕ) (x : Fin n → Bool) :
    ∀ gs : List LGate, gs.length ≤ L → LReadClosed n L K gs →
      ∀ i, (i < n ∨ i - n ∈ K ∨ n + gs.length ≤ i) →
        L_meta_951_aux.val (lmask K gs) x i = L_meta_951_aux.val gs x i := by
  intro gs hL hcl i hi
  rw [← ofList_valN' _ gs.length (lmask_length K gs), ← ofList_valN gs, ofList_lmask]
  by_cases hlt : i < n + gs.length
  · rw [Dag.valN_of_lt _ _ hlt, Dag.valN_of_lt _ _ hlt]
    refine Dag.val_mask _ _ (closed_of_readClosed K L gs hL hcl) x _ ?_
    rcases hi with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · omega
  · rw [Dag.valN_of_ge _ _ (not_lt.mp hlt), Dag.valN_of_ge _ _ (not_lt.mp hlt)]

/-- W951 `Cone.val_mask_out` (a masked-away gate is `false`), from `Dag.val_mask_out`. -/
theorem val_mask_out_viaDag {n : ℕ} (K : Finset ℕ) (gs : List LGate) (x : Fin n → Bool) (j : ℕ)
    (hj : j < gs.length) (hjK : j ∉ K) : L_meta_951_aux.val (lmask K gs) x (n + j) = false := by
  rw [← ofList_valN' _ gs.length (lmask_length K gs), ofList_lmask,
    Dag.valN_of_lt _ _ (by omega)]
  exact Dag.val_mask_out _ _ x ⟨j, hj⟩ (by simp [wiresOf, hjK])

end PEqualNP.Kernel
