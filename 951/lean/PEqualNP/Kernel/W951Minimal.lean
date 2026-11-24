import PEqualNP.Kernel.Minimal
import PEqualNP.Kernel.W951Core
import PEqualNP.W951.Cases

/-!
# Kernel/W951Minimal: the minimality operations on W951's `List Gate` circuits

The kernel passes of `Kernel/Minimal.lean`, restated for `gates : List Gate` through the total
bridge `ofList` and back through `toList` (an inverse of `ofList` on dags with no constant-`true`
input, `ofList_toList`).

* `list_keep`: for every set `K ⊆ range |gates|` of gate indices closed under past reads (the
  `PastClosed` of `W951/MinCEFacts.lean`, written out) and outputs inside `K` (or inputs, or out
  of range), there is a circuit with EXACTLY `K.card` gates, the same outputs, and gates that are
  gates of `gates` (in order, `ShapeMap`): fan-in and AND/OR/NOT shape and `AtMostOneNot` carry
  over (`ShapeMap.hg`, `ShapeMap.hU`).
* `list_restrictOutputs`: keep the cone of a set `O` of output wires; exact size
  `|gates'| + #outsideL O = |gates|`; `outsideL_card_ge`: every past-closed `K` containing the
  outputs has `|gates| ≤ K.card + #outsideL O`.
* `list_restrictVar`: fix `x_v := b`. Exact size `|gates'| + #deadL v b O = |gates|`; every
  output is constant on `{x v = b}` or is computed by `gates'` on EVERY input `x` as the original
  output at `update x v b`. Dead gates: `mem_deadL_of_copy` (equal to an earlier wire on
  `{x v = b}`), `mem_deadL_of_const`, `mem_deadL_of_reader` (AND/OR reading `x_v`, NOT whose first
  input is `x_v`).
* `restrictVar_bound`: from a bound `B` for shorter circuits (e.g. `MinCE.bound_lt`):
  `∑_{w ∈ I} (|S w \ v| - 1) + #deadL v b ≤ |gates|`, `I` = the sets that stay non-constant
  (`|S w \ v| ≥ 2`, and `v ∉ S w` when `b = true`). Corollaries `restrictVar_bound_true` (N3:
  `∑_{w ∌ v} (|S w| - 1) + #deadL v true ≤ |gates|`) and `restrictVar_bound_false` (N2:
  `∑_w (|S w| - 1) + #deadL v false ≤ |gates| + deg v`).
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open PEqualNP.Outside
open PEqualNP.Outside.L_meta_951_aux (AtMostOneNot)

local notation "lval" => L_meta_951_aux.val

variable {n : ℕ}

/-! ## From dags back to lists -/

/-- Encode an input: a wire by its index, a constant by the gate's own position (W951 reads it
as `false`). -/
def encSrc (k : ℕ) : Src k → ℕ
  | .wire a => a.1
  | .const _ => k

/-- Encode a gate. -/
def encGate (k : ℕ) (g : KGate k) : LGate := ⟨g.op, g.inputs.map (encSrc k)⟩

/-- Encode a dag as a W951 list circuit. -/
def toList {s : ℕ} (D : Dag n s) : List LGate := List.ofFn fun i : Fin s => encGate (n + i) (D.gate i)

@[simp] theorem toList_length {s : ℕ} (D : Dag n s) : (toList D).length = s := by simp [toList]

theorem toList_getElem {s : ℕ} (D : Dag n s) (t : ℕ) (ht : t < (toList D).length) :
    (toList D)[t] = encGate (n + t) (D.gate ⟨t, by simpa using ht⟩) := by simp [toList]

/-- No gate has a constant-`true` input (W951 has no encoding for it). -/
def NoTrue {s : ℕ} (D : Dag n s) : Prop := ∀ i, Src.const true ∉ (D.gate i).inputs

theorem src_encSrc (k : ℕ) (t : Src k) (ht : t ≠ Src.const true) : src k (encSrc k t) = t := by
  cases t with
  | wire a => simp [encSrc, src, a.2]
  | const b =>
    cases b
    · simp [encSrc, src]
    · exact absurd rfl ht

theorem ofList_toList {s : ℕ} (D : Dag n s) (h : NoTrue D) : (ofList (toList D) s : Dag n s) = D := by
  ext1
  funext i
  rw [ofList_gate, List.getD_eq_getElem _ _ (by simp), toList_getElem]
  have hi := h i
  simp only [Fin.eta]
  generalize D.gate i = g at hi ⊢
  obtain ⟨op, ins⟩ := g
  simp only [conv, encGate, List.map_map, KGate.mk.injEq, true_and]
  conv_rhs => rw [← List.map_id ins]
  exact List.map_congr_left fun t ht => src_encSrc _ t (fun e => hi (e ▸ ht))

theorem val_toList {s : ℕ} (D : Dag n s) (h : NoTrue D) (x : Fin n → Bool) (j : ℕ) :
    lval (toList D) x j = D.valN x j := by
  rw [← ofList_valN' (toList D) s (toList_length D) x j, ofList_toList D h]

theorem val_toList_wire {s : ℕ} (D : Dag n s) (h : NoTrue D) (x : Fin n → Bool)
    (w : Fin (n + s)) : lval (toList D) x w.1 = D.val x w := by
  rw [val_toList D h, Dag.valN_val]

/-! ## Shapes -/

/-- A kernel gate has the shape of a list gate: same operation (or a constant: AND/OR with no
input), and no more inputs. -/
def GS {k : ℕ} (g : KGate k) (h : LGate) : Prop :=
  (g.op = h.op ∨ (g.inputs = [] ∧ (g.op = GateOp.and ∨ g.op = GateOp.or))) ∧
    g.inputs.length ≤ h.inputs.length

/-- The gates of `gates'` are, in order (`e` strictly increasing), gates of `gates` or constants,
with no more inputs. -/
def ShapeMap (gates gates' : List LGate) (e : ℕ → ℕ) : Prop :=
  (∀ t t', t < t' → t' < gates'.length → e t < e t') ∧
  ∀ t (ht : t < gates'.length), ∃ he : e t < gates.length,
    (gates'[t].op = (gates[e t]'he).op ∨
      (gates'[t].inputs = [] ∧ (gates'[t].op = GateOp.and ∨ gates'[t].op = GateOp.or))) ∧
    gates'[t].inputs.length ≤ (gates[e t]'he).inputs.length

/-- The 951 gate shape carries over. -/
theorem ShapeMap.hg {gates gates' : List LGate} {e : ℕ → ℕ} (h : ShapeMap gates gates' e)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
  intro g hgm
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hgm
  obtain ⟨he, hop, hlen⟩ := h.2 t ht
  have := hg _ (List.getElem_mem he)
  refine ⟨?_, hlen.trans this.2⟩
  rcases hop with hop | ⟨-, hop⟩
  · rw [hop]; exact this.1
  · rcases hop with hop | hop
    · exact Or.inl hop
    · exact Or.inr (Or.inl hop)

/-- At most one NOT carries over. -/
theorem ShapeMap.hU {gates gates' : List LGate} {e : ℕ → ℕ} (h : ShapeMap gates gates' e)
    (hU : AtMostOneNot gates) : AtMostOneNot gates' := by
  intro t1 t2 h1 h2 n1 n2
  obtain ⟨he1, hop1, -⟩ := h.2 t1 h1
  obtain ⟨he2, hop2, -⟩ := h.2 t2 h2
  have k1 : (gates[e t1]'he1).op = GateOp.not := by
    rcases hop1 with hop | ⟨-, hop | hop⟩
    · rw [← hop]; exact n1
    · rw [n1] at hop; cases hop
    · rw [n1] at hop; cases hop
  have k2 : (gates[e t2]'he2).op = GateOp.not := by
    rcases hop2 with hop | ⟨-, hop | hop⟩
    · rw [← hop]; exact n2
    · rw [n2] at hop; cases hop
    · rw [n2] at hop; cases hop
  have := hU _ _ he1 he2 k1 k2
  rcases lt_trichotomy t1 t2 with h' | h' | h'
  · have := h.1 _ _ h' h2; omega
  · exact h'
  · have := h.1 _ _ h' h1; omega

theorem GS_ofList (gates : List LGate) (j : Fin gates.length) :
    GS ((ofList gates gates.length : Dag n _).gate j) gates[j] := by
  rw [ofList_gate, List.getD_eq_getElem _ _ j.2]
  exact ⟨Or.inl rfl, by simp⟩

/-- Encoding a compacted dag gives a `ShapeMap`. -/
theorem shapeMap_keep (gates : List LGate) (Dx : Dag n gates.length)
    (hx : ∀ j : Fin gates.length, GS (Dx.gate j) gates[j]) (K : Finset (Fin gates.length)) :
    ShapeMap gates (toList (Dx.keep K))
      (fun t => if h : t < K.card then (Dag.kemb K ⟨t, h⟩).1 else 0) := by
  refine ⟨fun t t' htt' ht' => ?_, fun t ht => ?_⟩
  · simp only [toList_length] at ht'
    dsimp only
    rw [dif_pos (by omega : t < K.card), dif_pos ht']
    exact Dag.kemb_strictMono K (show (⟨t, by omega⟩ : Fin K.card) < ⟨t', ht'⟩ from htt')
  · have ht' : t < K.card := by simpa using ht
    simp only [dif_pos ht']
    refine ⟨(Dag.kemb K ⟨t, ht'⟩).2, ?_⟩
    rw [toList_getElem]
    have := hx (Dag.kemb K ⟨t, ht'⟩)
    simp only [encGate, Dag.keep_gate_op, List.length_map, List.map_eq_nil_iff,
      Fin.getElem_fin] at this ⊢
    refine ⟨?_, (Dag.keep_gate_inputs_length Dx K _).trans_le this.2⟩
    rcases this.1 with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · refine Or.inr ⟨?_, h2⟩
      simp [Dag.keep_gate, KGate.bind, h1]

theorem noTrue_ofList (gates : List LGate) (s : ℕ) (j : Fin s) :
    Src.const true ∉ ((ofList gates s : Dag n s).gate j).inputs := by
  rw [ofList_gate]
  simp only [conv, List.mem_map, not_exists, not_and]
  intro i _ h
  unfold src at h
  split at h <;> simp at h

/-! ## Compaction and output deletion -/

/-- The gate indices of `K`, as a set of gates of the dag. -/
def finK (L : ℕ) (K : Finset ℕ) : Finset (Fin L) := Finset.univ.filter fun i => i.1 ∈ K

theorem card_finK {L : ℕ} {K : Finset ℕ} (hK : K ⊆ Finset.range L) : (finK L K).card = K.card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext j
  simp only [finK, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hj; exact ⟨⟨j, by simpa using hK hj⟩, hj, rfl⟩

/-- Past-closedness (W951 `MinCEFacts.PastClosed`) gives closedness of the dag. -/
theorem gclosed_finK (gates : List LGate) (K : Finset ℕ)
    (hP : ∀ (i : ℕ) (hi : i < gates.length), i ∈ K →
      ∀ j ∈ (gates[i]'hi).inputs, n ≤ j → j < n + i → j - n ∈ K) :
    (ofList gates gates.length : Dag n _).GClosed (finK gates.length K) := by
  intro i hi a ha hna
  rw [Dag.gw_natAdd] at hi
  simp only [finK, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rw [ofList_gate, List.getD_eq_getElem _ _ i.2] at ha
  exact hP i.1 i.2 hi a.1 (mem_reads_conv.mp ha) hna a.2

/-- **Compaction, list form** (subsumes `MinCEFacts.prune`): keep exactly the gates of a
past-closed `K`. -/
theorem list_keep (gates : List LGate) (K : Finset ℕ) (hK : K ⊆ Finset.range gates.length)
    (hP : ∀ (i : ℕ) (hi : i < gates.length), i ∈ K →
      ∀ j ∈ (gates[i]'hi).inputs, n ≤ j → j < n + i → j - n ∈ K)
    {m' : ℕ} (out : Fin m' → ℕ)
    (hout : ∀ w, out w < n ∨ (n ≤ out w ∧ out w - n ∈ K) ∨ n + gates.length ≤ out w) :
    ∃ (gates' : List LGate) (e : ℕ → ℕ) (out' : Fin m' → ℕ), gates'.length = K.card ∧
      ShapeMap gates gates' e ∧ ∀ (w : Fin m') (x : Fin n → Bool),
        lval gates' x (out' w) = lval gates x (out w) := by
  set G : Dag n gates.length := ofList gates gates.length
  set K' := finK gates.length K
  have hcl : G.GClosed K' := gclosed_finK gates K hP
  have hNT : NoTrue (G.keep K') := fun t => Dag.keep_const_true _ _ _ (noTrue_ofList _ _ _)
  have hex : ∀ w, ∃ o' : ℕ, ∀ x : Fin n → Bool,
      lval (toList (G.keep K')) x o' = lval gates x (out w) := by
    intro w
    by_cases hw : out w < n + gates.length
    · have hgw : Dag.gw K' (⟨out w, hw⟩ : Fin (n + gates.length)) := by
        intro hn
        simp only [K', finK, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hout w with h | ⟨-, h⟩ | h
        · exact absurd hn (by simp; omega)
        · exact h
        · exact absurd hw (by omega)
      obtain ⟨w', hw'⟩ := Dag.exists_ew K' _ hgw
      refine ⟨w'.1, fun x => ?_⟩
      rw [val_toList_wire _ hNT, Dag.val_keep _ _ hcl, hw', ofList_val]
    · refine ⟨n + K'.card, fun x => ?_⟩
      rw [val_ge_viaDag _ x _ (by simp), val_ge_viaDag _ x _ (by omega)]
  choose out' hout' using hex
  exact ⟨_, _, out', by rw [toList_length, card_finK hK],
    shapeMap_keep gates G (GS_ofList gates) K', hout'⟩

/-- The gates outside every cone of the wires `O` (as indices). -/
noncomputable def outsideL (n : ℕ) (gates : List LGate) (O : Finset ℕ) : Finset ℕ :=
  ((ofList gates gates.length : Dag n _).outsideGates fun w => w.1 ∈ O).map Fin.valEmbedding

/-- **Output deletion, list form.** Exact size `|gates'| + #outsideL O = |gates|`. -/
theorem list_restrictOutputs (gates : List LGate) (O : Finset ℕ) :
    ∃ (gates' : List LGate) (e r : ℕ → ℕ),
      gates'.length + (outsideL n gates O).card = gates.length ∧ ShapeMap gates gates' e ∧
      ∀ o ∈ O, ∀ x : Fin n → Bool, lval gates' x (r o) = lval gates x o := by
  set G : Dag n gates.length := ofList gates gates.length
  set P : Fin (n + gates.length) → Prop := fun w => w.1 ∈ O
  set K' := G.coneGates P
  have hcl : G.GClosed K' := G.coneGates_closed P
  have hNT : NoTrue (G.keep K') := fun t => Dag.keep_const_true _ _ _ (noTrue_ofList _ _ _)
  have hex : ∀ o, ∃ o' : ℕ, o ∈ O → ∀ x : Fin n → Bool,
      lval (toList (G.keep K')) x o' = lval gates x o := by
    intro o
    by_cases hw : o < n + gates.length
    · by_cases ho : o ∈ O
      · obtain ⟨w', hw'⟩ := Dag.exists_ew K' _
          (Dag.gw_coneGates (G.subset_cone P (o := ⟨o, hw⟩) ho))
        refine ⟨w'.1, fun _ x => ?_⟩
        rw [val_toList_wire _ hNT, Dag.val_keep _ _ hcl, hw', ofList_val]
      · exact ⟨0, fun h => absurd h ho⟩
    · refine ⟨n + K'.card, fun _ x => ?_⟩
      rw [val_ge_viaDag _ x _ (by simp), val_ge_viaDag _ x _ (by omega)]
  choose r hr using hex
  refine ⟨_, _, r, ?_, shapeMap_keep gates G (GS_ofList gates) K', fun o ho x => hr o ho x⟩
  rw [toList_length, outsideL, Finset.card_map]
  exact G.card_coneGates_add P

/-- Every past-closed set of gates containing the output gates bounds the cone:
`|gates| ≤ K.card + #outsideL O`. -/
theorem outsideL_card_ge (gates : List LGate) (O K : Finset ℕ) (hK : K ⊆ Finset.range gates.length)
    (hP : ∀ (i : ℕ) (hi : i < gates.length), i ∈ K →
      ∀ j ∈ (gates[i]'hi).inputs, n ≤ j → j < n + i → j - n ∈ K)
    (hO : ∀ o ∈ O, n ≤ o → o < n + gates.length → o - n ∈ K) :
    gates.length ≤ K.card + (outsideL n gates O).card := by
  have hsub : (ofList gates gates.length : Dag n _).coneGates (fun w => w.1 ∈ O) ⊆ finK gates.length K := by
    refine (ofList gates gates.length : Dag n _).coneGates_subset _ (gclosed_finK gates K hP)
      fun o ho hn => ?_
    simp only [finK, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hO o.1 ho hn o.2
  have h1 := Finset.card_le_card hsub
  rw [card_finK hK] at h1
  have h2 := (ofList gates gates.length : Dag n _).card_coneGates_add (fun w => w.1 ∈ O)
  rw [outsideL, Finset.card_map]
  omega

/-! ## Variable restriction -/

/-- The gates that die under `x_v := b` with outputs `O` (as indices). -/
noncomputable def deadL (gates : List LGate) (v : Fin n) (b : Bool) (O : Finset ℕ) : Finset ℕ :=
  ((ofList gates gates.length : Dag n _).deadGates (fun x => x v = b)
    fun w => w.1 ∈ O).map Fin.valEmbedding

/-- **Variable restriction, list form.** -/
theorem list_restrictVar (gates : List LGate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (v : Fin n) (b : Bool) (O : Finset ℕ) :
    ∃ (gates' : List LGate) (e r : ℕ → ℕ),
      gates'.length + (deadL gates v b O).card = gates.length ∧ ShapeMap gates gates' e ∧
      ∀ o ∈ O, (∃ c, ∀ x : Fin n → Bool, x v = b → lval gates x o = c) ∨
        ∀ x : Fin n → Bool, lval gates' x (r o) = lval gates (Function.update x v b) o := by
  set G : Dag n gates.length := ofList gates gates.length
  set A : (Fin n → Bool) → Prop := fun x => x v = b
  set P : Fin (n + gates.length) → Prop := fun w => w.1 ∈ O
  have hNT : NoTrue (G.restrictVar v b P) := by
    intro t
    refine Dag.keep_const_true _ _ _ (Dag.prop_const_true _ ?_)
    rw [ofList_gate, conv_op]
    exact getD_ind (P := fun g => g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
      hops (Or.inr (Or.inl rfl)) _
  have hex : ∀ o, ∃ o' : ℕ, o ∈ O → ((∃ c, ∀ x : Fin n → Bool, x v = b → lval gates x o = c) ∨
      ∀ x : Fin n → Bool, lval (toList (G.restrictVar v b P)) x o' =
        lval gates (Function.update x v b) o) := by
    intro o
    by_cases hw : o < n + gates.length
    · by_cases ho : o ∈ O
      · rcases G.val_restrictVar v b P ⟨o, hw⟩ ho with ⟨c, hc⟩ | ⟨o', ho'⟩
        · exact ⟨0, fun _ => Or.inl ⟨c, fun x hx =>
            (ofList_val gates x ⟨o, hw⟩).symm.trans (hc x hx)⟩⟩
        · refine ⟨o'.1, fun _ => Or.inr fun x => ?_⟩
          rw [val_toList_wire _ hNT, ho', ofList_val]
      · exact ⟨0, fun h => absurd h ho⟩
    · exact ⟨0, fun _ => Or.inl ⟨false, fun x _ => val_ge_viaDag _ x _ (by omega)⟩⟩
  choose r hr using hex
  refine ⟨_, _, r, ?_, shapeMap_keep gates (G.prop A) ?_ _, fun o ho => hr o ho⟩
  · rw [toList_length, deadL, Finset.card_map]
    exact G.card_simplify A P
  · intro j
    obtain ⟨h1, h2⟩ := Dag.prop_gate_shape (D := G) (A := A) j
    obtain ⟨-, g2⟩ := GS_ofList (n := n) gates j
    have g1 : (G.gate j).op = gates[j].op := by
      rw [ofList_gate, List.getD_eq_getElem _ _ j.2]; rfl
    refine ⟨?_, h2.trans g2⟩
    rcases h1 with h1 | h1
    · exact Or.inl (h1.trans g1)
    · exact Or.inr h1

theorem mem_deadL_of_constOrCopy (gates : List LGate) (v : Fin n) (b : Bool) (O : Finset ℕ)
    (k : ℕ) (hk : k < gates.length)
    (h : (ofList gates gates.length : Dag n _).ConstOrCopy (fun x => x v = b) ⟨k, hk⟩) :
    k ∈ deadL gates v b O :=
  Finset.mem_map.mpr ⟨⟨k, hk⟩, Dag.mem_deadGates_of_constOrCopy h, rfl⟩

/-- A gate equal, on `{x v = b}`, to an earlier wire is dead (W951 `DCp`, `DC1`). -/
theorem mem_deadL_of_copy (gates : List LGate) (v : Fin n) (b : Bool) (O : Finset ℕ)
    (k : ℕ) (hk : k < gates.length) (j : ℕ) (hj : j < n + k)
    (h : ∀ x : Fin n → Bool, x v = b → lval gates x (n + k) = lval gates x j) :
    k ∈ deadL gates v b O := by
  refine mem_deadL_of_constOrCopy gates v b O k hk
    (Dag.constOrCopy_of_copy (u := ⟨j, by omega⟩) (by rw [Fin.lt_def]; simpa using hj)
      fun x hx => ?_)
  rw [ofList_val, ofList_val]
  exact (h x hx).symm

/-- A gate constant on `{x v = b}` is dead (W951 `DTr`, `GeqV`). -/
theorem mem_deadL_of_const (gates : List LGate) (v : Fin n) (b : Bool) (O : Finset ℕ)
    (k : ℕ) (hk : k < gates.length) (c : Bool)
    (h : ∀ x : Fin n → Bool, x v = b → lval gates x (n + k) = c) :
    k ∈ deadL gates v b O :=
  mem_deadL_of_constOrCopy gates v b O k hk
    (Dag.constOrCopy_of_const fun x hx => by rw [ofList_val]; exact h x hx)

/-- A reader of `x_v` (AND/OR of fan-in ≤ 2 with `v` among its inputs, or NOT with first input
`v`; W951 `MinCEFacts.Readers`) is dead under `x_v := b`. -/
theorem mem_deadL_of_reader (gates : List LGate) (v : Fin n) (b : Bool) (O : Finset ℕ)
    (k : ℕ) (hk : k < gates.length) (hlen : (gates[k]'hk).inputs.length ≤ 2)
    (h : (((gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or) ∧
        (v : ℕ) ∈ (gates[k]'hk).inputs) ∨
      ((gates[k]'hk).op = GateOp.not ∧ ∃ rest, (gates[k]'hk).inputs = (v : ℕ) :: rest)) :
    k ∈ deadL gates v b O := by
  set G : Dag n gates.length := ofList gates gates.length
  have hvk : (v : ℕ) < n + k := by have := v.2; omega
  have hlift : lift (⟨k, hk⟩ : Fin gates.length) (⟨v, hvk⟩ : Fin (n + k)) =
      Fin.castAdd gates.length v := Fin.ext rfl
  have hgate : G.gate ⟨k, hk⟩ = conv (n + k) (gates[k]'hk) := by
    rw [ofList_gate, List.getD_eq_getElem _ _ hk]
  have he : G.EffReads ⟨k, hk⟩ (Fin.castAdd gates.length v) := by
    unfold Dag.EffReads
    rw [hgate]
    rcases h with ⟨hop, hv⟩ | ⟨hop, rest, hin⟩
    · exact Or.inl ⟨by simpa using hop, by simpa using hlen,
        ⟨v, hvk⟩, mem_reads_conv.mpr hv, hlift⟩
    · refine Or.inr ⟨by simpa using hop, ⟨v, hvk⟩, ?_, hlift⟩
      simp only [conv, hin, List.map_cons, List.head?_cons, Option.some.injEq]
      simp [src, hvk]
  exact mem_deadL_of_constOrCopy gates v b O k hk
    (Dag.constOrCopy_of_effReads he (G.isConst_var v b))

/-! ## The bound for the restricted problem -/

/-- **Restriction bound.** Given a lower bound `B` for circuits shorter than `gates` (e.g.
`MinCE.bound_lt`), a correct circuit with at least one dead gate under `x_v := b` satisfies
`∑_{w ∈ I} (|S w \ v| - 1) + #deadL v b ≤ |gates|`, where `I` are the sets with `|S w \ v| ≥ 2`
that do not become constant (`b = false` or `v ∉ S w`). -/
theorem restrictVar_bound {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List LGate)
    (out : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), lval gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (B : ∀ (m' : ℕ) (S' : Fin m' → Finset (Fin n)) (gates' : List LGate) (out' : Fin m' → ℕ),
      gates'.length < gates.length →
      (∀ i : Fin m', 2 ≤ (S' i).card) → (∀ i j : Fin m', i ≠ j → (S' i ∩ S' j).card ≤ 1) →
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates' →
      (∀ (w : Fin m') (x : Fin n → Bool), lval gates' x (out' w) = decide (∃ u ∈ S' w, x u = true)) →
      ∑ i : Fin m', ((S' i).card - 1) ≤ gates'.length)
    (v : Fin n) (b : Bool) (hd : 1 ≤ (deadL gates v b (Finset.univ.image out)).card) :
    ∑ w ∈ Finset.univ.filter (fun w => 2 ≤ ((S w).erase v).card ∧ (b = false ∨ v ∉ S w)),
        (((S w).erase v).card - 1) + (deadL gates v b (Finset.univ.image out)).card ≤
      gates.length := by
  classical
  set I := Finset.univ.filter (fun w => 2 ≤ ((S w).erase v).card ∧ (b = false ∨ v ∉ S w))
  obtain ⟨gates', e, r, hlen, hsh, hval⟩ := list_restrictVar gates (fun g hg' => (hg g hg').1)
    v b (Finset.univ.image out)
  -- the outputs of `I` are computed by `gates'`, on every input
  have hI : ∀ w ∈ I, ∀ x : Fin n → Bool,
      lval gates' x (r (out w)) = decide (∃ u ∈ (S w).erase v, x u = true) := by
    intro w hw x
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨hw2, hwb⟩ := hw
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < ((S w).erase v).card)
    have huv : u ≠ v := Finset.ne_of_mem_erase hu
    have hev' : ∀ y : Fin n → Bool, y v = b →
        lval gates y (out w) = decide (∃ u ∈ (S w).erase v, y u = true) := by
      intro y hy
      rw [hev]
      congr 1
      apply propext
      constructor
      · rintro ⟨u', hu', hy'⟩
        refine ⟨u', Finset.mem_erase.mpr ⟨fun e => ?_, hu'⟩, hy'⟩
        subst e
        rcases hwb with hb | hb
        · rw [hy, hb] at hy'; cases hy'
        · exact hb hu'
      · rintro ⟨u', hu', hy'⟩; exact ⟨u', Finset.mem_of_mem_erase hu', hy'⟩
    rcases hval (out w) (Finset.mem_image_of_mem _ (Finset.mem_univ w)) with ⟨c, hc⟩ | hc
    · exfalso
      set x0 : Fin n → Bool := Function.update (fun _ => false) v b
      have hx0 : x0 v = b := by simp [x0]
      have hx1 : (Function.update x0 u true) v = b := by
        rw [Function.update_of_ne huv.symm]; exact hx0
      have e0 := (hev' x0 hx0).symm.trans (hc x0 hx0)
      have e1 := (hev' _ hx1).symm.trans (hc _ hx1)
      have : decide (∃ u' ∈ (S w).erase v, x0 u' = true) = false := by
        simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro u' hu'
        simp [x0, Function.update_of_ne (Finset.ne_of_mem_erase hu')]
      have h1 : decide (∃ u' ∈ (S w).erase v, (Function.update x0 u true) u' = true) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨u, hu, by simp⟩
      rw [this] at e0
      rw [h1, ← e0] at e1
      cases e1
    · rw [hc x, hev' _ (by simp)]
      congr 1
      apply propext
      constructor
      · rintro ⟨u', hu', hy'⟩
        exact ⟨u', hu', by rwa [Function.update_of_ne (Finset.ne_of_mem_erase hu')] at hy'⟩
      · rintro ⟨u', hu', hy'⟩
        exact ⟨u', hu', by rwa [Function.update_of_ne (Finset.ne_of_mem_erase hu')]⟩
  -- the subfamily
  let eI : Fin I.card ≃ I := I.equivFin.symm
  have hB := B I.card (fun i => (S (eI i).1).erase v) gates' (fun i => r (out (eI i).1))
    (by omega)
    (fun i => by
      have := (eI i).2
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this.1)
    (fun i j hij => by
      have hne : (eI i).1 ≠ (eI j).1 := fun h => hij (eI.injective (Subtype.ext h))
      refine le_trans (Finset.card_le_card ?_) (hS _ _ hne)
      intro t ht
      simp only [Finset.mem_inter, Finset.mem_erase] at ht
      exact Finset.mem_inter.mpr ⟨ht.1.2, ht.2.2⟩)
    (hsh.hg hg) (hsh.hU hU) (fun i x => hI _ (eI i).2 x)
  have hsum : ∑ i : Fin I.card, (((S (eI i).1).erase v).card - 1) =
      ∑ w ∈ I, (((S w).erase v).card - 1) := by
    exact PEqualNP.Base.Matching.sum_equivFin I (fun w => (((S w).erase v).card - 1))
  omega

/-- **N3** (`MinCEDraft.liveBound1` shape): `x_v := 1`. -/
theorem restrictVar_bound_true {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List LGate)
    (out : Fin m → ℕ) (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), lval gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (B : ∀ (m' : ℕ) (S' : Fin m' → Finset (Fin n)) (gates' : List LGate) (out' : Fin m' → ℕ),
      gates'.length < gates.length →
      (∀ i : Fin m', 2 ≤ (S' i).card) → (∀ i j : Fin m', i ≠ j → (S' i ∩ S' j).card ≤ 1) →
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates' →
      (∀ (w : Fin m') (x : Fin n → Bool), lval gates' x (out' w) = decide (∃ u ∈ S' w, x u = true)) →
      ∑ i : Fin m', ((S' i).card - 1) ≤ gates'.length)
    (v : Fin n) (hd : 1 ≤ (deadL gates v true (Finset.univ.image out)).card) :
    ∑ w ∈ Finset.univ.filter (fun w => v ∉ S w), ((S w).card - 1) +
      (deadL gates v true (Finset.univ.image out)).card ≤ gates.length := by
  classical
  have h := restrictVar_bound S gates out hS hg hU hev B v true hd
  have e : Finset.univ.filter (fun w => 2 ≤ ((S w).erase v).card ∧ (true = false ∨ v ∉ S w)) =
      Finset.univ.filter (fun w => v ∉ S w) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.true_eq_false, false_or]
    constructor
    · exact fun h => h.2
    · intro hv; exact ⟨by rw [Finset.erase_eq_of_notMem hv]; exact h2 w, hv⟩
  rw [e] at h
  have e2 : ∑ w ∈ Finset.univ.filter (fun w => v ∉ S w), (((S w).erase v).card - 1) =
      ∑ w ∈ Finset.univ.filter (fun w => v ∉ S w), ((S w).card - 1) := by
    refine Finset.sum_congr rfl fun w hw => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rw [Finset.erase_eq_of_notMem hw]
  omega

/-- **N2** (`MinCEFacts.deadBound` shape, with `#deadL v false ≥ #DC v`): `x_v := 0`. -/
theorem restrictVar_bound_false {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List LGate)
    (out : Fin m → ℕ) (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), lval gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (B : ∀ (m' : ℕ) (S' : Fin m' → Finset (Fin n)) (gates' : List LGate) (out' : Fin m' → ℕ),
      gates'.length < gates.length →
      (∀ i : Fin m', 2 ≤ (S' i).card) → (∀ i j : Fin m', i ≠ j → (S' i ∩ S' j).card ≤ 1) →
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates' →
      (∀ (w : Fin m') (x : Fin n → Bool), lval gates' x (out' w) = decide (∃ u ∈ S' w, x u = true)) →
      ∑ i : Fin m', ((S' i).card - 1) ≤ gates'.length)
    (v : Fin n) (hd : 1 ≤ (deadL gates v false (Finset.univ.image out)).card) :
    ∑ i : Fin m, ((S i).card - 1) + (deadL gates v false (Finset.univ.image out)).card ≤
      gates.length + (Finset.univ.filter fun w : Fin m => v ∈ S w).card := by
  classical
  have h := restrictVar_bound S gates out hS hg hU hev B v false hd
  simp only [true_or, and_true] at h
  set I := Finset.univ.filter (fun w : Fin m => 2 ≤ ((S w).erase v).card)
  -- termwise: `|S w| - 1 ≤ (if w ∈ I then |S w \ v| - 1 else 0) + [v ∈ S w]`
  have key : ∀ w : Fin m, (S w).card - 1 ≤
      (if w ∈ I then ((S w).erase v).card - 1 else 0) + (if v ∈ S w then 1 else 0) := by
    intro w
    have h2w := h2 w
    by_cases hv : v ∈ S w
    · have := Finset.card_erase_of_mem hv
      by_cases hI : w ∈ I
      · rw [if_pos hI, if_pos hv]; omega
      · simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hI
        rw [if_neg (by simp [I]; omega), if_pos hv]; omega
    · have := Finset.erase_eq_of_notMem hv
      have hI : w ∈ I := by simp [I, this, h2w]
      rw [if_pos hI, if_neg hv, this]; simp
  have hsum := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => key w
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hsum
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.filter_mem_eq_inter,
    Finset.univ_inter] at hsum
  omega

end PEqualNP.Kernel
