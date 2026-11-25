import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.MergeRun
import PEqualNP.W951.Cases

/-! Theorem P (payment lemma, scaffold notes `work/notes951/payment_lemma.md`): setting,
definitions and the lemmas proved so far (no sorry). The remaining lemmas and the assembly
are in `PayDraft.lean`.

Setting: one NOT gate `kN` reading only the wire `hw`, with `hw = x_a ∨ x_b` as a function.
Per set `w`: frame `Q w ∈ {S w, S w ∪ {a,b}}`, a read-closed gate set `K w` (the cone),
`Good (Q w) (mask (K w) gates)`; merges `M w` = the explicit unit-vector union-find run of
MergeRun.lean on `mask (K w) gates`. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Structure of a merge gate (generic, for the explicit run of MergeRun.lean) -/

theorem mg_card_le_one {n : ℕ} (T : Finset (Fin n)) (l : Fin n → Fin n) (c0 : Fin n)
    (h : ∀ u ∈ T, l u = c0) : (T.image l).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  rw [h u hu, h v hv]

/-- A merge gate of the explicit run is an OR of two earlier tracked wires whose traces within
`R` are nonempty and lie in different classes. -/
theorem mg_split {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (hgood : Good Q gs) (j : ℕ)
    (hm : Mg Q R gs (runL Q R gs j) j) :
    ∃ hj : j < gs.length, (gs[j]'hj).op = GateOp.or ∧ ∃ α β, (gs[j]'hj).inputs = [α, β] ∧
      α < n + j ∧ β < n + j ∧ val gs (Zof Q) α = false ∧ val gs (Zof Q) β = false ∧
      (∀ x : Fin n → Bool, val gs x (n + j) = (val gs x α || val gs x β)) ∧
      (∃ u ∈ R, val gs (eof u) α = true) ∧ (∃ v ∈ R, val gs (eof v) β = true) ∧
      ∀ u ∈ R, ∀ v ∈ R, val gs (eof u) α = true → val gs (eof v) β = true →
        runL Q R gs j u ≠ runL Q R gs j v := by
  have hinv := runL_inv Q R gs j
  obtain ⟨hz, hcard⟩ := hm
  obtain ⟨x0, hx0⟩ := Finset.card_pos.mp
    (by omega : 0 < ((trR R gs (n + j)).image (runL Q R gs j)).card)
  obtain ⟨u0, hu0, -⟩ := Finset.mem_image.mp hx0
  rw [trR, Finset.mem_filter] at hu0
  have one : ∀ a, a < n + j → val gs (Zof Q) a = false →
      (∀ u ∈ R, val gs (eof u) (n + j) = true → val gs (eof u) a = true) → False := by
    intro a ha hza hsub
    have : ((trR R gs (n + j)).image (runL Q R gs j)).card ≤ 1 :=
      mg_card_le_one _ _ (runL Q R gs j u0) (fun u hu => by
        rw [trR, Finset.mem_filter] at hu
        exact hinv a ha hza u hu.1 u0 hu0.1 (hsub u hu.1 hu.2) (hsub u0 hu0.1 hu0.2))
    omega
  have hj : j < gs.length := by
    by_contra h
    have := hu0.2
    rw [mr_val_ge gs _ _ (by omega)] at this
    exact absurd this (by simp)
  refine ⟨hj, ?_⟩
  have hval := fun (x : Fin n → Bool) => mr_val_gate gs x j hj
  have ftk : ∀ (x : Fin n → Bool) i,
      val (gs.take j) x i = if i < n + j then val gs x i else false := by
    intro x i
    split_ifs with hi
    · exact (mr_val_take gs x j i hi).symm
    · exact mr_val_ge _ x i (by rw [List.length_take, Nat.min_eq_left hj.le]; omega)
  have hg := hgood _ _ _ (mr_split gs j hj)
  generalize gs[j]'hj = g at hval hg ⊢
  obtain ⟨op, ins⟩ := g
  simp only at hval hg ⊢
  rcases hg with ⟨hop, hlen⟩ | h | h
  swap
  · exfalso
    rw [hval] at hz
    rw [hz] at h
    exact absurd h (by simp)
  swap
  · exfalso
    have := hu0.2
    rw [hval, h u0] at this
    exact absurd this (by simp)
  have hu0' := hu0.2
  rcases ins with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · exfalso
    rcases hop with rfl | rfl
    · rw [hval] at hz; simp [GateOp.eval] at hz
    · rw [hval] at hu0'; simp [GateOp.eval] at hu0'
  · exfalso
    have hv1 : ∀ y : Fin n → Bool, val gs y (n + j) = if x < n + j then val gs y x else false := by
      intro y
      rw [hval]
      rcases hop with rfl | rfl <;> simp [GateOp.eval, ftk]
    by_cases hx : x < n + j
    · simp only [hv1, hx, ite_true] at hz hu0'
      exact one x hx hz (fun u _ h => by rw [hv1, ite_eq_left hx] at h; exact h)
    · rw [hv1, ite_eq_right hx] at hu0'
      exact absurd hu0' (by simp)
  · rcases hop with rfl | rfl
    · exfalso
      have hv2 : ∀ w : Fin n → Bool, val gs w (n + j) =
          ((if x < n + j then val gs w x else false) &&
            (if y < n + j then val gs w y else false)) := by
        intro w; rw [hval]; simp [GateOp.eval, ftk]
      have hz' := hz
      rw [hv2] at hz' hu0'
      by_cases hx : x < n + j <;> by_cases hy : y < n + j <;>
        simp only [hx, hy, ite_true, ite_false, Bool.and_false, Bool.false_and] at hz' hu0'
      · rcases Bool.and_eq_false_iff.mp hz' with h | h
        · exact one x hx h (fun u _ hu => by
            rw [hv2, ite_eq_left hx, ite_eq_left hy] at hu; exact (Bool.and_eq_true _ _ ▸ hu).1)
        · exact one y hy h (fun u _ hu => by
            rw [hv2, ite_eq_left hx, ite_eq_left hy] at hu; exact (Bool.and_eq_true _ _ ▸ hu).2)
      all_goals exact absurd hu0' (by simp)
    · have hv2 : ∀ w : Fin n → Bool, val gs w (n + j) =
          ((if x < n + j then val gs w x else false) ||
            (if y < n + j then val gs w y else false)) := by
        intro w; rw [hval]; simp [GateOp.eval, ftk]
      have hz' := hz
      rw [hv2] at hz' hu0'
      by_cases hx : x < n + j <;> by_cases hy : y < n + j
      · simp only [hx, hy, ite_true, Bool.or_eq_false_iff] at hz'
        have hv3 : ∀ w : Fin n → Bool, val gs w (n + j) = (val gs w x || val gs w y) := by
          intro w; rw [hv2, ite_eq_left hx, ite_eq_left hy]
        refine ⟨rfl, x, y, rfl, hx, hy, hz'.1, hz'.2, hv3, ?_, ?_, ?_⟩
        · by_contra hno
          push Not at hno
          exact one y hy hz'.2 (fun u hu h => by
            rw [hv3] at h
            rcases Bool.or_eq_true_iff.mp h with h | h
            · exact absurd h (hno u hu)
            · exact h)
        · by_contra hno
          push Not at hno
          exact one x hx hz'.1 (fun u hu h => by
            rw [hv3] at h
            rcases Bool.or_eq_true_iff.mp h with h | h
            · exact h
            · exact absurd h (hno u hu))
        · intro u hu v hv hux hvy heq
          have : ((trR R gs (n + j)).image (runL Q R gs j)).card ≤ 1 :=
            mg_card_le_one _ _ (runL Q R gs j u) (fun w hw => by
              rw [trR, Finset.mem_filter, hv3] at hw
              rcases Bool.or_eq_true_iff.mp hw.2 with h | h
              · exact hinv x hx hz'.1 w hw.1 u hu h hux
              · rw [heq]; exact hinv y hy hz'.2 w hw.1 v hv h hvy)
          omega
      · exfalso
        simp only [hx, hy, ite_true, ite_false, Bool.or_false] at hz'
        exact one x hx hz' (fun u _ h => by
          rw [hv2, ite_eq_left hx, ite_eq_right hy, Bool.or_false] at h; exact h)
      · exfalso
        simp only [hx, hy, ite_true, ite_false, Bool.false_or] at hz'
        exact one y hy hz' (fun u _ h => by
          rw [hv2, ite_eq_right hx, ite_eq_left hy, Bool.false_or] at h; exact h)
      · exfalso
        simp only [hx, hy, ite_false, Bool.or_false] at hu0'
        exact absurd hu0' (by simp)
  · exfalso
    simp at hlen

structure PaySetting (n m : ℕ) where
  gates : List Gate
  S : Fin m → Finset (Fin n)
  out : Fin m → ℕ
  hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2
  hU : AtMostOneNot gates
  hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)
  hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1
  a : Fin n
  b : Fin n
  hab : a ≠ b
  hw : ℕ
  hhw : ∀ x : Fin n → Bool, val gates x hw = (x a || x b)
  kN : ℕ
  hkN : kN < gates.length
  hNop : (gates[kN]'hkN).op = GateOp.not
  hNin : ∀ i ∈ (gates[kN]'hkN).inputs, i = hw
  Q : Fin m → Finset (Fin n)
  hQ : ∀ w, Q w = S w ∨ Q w = S w ∪ {a, b}
  K : Fin m → Finset ℕ
  hcl : ∀ w, ReadClosed n gates.length (K w) gates
  hout : ∀ w, out w < n ∨ out w - n ∈ K w ∨ n + gates.length ≤ out w
  hgood : ∀ w, Good (Q w) (mask (K w) gates)

namespace PaySetting

variable {n m : ℕ} (P : PaySetting n m)

/-! ## Definitions -/

def Pa (w : Fin m) : Prop := P.a ∈ P.S w ∧ P.b ∉ P.S w
def Pb (w : Fin m) : Prop := P.b ∈ P.S w ∧ P.a ∉ P.S w

/-- Crossing pair `(w, w')` with point `c` (`w` on the a-side). -/
def Cross (w w' : Fin m) (c : Fin n) : Prop :=
  P.Pa w ∧ P.Pb w' ∧ P.S w ∩ P.S w' = {c} ∧ c ≠ P.a ∧ c ≠ P.b

def Partner (w v : Fin m) : Prop := ∃ c, P.Cross w v c ∨ P.Cross v w c

open Classical in
/-- Crossing degree. -/
noncomputable def deg (w : Fin m) : ℕ := (Finset.univ.filter fun v => P.Partner w v).card

/-- The merges of set `w` (explicit union-find run, cone-masked circuit, unit vectors). -/
noncomputable def M (w : Fin m) : Finset ℕ :=
  runM (P.Q w) (P.S w) (mask (P.K w) P.gates) P.gates.length

/-- The counted wires of set `w`. -/
noncomputable def Dd (w : Fin m) : Finset ℕ := D (P.Q w) (P.S w) (mask (P.K w) P.gates)

def Coll (i : ℕ) : Prop := ∃ w w', w ≠ w' ∧ i ∈ P.M w ∧ i ∈ P.M w'

def opAt (i : ℕ) (op : GateOp) : Prop :=
  ∃ k, ∃ hk : k < P.gates.length, i = n + k ∧ (P.gates[k]'hk).op = op

open Classical in
noncomputable def coll : Finset ℕ := (Finset.Ico n (n + P.gates.length)).filter P.Coll
open Classical in
noncomputable def ands : Finset ℕ :=
  (Finset.Ico n (n + P.gates.length)).filter fun i => P.opAt i GateOp.and
open Classical in
noncomputable def ors : Finset ℕ :=
  (Finset.Ico n (n + P.gates.length)).filter fun i => P.opAt i GateOp.or
open Classical in
/-- Uncharged OR gates. -/
noncomputable def unch : Finset ℕ := P.ors.filter fun i => ∀ w, i ∉ P.M w
noncomputable def allM : Finset ℕ := Finset.univ.biUnion P.M

def base : ℕ := ∑ w, ((P.S w).card - 1)

/-- Hypothesis (H*). -/
def HStar : Prop :=
  ∀ i w w' c, P.Cross w w' c → i ∈ P.M w → i ∈ P.M w' → P.deg w = 1 ∨ P.deg w' = 1

/-- A read edge `i → n + k` (only reads of earlier wires are meaningful). -/
def Reads (i j : ℕ) : Prop :=
  ∃ k, ∃ hk : k < P.gates.length, j = n + k ∧ i < j ∧ i ∈ (P.gates[k]'hk).inputs

def IsPath (L : List ℕ) (s t : ℕ) : Prop :=
  List.IsChain P.Reads L ∧ L.head? = some s ∧ L.getLast? = some t

/-- Every wire on `L` is 1 at the point `y`. -/
def LiveAt (y : Fin n → Bool) (L : List ℕ) : Prop := ∀ i ∈ L, val P.gates y i = true

/-- Position `t + 1` of `L` is a kill at `y`. -/
def KillAt (L : List ℕ) (y : Fin n → Bool) (t : ℕ) : Prop :=
  ∃ h : t + 1 < L.length, val P.gates y (L[t]'(by omega)) = true ∧
    val P.gates y (L[t + 1]'h) = false

/-- Crossing point of some collision gate. -/
def CPt (x : Fin n) : Prop := ∃ i w w', P.Cross w w' x ∧ i ∈ P.M w ∧ i ∈ P.M w'

/-- `X_g = {k̄} ∪ (C* \ {c})`. -/
def Xg (c kbar x : Fin n) : Prop := x = kbar ∨ (P.CPt x ∧ x ≠ c)

/-- Choice of paying side `T` (crossing degree 1) for collision gate `g` with point `c`. -/
def SideOK (g : ℕ) (T : Fin m) (c kbar : Fin n) : Prop :=
  ∃ w w', P.Cross w w' c ∧ g ∈ P.M w ∧ g ∈ P.M w' ∧
    ((T = w ∧ P.deg w = 1 ∧ kbar = P.b) ∨ (T = w' ∧ P.deg w' = 1 ∧ kbar = P.a))

def LivePayer (g p : ℕ) : Prop :=
  ∃ T c kbar, P.SideOK g T c kbar ∧ ∃ L, P.IsPath L g (P.out T) ∧ P.LiveAt (eof c) L ∧
    ∃ t, ∃ h : t + 1 < L.length, L[t + 1] = p ∧ (∃ x, P.Xg c kbar x ∧ P.KillAt L (eof x) t) ∧
      ∀ t', t < t' → ∀ x, P.Xg c kbar x → ¬ P.KillAt L (eof x) t'

def BypassPayer (g p : ℕ) : Prop :=
  ∃ T c kbar, P.SideOK g T c kbar ∧
    (¬ ∃ L, P.IsPath L g (P.out T) ∧ P.LiveAt (eof c) L) ∧ p ∈ P.Dd T ∧ p ∈ P.unch

def Payer (g p : ℕ) : Prop := P.LivePayer g p ∨ P.BypassPayer g p

/-- `C⁻`: gate `k` rewired to `OR(α, α)`. -/
def rewire (k α : ℕ) : List Gate := P.gates.set k ⟨GateOp.or, [α, α]⟩


/-! ## Proved lemmas -/

theorem pay_M_sub_D (w : Fin m) : P.M w ⊆ P.Dd w :=
  run_sub_D (P.Q w) (P.S w) (mask (P.K w) P.gates) _

theorem pay_chain_pred {R : ℕ → ℕ → Prop} :
    ∀ (L : List ℕ), List.IsChain R L → ∀ x ∈ L, L.head? ≠ some x → ∃ p ∈ L, R p x
  | [], _, x, hx, _ => by simp at hx
  | [y], _, x, hx, hh => by
    simp only [List.mem_singleton] at hx
    subst hx
    simp at hh
  | y :: z :: t, hc, x, hx, hh => by
    rw [List.isChain_cons_cons] at hc
    rcases List.mem_cons.mp hx with rfl | hx
    · simp at hh
    · by_cases hxz : x = z
      · subst hxz
        exact ⟨y, by simp, hc.1⟩
      · obtain ⟨p, hp, hR⟩ := pay_chain_pred (z :: t) hc.2 x hx
          (by simp only [List.head?_cons]; exact fun h => hxz (Option.some.inj h).symm)
        exact ⟨p, List.mem_cons_of_mem _ hp, hR⟩

/-- Lemma 3: a kill along a read edge into a gate other than `N` is an AND. -/
theorem pay_lemma3 (i k : ℕ) (hk : k < P.gates.length) (hr : P.Reads i (n + k))
    (hkN : k ≠ P.kN) (y : Fin n → Bool) (h1 : val P.gates y i = true)
    (h0 : val P.gates y (n + k) = false) : (P.gates[k]'hk).op = GateOp.and := by
  obtain ⟨k', hk', he, hlt, hin⟩ := hr
  obtain rfl : k = k' := by omega
  rw [val_gate P.gates y k hk] at h0
  have hi' : val (P.gates.take k) y i = true := by
    rw [← mr_val_take P.gates y k i hlt]; exact h1
  rcases (P.hg _ (List.getElem_mem hk)).1 with h | h | h
  · exact h
  · exfalso
    rw [h] at h0
    simp only [GateOp.eval, List.any_eq_false, List.mem_map] at h0
    exact absurd hi' (by simpa using h0 _ ⟨i, hin, rfl⟩)
  · exact absurd (P.hU k P.kN hk P.hkN h P.hNop) hkN

/-- Lemma 2: a path from `g ≠ N` that is live at `e_c` (`c ∉ {a,b}`) avoids `h` and `N`. -/
theorem pay_lemma2 (c : Fin n) (hca : c ≠ P.a) (hcb : c ≠ P.b) (L : List ℕ) (g o : ℕ)
    (hL : P.IsPath L g o) (hlive : P.LiveAt (eof c) L) (hg : g ≠ n + P.kN) :
    P.hw ∉ L ∧ n + P.kN ∉ L := by
  have hhw : val P.gates (eof c) P.hw = false := by
    rw [P.hhw]; simp [eof, Ne.symm hca, Ne.symm hcb]
  have h1 : P.hw ∉ L := fun h => by
    have := hlive _ h
    rw [hhw] at this
    exact absurd this (by simp)
  refine ⟨h1, fun hN => ?_⟩
  obtain ⟨p, hp, k, hk, he, hlt, hin⟩ := pay_chain_pred L hL.1 _ hN
    (by rw [hL.2.1]; exact fun h => hg (Option.some.inj h))
  obtain rfl : k = P.kN := by omega
  rw [P.hNin p hin] at hp
  exact h1 hp

/-- A counted wire is a kept gate, where the mask agrees with the original circuit. -/
theorem pay_kept (w : Fin m) (i : ℕ) (hi : i ∈ P.Dd w) :
    (n ≤ i ∧ i < n + P.gates.length ∧ i - n ∈ P.K w) ∧
      ∀ y : Fin n → Bool, val (mask (P.K w) P.gates) y i = val P.gates y i := by
  classical
  simp only [Dd, D, Finset.mem_filter, Finset.mem_Ico, mask_length] at hi
  obtain ⟨⟨h1, h2⟩, -, u, -, -, -, -, hu, -⟩ := hi
  have hK : i - n ∈ P.K w := by
    by_contra hk
    have := val_mask_out (P.K w) P.gates (eof u) (i - n) (by omega) hk
    rw [show n + (i - n) = i by omega] at this
    rw [this] at hu
    exact absurd hu (by simp)
  exact ⟨⟨h1, h2, hK⟩, fun y =>
    val_mask (P.K w) P.gates.length y P.gates le_rfl (P.hcl w) i (Or.inr (Or.inl hK))⟩

/-- The cross argument of Theorem X: a wire counted by `w` and `v` gives `|S_w ∩ Q_v| ≥ 2`. -/
theorem pay_cross_two (w v : Fin m) (i : ℕ) (hw : i ∈ P.Dd w) (hv : i ∈ P.Dd v) :
    2 ≤ (P.S w ∩ P.Q v).card := by
  classical
  have ka := (P.pay_kept w i hw).2
  have kb := (P.pay_kept v i hv).2
  simp only [Dd, D, Finset.mem_filter] at hw hv
  obtain ⟨-, -, u, u', huv, huR, hvR, hu, hv'⟩ := hw
  obtain ⟨-, hzb, -⟩ := hv
  have hu2 : val (mask (P.K v) P.gates) (eof u) i = true := by rw [kb, ← ka]; exact hu
  have hv2 : val (mask (P.K v) P.gates) (eof u') i = true := by rw [kb, ← ka]; exact hv'
  have hub := inv_mem (P.Q v) _ (P.hgood v) i u hzb hu2
  have hvb := inv_mem (P.Q v) _ (P.hgood v) i u' hzb hv2
  have hsub : ({u, u'} : Finset (Fin n)) ⊆ P.S w ∩ P.Q v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨huR, hub⟩
    · exact Finset.mem_inter.mpr ⟨hvR, hvb⟩
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair huv] at this

theorem pay_exists_ne (c : Fin n) (X : Finset (Fin n)) (h : 2 ≤ ({c} ∪ X).card) :
    ∃ x ∈ X, x ≠ c := by
  classical
  by_contra hne
  push Not at hne
  have : {c} ∪ X ⊆ {c} := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hz
    · rw [hne z hz]; exact Finset.mem_singleton_self c
  have h2 := Finset.card_le_card this
  rw [Finset.card_singleton] at h2
  omega

theorem pay_both_of_two (X : Finset (Fin n)) (h : 2 ≤ (X ∩ {P.a, P.b}).card) :
    P.a ∈ X ∧ P.b ∈ X := by
  classical
  have hs : X ∩ {P.a, P.b} ⊆ {P.a, P.b} := Finset.inter_subset_right
  have hc : ({P.a, P.b} : Finset (Fin n)).card = 2 := Finset.card_pair P.hab
  have he := Finset.eq_of_subset_of_card_le hs (by omega)
  have ha : P.a ∈ X ∩ {P.a, P.b} := by rw [he]; simp
  have hb : P.b ∈ X ∩ {P.a, P.b} := by rw [he]; simp
  exact ⟨(Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp hb).1⟩

/-- F1: two sets counting a common wire form a crossing pair, both with enlarged frames. -/
theorem pay_F1 (w v : Fin m) (hwv : w ≠ v) (i : ℕ) (hw : i ∈ P.Dd w) (hv : i ∈ P.Dd v) :
    P.Partner w v ∧ P.Q w = P.S w ∪ {P.a, P.b} ∧ P.Q v = P.S v ∪ {P.a, P.b} := by
  classical
  have h1 := P.pay_cross_two w v i hw hv
  have h2 := P.pay_cross_two v w i hv hw
  have hI := P.hS w v hwv
  have hI' : (P.S v ∩ P.S w).card ≤ 1 := by rw [Finset.inter_comm]; exact hI
  have hQv : P.Q v = P.S v ∪ {P.a, P.b} := by
    rcases P.hQ v with h | h
    · rw [h] at h1; omega
    · exact h
  have hQw : P.Q w = P.S w ∪ {P.a, P.b} := by
    rcases P.hQ w with h | h
    · rw [h] at h2; omega
    · exact h
  refine ⟨?_, hQw, hQv⟩
  rw [hQv, Finset.inter_union_distrib_left] at h1
  rw [hQw, Finset.inter_union_distrib_left, Finset.inter_comm (P.S v) (P.S w)] at h2
  by_cases hI0 : P.S w ∩ P.S v = ∅
  · exfalso
    rw [hI0, Finset.empty_union] at h1 h2
    obtain ⟨ha, -⟩ := P.pay_both_of_two _ h1
    obtain ⟨ha', -⟩ := P.pay_both_of_two _ h2
    have : P.a ∈ P.S w ∩ P.S v := Finset.mem_inter.mpr ⟨ha, ha'⟩
    rw [hI0] at this
    simp at this
  obtain ⟨c, hc⟩ : ∃ c, P.S w ∩ P.S v = {c} := by
    apply Finset.card_eq_one.mp
    have := Finset.nonempty_iff_ne_empty.mpr hI0
    have := this.card_pos
    omega
  rw [hc] at h1 h2
  obtain ⟨x, hx, hxc⟩ := pay_exists_ne c _ h1
  obtain ⟨y, hy, hyc⟩ := pay_exists_ne c _ h2
  have both : ∀ z, z ∈ P.S w → z ∈ P.S v → z = c := by
    intro z h1 h2
    have : z ∈ P.S w ∩ P.S v := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hc] at this
    simpa using this
  rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx hy
  have hcw : c ∈ P.S w := (Finset.mem_inter.mp (hc ▸ Finset.mem_singleton_self c :
    c ∈ P.S w ∩ P.S v)).1
  have hcv : c ∈ P.S v := (Finset.mem_inter.mp (hc ▸ Finset.mem_singleton_self c :
    c ∈ P.S w ∩ P.S v)).2
  have hab := P.hab
  refine ⟨c, ?_⟩
  rcases hx.2 with rfl | rfl <;> rcases hy.2 with rfl | rfl
  · exact absurd (both _ hx.1 hy.1) hxc
  · left
    refine ⟨⟨hx.1, fun h => hyc (both _ h hy.1)⟩, ⟨hy.1, fun h => hxc (both _ hx.1 h)⟩,
      hc, ?_, ?_⟩
    · intro h; subst h; exact hxc rfl
    · intro h; subst h; exact hyc rfl
  · right
    refine ⟨⟨hy.1, fun h => hxc (both _ hx.1 h)⟩, ⟨hx.1, fun h => hyc (both _ h hy.1)⟩,
      by rw [Finset.inter_comm]; exact hc, ?_, ?_⟩
    · intro h; subst h; exact hyc rfl
    · intro h; subst h; exact hxc rfl
  · exact absurd (both _ hx.1 hy.1) hxc

theorem pay_partner_sides (w v : Fin m) (h : P.Partner w v) :
    (P.Pa w ∧ P.Pb v) ∨ (P.Pa v ∧ P.Pb w) := by
  obtain ⟨c, h | h⟩ := h
  · exact Or.inl ⟨h.1, h.2.1⟩
  · exact Or.inr ⟨h.1, h.2.1⟩

theorem pay_not_PaPb (w : Fin m) (h1 : P.Pa w) (h2 : P.Pb w) : False := h1.2 h2.1

/-- F3: two sets of the same side count disjoint wires. -/
theorem pay_F3 (w v : Fin m) (hwv : w ≠ v) (h : (P.Pa w ∧ P.Pa v) ∨ (P.Pb w ∧ P.Pb v)) :
    Disjoint (P.Dd w) (P.Dd v) := by
  rw [Finset.disjoint_left]
  intro i hw hv
  rcases P.pay_partner_sides w v (P.pay_F1 w v hwv i hw hv).1 with h' | h' <;>
    rcases h with h | h
  · exact P.pay_not_PaPb v h.2 h'.2
  · exact P.pay_not_PaPb w h'.1 h.1
  · exact P.pay_not_PaPb w h.1 h'.2
  · exact P.pay_not_PaPb v h'.1 h.2

/-- F2 (multiplicity): a wire is merged by at most two sets. -/
theorem pay_F2_two (i : ℕ) (u1 u2 u3 : Fin m) (h1 : i ∈ P.M u1) (h2 : i ∈ P.M u2)
    (h3 : i ∈ P.M u3) : u1 = u2 ∨ u1 = u3 ∨ u2 = u3 := by
  by_contra hne
  push Not at hne
  obtain ⟨h12, h13, h23⟩ := hne
  have p12 := P.pay_partner_sides _ _ (P.pay_F1 u1 u2 h12 i (P.pay_M_sub_D _ h1)
    (P.pay_M_sub_D _ h2)).1
  have p13 := P.pay_partner_sides _ _ (P.pay_F1 u1 u3 h13 i (P.pay_M_sub_D _ h1)
    (P.pay_M_sub_D _ h3)).1
  have p23 := P.pay_partner_sides _ _ (P.pay_F1 u2 u3 h23 i (P.pay_M_sub_D _ h2)
    (P.pay_M_sub_D _ h3)).1
  have n1 := P.pay_not_PaPb u1
  have n2 := P.pay_not_PaPb u2
  have n3 := P.pay_not_PaPb u3
  tauto

/-- A paying side exists under (H*). -/
theorem pay_side (hH : P.HStar) (g : ℕ) (hg : P.Coll g) :
    ∃ T c kbar, P.SideOK g T c kbar := by
  obtain ⟨w, w', hne, hw, hw'⟩ := hg
  obtain ⟨c, hc | hc⟩ := (P.pay_F1 w w' hne g (P.pay_M_sub_D _ hw) (P.pay_M_sub_D _ hw')).1
  · rcases hH g w w' c hc hw hw' with hd | hd
    · exact ⟨w, c, P.b, w, w', hc, hw, hw', Or.inl ⟨rfl, hd, rfl⟩⟩
    · exact ⟨w', c, P.a, w, w', hc, hw, hw', Or.inr ⟨rfl, hd, rfl⟩⟩
  · rcases hH g w' w c hc hw' hw with hd | hd
    · exact ⟨w', c, P.b, w', w, hc, hw', hw, Or.inl ⟨rfl, hd, rfl⟩⟩
    · exact ⟨w, c, P.a, w', w, hc, hw', hw, Or.inr ⟨rfl, hd, rfl⟩⟩

theorem pay_SQ (w : Fin m) : P.S w ⊆ P.Q w := by
  intro x hx
  rcases P.hQ w with h | h <;> rw [h]
  · exact hx
  · exact Finset.mem_union_left _ hx

/-- Each set merges at least `|S| - 1` times. -/
theorem pay_sum_M : P.base ≤ ∑ w, (P.M w).card := by
  unfold base
  apply Finset.sum_le_sum
  intro w _
  have hm : ∀ x : Fin n → Bool, val (mask (P.K w) P.gates) x (P.out w) = val P.gates x (P.out w) :=
    fun x => val_mask (P.K w) P.gates.length x P.gates le_rfl (P.hcl w) (P.out w) (P.hout w)
  have := merge_count (P.Q w) (P.S w) (mask (P.K w) P.gates) (P.hgood w) (P.out w)
    (by
      rw [hm, P.hev, decide_eq_false_iff_not]
      rintro ⟨v, hv, hv'⟩
      simp only [Zof, decide_eq_true_eq] at hv'
      exact hv' (P.pay_SQ w hv))
    (by
      intro u hu
      rw [hm, P.hev, decide_eq_true_eq]
      exact ⟨u, hu, by simp [eof]⟩)
  rw [mask_length] at this
  exact this

/-- Merge gates are OR gates. -/
theorem pay_merge_or (w : Fin m) (i : ℕ) (hi : i ∈ P.M w) : P.opAt i GateOp.or := by
  obtain ⟨⟨h1, h2, hK⟩, -⟩ := P.pay_kept w i (P.pay_M_sub_D w hi)
  obtain ⟨j, -, rfl, hm⟩ := (runM_mem _ _ _ _ i).mp hi
  obtain ⟨hj, hop, -⟩ := mg_split _ _ _ (P.hgood w) j hm
  have hj' : j < P.gates.length := by rw [mask_length] at hj; exact hj
  have hjK : j ∈ P.K w := by simpa using hK
  refine ⟨j, hj', rfl, ?_⟩
  have : (mask (P.K w) P.gates)[j]'hj = P.gates[j]'hj' := by
    simp [mask, List.getElem_mapIdx, hjK]
  rw [← this]; exact hop

theorem pay_opAt_unique (i : ℕ) (o1 o2 : GateOp) (h1 : P.opAt i o1) (h2 : P.opAt i o2) :
    o1 = o2 := by
  obtain ⟨k, hk, rfl, e1⟩ := h1
  obtain ⟨k', hk', he, e2⟩ := h2
  obtain rfl : k = k' := by omega
  rw [← e1, ← e2]

theorem pay_M_Ico (w : Fin m) (i : ℕ) (hi : i ∈ P.M w) :
    i ∈ Finset.Ico n (n + P.gates.length) := by
  have := (P.pay_kept w i (P.pay_M_sub_D w hi)).1
  simp only [Finset.mem_Ico]; omega

theorem pay_mult (i : ℕ) :
    (Finset.univ.filter fun w => i ∈ P.M w).card ≤ 1 + if i ∈ P.coll then 1 else 0 := by
  classical
  split_ifs with hc
  · by_contra hlt
    obtain ⟨u1, h1, u2, h2, u3, h3, h12, h13, h23⟩ := Finset.two_lt_card.mp
      (by omega : 2 < (Finset.univ.filter fun w => i ∈ P.M w).card)
    rcases P.pay_F2_two i u1 u2 u3 (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
      (Finset.mem_filter.mp h3).2 with h | h | h
    · exact h12 h
    · exact h13 h
    · exact h23 h
  · rw [Finset.card_le_one]
    intro u1 h1 u2 h2
    replace h1 := (Finset.mem_filter.mp h1).2
    replace h2 := (Finset.mem_filter.mp h2).2
    by_contra hne
    apply hc
    simp only [coll, Finset.mem_filter]
    exact ⟨P.pay_M_Ico u1 i h1, u1, u2, hne, h1, h2⟩

/-- Double counting: `Σ |M_w| ≤ |∪ M_w| + #collisions`. -/
theorem pay_union_coll : ∑ w, (P.M w).card ≤ P.allM.card + P.coll.card := by
  classical
  have h1 : ∀ w, (P.M w).card = ∑ i ∈ P.allM, if i ∈ P.M w then 1 else 0 := by
    intro w
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr]
    intro i hi
    simp only [allM, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨w, hi⟩
  calc ∑ w, (P.M w).card = ∑ w, ∑ i ∈ P.allM, (if i ∈ P.M w then 1 else 0) := by
        simp only [h1]
    _ = ∑ i ∈ P.allM, ∑ w, (if i ∈ P.M w then 1 else 0) := Finset.sum_comm
    _ ≤ ∑ i ∈ P.allM, (1 + if i ∈ P.coll then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← Finset.card_filter]
        exact P.pay_mult i
    _ = P.allM.card + (P.allM.filter fun i => i ∈ P.coll).card := by
        rw [Finset.sum_add_distrib, Finset.card_filter]
        simp
    _ ≤ P.allM.card + P.coll.card :=
        Nat.add_le_add_left (Finset.card_le_card fun i hi => (Finset.mem_filter.mp hi).2) _

theorem pay_ands_unch_disj : Disjoint P.ands P.unch := by
  classical
  rw [Finset.disjoint_left]
  intro i ha hu
  simp only [ands, unch, ors, Finset.mem_filter] at ha hu
  exact GateOp.noConfusion (P.pay_opAt_unique i _ _ ha.2 hu.1.2)

/-- Counting step: `N`, the ANDs, the merged ORs and the uncharged ORs are distinct gates. -/
theorem pay_count_step : 1 + P.ands.card + P.allM.card + P.unch.card ≤ P.gates.length := by
  classical
  have hNop : P.opAt (n + P.kN) GateOp.not := ⟨P.kN, P.hkN, rfl, P.hNop⟩
  have hallOr : ∀ i ∈ P.allM, P.opAt i GateOp.or := by
    intro i hi
    simp only [allM, Finset.mem_biUnion, Finset.mem_univ, true_and] at hi
    obtain ⟨w, hw⟩ := hi
    exact P.pay_merge_or w i hw
  have d1 : Disjoint P.ands P.allM := by
    rw [Finset.disjoint_left]
    intro i ha hm
    simp only [ands, Finset.mem_filter] at ha
    exact GateOp.noConfusion (P.pay_opAt_unique i _ _ ha.2 (hallOr i hm))
  have d2 : Disjoint (P.ands ∪ P.allM) P.unch := by
    rw [Finset.disjoint_union_left]
    refine ⟨P.pay_ands_unch_disj, ?_⟩
    rw [Finset.disjoint_left]
    intro i hm hu
    simp only [unch, Finset.mem_filter] at hu
    simp only [allM, Finset.mem_biUnion, Finset.mem_univ, true_and] at hm
    obtain ⟨w, hw⟩ := hm
    exact hu.2 w hw
  have hN : n + P.kN ∉ P.ands ∪ P.allM ∪ P.unch := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · simp only [ands, Finset.mem_filter] at h
        exact GateOp.noConfusion (P.pay_opAt_unique _ _ _ hNop h.2)
      · exact GateOp.noConfusion (P.pay_opAt_unique _ _ _ hNop (hallOr _ h))
    · simp only [unch, ors, Finset.mem_filter] at h
      exact GateOp.noConfusion (P.pay_opAt_unique _ _ _ hNop h.1.2)
  have hsub : insert (n + P.kN) (P.ands ∪ P.allM ∪ P.unch) ⊆
      Finset.Ico n (n + P.gates.length) := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp only [Finset.mem_Ico]; have := P.hkN; omega
    rcases Finset.mem_union.mp hi with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact (Finset.mem_filter.mp h).1
      · simp only [allM, Finset.mem_biUnion, Finset.mem_univ, true_and] at h
        obtain ⟨w, hw⟩ := h
        exact P.pay_M_Ico w i hw
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hN, Finset.card_union_of_disjoint d2,
    Finset.card_union_of_disjoint d1] at this
  simp at this
  omega

theorem pay_tracked (w : Fin m) (i : ℕ) (hi : i ∈ P.Dd w) :
    val P.gates (Zof (P.Q w)) i = false := by
  have k := (P.pay_kept w i hi).2
  simp only [Dd, D, Finset.mem_filter] at hi
  rw [← k]; exact hi.2.1

theorem pay_trace_Q (w : Fin m) (i : ℕ) (hi : i ∈ P.Dd w) (u : Fin n)
    (hu : val P.gates (eof u) i = true) : u ∈ P.Q w := by
  have k := (P.pay_kept w i hi).2
  have hz : val (mask (P.K w) P.gates) (Zof (P.Q w)) i = false := by
    simp only [Dd, D, Finset.mem_filter] at hi; exact hi.2.1
  exact inv_mem (P.Q w) _ (P.hgood w) i u hz (by rw [k]; exact hu)

theorem pay_two_trace (w : Fin m) (i : ℕ) (hi : i ∈ P.Dd w) :
    ∃ u v, u ≠ v ∧ u ∈ P.S w ∧ v ∈ P.S w ∧ val P.gates (eof u) i = true ∧
      val P.gates (eof v) i = true := by
  have k := (P.pay_kept w i hi).2
  simp only [Dd, D, Finset.mem_filter] at hi
  obtain ⟨-, -, u, v, huv, hu, hv, hut, hvt⟩ := hi
  rw [k] at hut hvt
  exact ⟨u, v, huv, hu, hv, hut, hvt⟩

theorem pay_input_kept (w : Fin m) (j : ℕ) (hj : j < P.gates.length) (hjK : j ∈ P.K w) (x : ℕ)
    (hx : x ∈ (P.gates[j]'hj).inputs) (hxl : x < n + j) (y : Fin n → Bool) :
    val (mask (P.K w) P.gates) y x = val P.gates y x := by
  apply val_mask (P.K w) P.gates.length y P.gates le_rfl (P.hcl w) x
  by_cases h : x < n
  · exact Or.inl h
  · exact Or.inr (Or.inl (P.hcl w j hj hjK x hx (by omega) (by omega)))

theorem pay_mask_get (w : Fin m) (j : ℕ) (hj : j < P.gates.length) (hjK : j ∈ P.K w)
    (hj' : j < (mask (P.K w) P.gates).length) :
    (mask (P.K w) P.gates)[j]'hj' = P.gates[j]'hj := by
  simp [mask, List.getElem_mapIdx, hjK]

theorem pay_cross_ne (w w' : Fin m) (c : Fin n) (hc : P.Cross w w' c) : w ≠ w' := by
  intro h; subst h; exact P.pay_not_PaPb w hc.1 hc.2.1

theorem pay_cross_mem (w w' : Fin m) (c : Fin n) (hc : P.Cross w w' c) :
    c ∈ P.S w ∧ c ∈ P.S w' ∧ ∀ u, u ∈ P.S w → u ∈ P.S w' → u = c := by
  have hI := hc.2.2.1
  have hcm : c ∈ P.S w ∩ P.S w' := by rw [hI]; exact Finset.mem_singleton_self c
  refine ⟨(Finset.mem_inter.mp hcm).1, (Finset.mem_inter.mp hcm).2, fun u h1 h2 => ?_⟩
  have : u ∈ P.S w ∩ P.S w' := Finset.mem_inter.mpr ⟨h1, h2⟩
  rw [hI] at this
  simpa using this

/-- F2 (trace): a collision gate of the crossing pair with point `c` has trace `{a, b, c}`. -/
theorem pay_F2_trace (w w' : Fin m) (c : Fin n) (hc : P.Cross w w' c) (i : ℕ)
    (hw : i ∈ P.M w) (hw' : i ∈ P.M w') :
    ∀ u, val P.gates (eof u) i = true ↔ (u = P.a ∨ u = P.b ∨ u = c) := by
  have hDw := P.pay_M_sub_D w hw
  have hDw' := P.pay_M_sub_D w' hw'
  obtain ⟨-, hQw, hQw'⟩ := P.pay_F1 w w' (P.pay_cross_ne w w' c hc) i hDw hDw'
  obtain ⟨hcw, hcw', inI⟩ := P.pay_cross_mem w w' c hc
  obtain ⟨⟨ha, hnb⟩, ⟨hb, hna⟩, -, hca, hcb⟩ := hc
  have sw : ∀ u ∈ P.S w, val P.gates (eof u) i = true → u = P.a ∨ u = c := by
    intro u hu hv
    have := P.pay_trace_Q w' i hDw' u hv
    rw [hQw'] at this
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact Or.inr (inI u hu h)
    · exact Or.inl h
    · rw [h] at hu; exact absurd hu hnb
  have sw' : ∀ u ∈ P.S w', val P.gates (eof u) i = true → u = P.b ∨ u = c := by
    intro u hu hv
    have := P.pay_trace_Q w i hDw u hv
    rw [hQw] at this
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact Or.inr (inI u h hu)
    · rw [h] at hu; exact absurd hu hna
    · exact Or.inl h
  have hA : val P.gates (eof P.a) i = true ∧ val P.gates (eof c) i = true := by
    obtain ⟨u1, v1, h1ne, hu1, hv1, hu1t, hv1t⟩ := P.pay_two_trace w i hDw
    rcases sw u1 hu1 hu1t with h | h <;> rcases sw v1 hv1 hv1t with h' | h'
    · exact absurd (h.trans h'.symm) h1ne
    · rw [h] at hu1t; rw [h'] at hv1t; exact ⟨hu1t, hv1t⟩
    · rw [h] at hu1t; rw [h'] at hv1t; exact ⟨hv1t, hu1t⟩
    · exact absurd (h.trans h'.symm) h1ne
  have hB : val P.gates (eof P.b) i = true := by
    obtain ⟨u1, v1, h1ne, hu1, hv1, hu1t, hv1t⟩ := P.pay_two_trace w' i hDw'
    rcases sw' u1 hu1 hu1t with h | h <;> rcases sw' v1 hv1 hv1t with h' | h'
    · exact absurd (h.trans h'.symm) h1ne
    · rw [h] at hu1t; exact hu1t
    · rw [h'] at hv1t; exact hv1t
    · exact absurd (h.trans h'.symm) h1ne
  intro u
  constructor
  · intro hu
    have q1 := P.pay_trace_Q w i hDw u hu
    have q2 := P.pay_trace_Q w' i hDw' u hu
    rw [hQw] at q1
    rw [hQw'] at q2
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at q1 q2
    rcases q1 with h | h | h
    · rcases q2 with h' | h' | h'
      · exact Or.inr (Or.inr (inI u h h'))
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h) <;> rw [h]
    · exact hA.1
    · exact hB
    · exact hA.2

/-- F2 (uniqueness): distinct collision gates have distinct crossing points; in particular a
crossing pair carries at most one collision gate (a union-find run joins `a` with `c` once). -/
theorem pay_F2_unique (w w' v v' : Fin m) (c : Fin n) (hc : P.Cross w w' c)
    (hc' : P.Cross v v' c) (i j : ℕ) (hi : i ∈ P.M w) (hi' : i ∈ P.M w') (hj : j ∈ P.M v)
    (hj' : j ∈ P.M v') : i = j := by
  classical
  -- the pair is determined by c
  have same : ∀ x y : Fin m, ∀ z : Fin n, z ∈ P.S x → z ∈ P.S y → z ≠ c → c ∈ P.S x →
      c ∈ P.S y → x = y := by
    intro x y z hzx hzy hzc hcx hcy
    by_contra hxy
    have hsub : ({z, c} : Finset (Fin n)) ⊆ P.S x ∩ P.S y := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hzx, hzy⟩
      · exact Finset.mem_inter.mpr ⟨hcx, hcy⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hzc] at this
    have := P.hS x y hxy
    omega
  obtain ⟨hcw, hcw', -⟩ := P.pay_cross_mem w w' c hc
  obtain ⟨hcv, hcv', -⟩ := P.pay_cross_mem v v' c hc'
  have hwv : w = v := same w v P.a hc.1.1 hc'.1.1 (Ne.symm hc.2.2.2.1) hcw hcv
  have hwv' : w' = v' := same w' v' P.b hc.2.1.1 hc'.2.1.1 (Ne.symm hc.2.2.2.2) hcw' hcv'
  subst hwv hwv'
  have tr := P.pay_F2_trace w w' c hc
  obtain ⟨j0, -, rfl, -⟩ := (runM_mem _ _ _ _ i).mp hi
  obtain ⟨j1, -, rfl, -⟩ := (runM_mem _ _ _ _ j).mp hj
  have key : ∀ k0 k1, n + k0 ∈ P.M w → n + k0 ∈ P.M w' → n + k1 ∈ P.M w →
      n + k1 ∈ P.M w' → k0 < k1 → False := by
    intro k0 k1 h0 h0' h1 h1' hlt
    have kk0 := (P.pay_kept w _ (P.pay_M_sub_D w h0)).2
    have kk1 := (P.pay_kept w _ (P.pay_M_sub_D w h1)).2
    have hjoin := (run_record (P.Q w) (P.S w) (mask (P.K w) P.gates) _ k0 h0).2 P.a hc.1.1 c hcw
      (by rw [kk0]; exact (tr _ h0 h0' _).mpr (Or.inl rfl))
      (by rw [kk0]; exact (tr _ h0 h0' _).mpr (Or.inr (Or.inr rfl)))
    refine run_once (P.Q w) (P.S w) (mask (P.K w) P.gates) _ k0 k1 P.a c hjoin hlt ?_ h1
    intro x hx hxt
    rw [kk1] at hxt
    rcases (tr _ h1 h1' x).mp hxt with h | h | h
    · exact Or.inl h
    · rw [h] at hx; exact absurd hx hc.1.2
    · exact Or.inr h
  rcases lt_trichotomy j0 j1 with h | h | h
  · exact (key j0 j1 hi hi' hj hj' h).elim
  · rw [h]
  · exact (key j1 j0 hj hj' hi hi' h).elim

theorem pay_split_logic (A B : Fin n → Bool) (a b c : Fin n) (Sw Sw' : Finset (Fin n))
    (ha : a ∈ Sw) (hnb : b ∉ Sw) (hb : b ∈ Sw') (hna : a ∉ Sw') (hcw : c ∈ Sw)
    (hg : ∀ u, (A u || B u) = true ↔ (u = a ∨ u = b ∨ u = c))
    (e1 : ∃ u ∈ Sw, A u = true) (e2 : ∃ u ∈ Sw, B u = true)
    (d1 : ∀ u ∈ Sw, ¬ (A u = true ∧ B u = true))
    (e1' : ∃ u ∈ Sw', A u = true) (e2' : ∃ u ∈ Sw', B u = true)
    (d1' : ∀ u ∈ Sw', ¬ (A u = true ∧ B u = true)) :
    ((∀ u, A u = true ↔ (u = a ∨ u = b)) ∧ (∀ u, B u = true ↔ u = c)) ∨
    ((∀ u, B u = true ↔ (u = a ∨ u = b)) ∧ (∀ u, A u = true ↔ u = c)) := by
  have gA : ∀ u, A u = true → u = a ∨ u = b ∨ u = c := fun u h => (hg u).mp (by simp [h])
  have gB : ∀ u, B u = true → u = a ∨ u = b ∨ u = c := fun u h => (hg u).mp (by simp [h])
  have inSw : ∀ u ∈ Sw, u = a ∨ u = b ∨ u = c → u = a ∨ u = c := by
    rintro u hu (h | h | h)
    · exact Or.inl h
    · rw [h] at hu; exact absurd hu hnb
    · exact Or.inr h
  have inSw' : ∀ u ∈ Sw', u = a ∨ u = b ∨ u = c → u = b ∨ u = c := by
    rintro u hu (h | h | h)
    · rw [h] at hu; exact absurd hu hna
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨u1, hu1, hA1⟩ := e1
  obtain ⟨v1, hv1, hB1⟩ := e2
  obtain ⟨u2, hu2, hA2⟩ := e1'
  obtain ⟨v2, hv2, hB2⟩ := e2'
  by_cases hAc : A c = true
  · have hBc : B c ≠ true := fun h => d1 c hcw ⟨hAc, h⟩
    have hBa : B a = true := by
      rcases inSw v1 hv1 (gB v1 hB1) with h | h
      · rw [h] at hB1; exact hB1
      · rw [h] at hB1; exact absurd hB1 hBc
    have hAa : A a ≠ true := fun h => d1 a ha ⟨h, hBa⟩
    have hBb : B b = true := by
      rcases inSw' v2 hv2 (gB v2 hB2) with h | h
      · rw [h] at hB2; exact hB2
      · rw [h] at hB2; exact absurd hB2 hBc
    have hAb : A b ≠ true := fun h => d1' b hb ⟨h, hBb⟩
    right
    refine ⟨fun u => ⟨fun h => ?_, ?_⟩, fun u => ⟨fun h => ?_, ?_⟩⟩
    · rcases gB u h with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · rw [h'] at h; exact absurd h hBc
    · rintro (h | h) <;> rw [h]
      · exact hBa
      · exact hBb
    · rcases gA u h with h' | h' | h'
      · rw [h'] at h; exact absurd h hAa
      · rw [h'] at h; exact absurd h hAb
      · exact h'
    · intro h; rw [h]; exact hAc
  · have hAa : A a = true := by
      rcases inSw u1 hu1 (gA u1 hA1) with h | h
      · rw [h] at hA1; exact hA1
      · rw [h] at hA1; exact absurd hA1 hAc
    have hBa : B a ≠ true := fun h => d1 a ha ⟨hAa, h⟩
    have hBc : B c = true := by
      rcases inSw v1 hv1 (gB v1 hB1) with h | h
      · rw [h] at hB1; exact absurd hB1 hBa
      · rw [h] at hB1; exact hB1
    have hAb : A b = true := by
      rcases inSw' u2 hu2 (gA u2 hA2) with h | h
      · rw [h] at hA2; exact hA2
      · rw [h] at hA2; exact absurd hA2 hAc
    have hBb : B b ≠ true := fun h => d1' b hb ⟨hAb, h⟩
    left
    refine ⟨fun u => ⟨fun h => ?_, ?_⟩, fun u => ⟨fun h => ?_, ?_⟩⟩
    · rcases gA u h with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · rw [h'] at h; exact absurd h hAc
    · rintro (h | h) <;> rw [h]
      · exact hAa
      · exact hAb
    · rcases gB u h with h' | h' | h'
      · rw [h'] at h; exact absurd h hBa
      · rw [h'] at h; exact absurd h hBb
      · exact h'
    · intro h; rw [h]; exact hBc

/-- Lemma 1 (split): a collision gate is `α ∨ β` with `tr(α) = {a, b}`, `tr(β) = {c}`, both
inputs 0 at both zero points. -/
theorem pay_lemma1 (w w' : Fin m) (c : Fin n) (hc : P.Cross w w' c) (g : ℕ)
    (hw : g ∈ P.M w) (hw' : g ∈ P.M w') :
    ∃ k, ∃ hk : k < P.gates.length, g = n + k ∧ (P.gates[k]'hk).op = GateOp.or ∧
      ∃ α β, ((P.gates[k]'hk).inputs = [α, β] ∨ (P.gates[k]'hk).inputs = [β, α]) ∧
        α < n + k ∧ β < n + k ∧
        (∀ u, val P.gates (eof u) α = true ↔ (u = P.a ∨ u = P.b)) ∧
        (∀ u, val P.gates (eof u) β = true ↔ u = c) ∧
        val P.gates (Zof (P.Q w)) α = false ∧ val P.gates (Zof (P.Q w)) β = false ∧
        val P.gates (Zof (P.Q w')) α = false ∧ val P.gates (Zof (P.Q w')) β = false := by
  have tr := P.pay_F2_trace w w' c hc g hw hw'
  have hDw := P.pay_M_sub_D w hw
  have hDw' := P.pay_M_sub_D w' hw'
  obtain ⟨hcw, -, -⟩ := P.pay_cross_mem w w' c hc
  obtain ⟨⟨h1, h2, hKw⟩, kw⟩ := P.pay_kept w g hDw
  obtain ⟨⟨-, -, hKw'⟩, -⟩ := P.pay_kept w' g hDw'
  obtain ⟨j, -, rfl, hm⟩ := (runM_mem _ _ _ _ g).mp hw
  obtain ⟨j', -, hjj, hm'⟩ := (runM_mem _ _ _ _ _).mp hw'
  obtain rfl : j = j' := by omega
  have hjl : j < P.gates.length := by omega
  have hjK : j ∈ P.K w := by simpa using hKw
  have hjK' : j ∈ P.K w' := by simpa using hKw'
  obtain ⟨hj1, hop, α, β, hin, hα, hβ, hzα, hzβ, hv, e1, e2, dist⟩ :=
    mg_split _ _ _ (P.hgood w) j hm
  obtain ⟨hj2, -, α', β', hin', -, -, hzα', hzβ', -, e1', e2', dist'⟩ :=
    mg_split _ _ _ (P.hgood w') j hm'
  rw [P.pay_mask_get w j hjl hjK hj1] at hop hin
  rw [P.pay_mask_get w' j hjl hjK' hj2, hin] at hin'
  obtain ⟨rfl, rfl⟩ : α = α' ∧ β = β' := by simpa using hin'
  have αin : α ∈ (P.gates[j]'hjl).inputs := by rw [hin]; simp
  have βin : β ∈ (P.gates[j]'hjl).inputs := by rw [hin]; simp
  have kα := P.pay_input_kept w j hjl hjK α αin hα
  have kβ := P.pay_input_kept w j hjl hjK β βin hβ
  have kα' := P.pay_input_kept w' j hjl hjK' α αin hα
  have kβ' := P.pay_input_kept w' j hjl hjK' β βin hβ
  simp only [kα, kβ] at hzα hzβ e1 e2 dist
  simp only [kα', kβ'] at hzα' hzβ' e1' e2' dist'
  simp only [kw, kα, kβ] at hv
  have hg : ∀ u, (val P.gates (eof u) α || val P.gates (eof u) β) = true ↔
      (u = P.a ∨ u = P.b ∨ u = c) := fun u => by rw [← hv]; exact tr u
  rcases pay_split_logic (fun u => val P.gates (eof u) α) (fun u => val P.gates (eof u) β)
      P.a P.b c (P.S w) (P.S w') hc.1.1 hc.1.2 hc.2.1.1 hc.2.1.2 hcw hg e1 e2
      (fun u hu h => dist u hu u hu h.1 h.2 rfl) e1' e2'
      (fun u hu h => dist' u hu u hu h.1 h.2 rfl) with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · exact ⟨j, hjl, rfl, hop, α, β, Or.inl hin, hα, hβ, hA, hB, hzα, hzβ, hzα', hzβ'⟩
  · exact ⟨j, hjl, rfl, hop, β, α, Or.inr hin, hβ, hα, hB, hA, hzβ, hzα, hzβ', hzα'⟩

end PaySetting

end PEqualNP.Outside.L_meta_951_aux
