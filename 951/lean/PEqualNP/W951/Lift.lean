import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Cases

/-!
# The lifted monotone form of a one-NOT circuit (S2 "Lift")

Replace the NOT gate (position `p`, wire `n + p`) of a circuit `gates` on `n` inputs by a fresh
input `y`, placed as input number `n`.  The result `lift n p gates` is a circuit on `n + 1` inputs
with one gate fewer and no NOT gate (`lift_ops`, `lift_length`), hence monotone (`lift_mono`).

Wires: original wire `i` is lifted wire `liftWire n p i` (inputs stay, the wires of the gates before
the NOT move up by one, the NOT wire becomes `y = n`, the wires after the NOT keep their index).
The gates before the NOT do not read `y` (`lift_pre_noY`), so the wire `h` read by the NOT is a
`y`-free wire of the lifted circuit (`val_lift_h`).

Main facts:
* `val_lift` : the original value of every wire is the lifted value at `(x, ν x)`, where
  `ν x = val gates x (n + p)` is the value of the NOT gate; `val_not` : `ν x = ! h x`.
* `lift_exact` (exactness lemma): for every wire, with `F y` its lifted value at `(x, y)` and `r` its
  original value at `x`: `F 0 ≤ r ≤ F 1`, `F 0 = r` when `h x = 1`, `F 1 = r` when `h x = 0`.
* `lift_interval` : for outputs computing `o_w = OR(S_w)`, `F_w(x, y)` lies in the interval
  `[o_w ∧ (y ∨ h), o_w ∨ (y ∧ h)]` for every `x` and `y`.
* `val_gate_congr` : two circuits that differ only in one gate computing the same value agree on
  every wire (they have the same lift).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Inputs `(x, y)`: `y` is input number `n` -/

/-- The input vector `(x, y)` on `n + 1` inputs: inputs `0, ..., n - 1` are `x`, input `n` is `y`. -/
def ext {n : ℕ} (x : Fin n → Bool) (y : Bool) : Fin (n + 1) → Bool :=
  fun i => if h : (i : ℕ) < n then x ⟨i, h⟩ else y

theorem val_input {n : ℕ} (gs : List Gate) (z : Fin n → Bool) (j : ℕ) (hj : j < n) :
    val gs z j = z ⟨j, hj⟩ := by
  have h := val_append [] gs z j (by simpa using hj)
  rw [List.nil_append] at h
  rw [h, val_nil]
  simp [hj]

theorem val_ext_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (y : Bool) (j : ℕ) (hj : j < n) :
    val gs (ext x y) j = x ⟨j, hj⟩ := by
  rw [val_input gs (ext x y) j (by omega)]
  simp [ext, hj]

theorem val_ext_y {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (y : Bool) :
    val gs (ext x y) n = y := by
  rw [val_input gs (ext x y) n (by omega)]
  simp [ext]

theorem ext_le {n : ℕ} (x : Fin n → Bool) :
    ∀ c, ext x false c = true → ext x true c = true := by
  intro c hc
  by_cases h : (c : ℕ) < n
  · simpa [ext, h] using hc
  · simp [ext, h]

/-! ## The gates before the NOT: insert `y` as wire `n` -/

/-- Wire map of the gates before the NOT: inputs stay, every other wire moves up by one. -/
def sh (n j : ℕ) : ℕ := if j < n then j else j + 1

/-- A gate before the NOT, lifted. -/
def shGate (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh n)⟩

theorem sh_ne (n j : ℕ) : sh n j ≠ n := by
  unfold sh; split_ifs <;> omega

theorem val_shift {n : ℕ} (pre : List Gate) (x : Fin n → Bool) (y : Bool) :
    ∀ i, val (pre.map (shGate n)) (ext x y) (sh n i) = val pre x i := by
  induction pre using List.reverseRecOn with
  | nil =>
    intro i
    rw [List.map_nil, val_nil, val_nil]
    by_cases hi : i < n
    · simp [sh, hi, ext, show i < n + 1 by omega]
    · simp [sh, hi]
  | append_singleton pre g ih =>
    intro i
    rw [List.map_append, List.map_singleton, val_snoc, val_snoc, List.length_map]
    have hiff : sh n i = n + 1 + pre.length ↔ i = n + pre.length := by
      unfold sh; split_ifs <;> omega
    by_cases hi : i = n + pre.length
    · rw [ite_eq_left (hiff.mpr hi), ite_eq_left hi]
      simp only [shGate, List.map_map]
      congr 2
      funext j
      exact ih j
    · rw [ite_eq_right (fun h => hi (hiff.mp h)), ite_eq_right hi]
      exact ih i

/-! ## The gates after the NOT -/

/-- Wire map of the original gate at position `q > p` (after the NOT at position `p`): an existing
wire goes to its lifted copy (the NOT wire `n + p` goes to `y = n`); a wire that does not exist yet
at position `q` goes to a wire that does not exist yet at the lifted position. -/
def rd (n p q j : ℕ) : ℕ :=
  if j < n then j else if j < n + p then j + 1 else if j = n + p then n
  else if j < n + q then j else j + 1

/-- The lifted wire of original wire `i`. -/
def liftWire (n p i : ℕ) : ℕ :=
  if i < n then i else if i < n + p then i + 1 else if i = n + p then n else i

/-- The gates after the NOT, lifted (`post` starts at original position `p + 1`). -/
def liftPost (n p : ℕ) (post : List Gate) : List Gate :=
  post.mapIdx fun k g => ⟨g.op, g.inputs.map (rd n p (p + 1 + k))⟩

/-- **The lift**: the NOT gate at position `p` replaced by the new input `y` (input number `n`). -/
def lift (n p : ℕ) (gates : List Gate) : List Gate :=
  (gates.take p).map (shGate n) ++ liftPost n p (gates.drop (p + 1))

theorem length_liftPost (n p : ℕ) (post : List Gate) : (liftPost n p post).length = post.length :=
  List.length_mapIdx

theorem rd_eq (n p q j : ℕ) (hj : j < n + q) : rd n p q j = liftWire n p j := by
  unfold rd liftWire; split_ifs <;> omega

theorem liftWire_lt_sh (n p j : ℕ) (hj : j < n + p) : liftWire n p j = sh n j := by
  unfold liftWire sh; split_ifs <;> omega

/-- The original circuit, split at the NOT, against its lift (any gate `N` at position `p`). -/
theorem val_lift_split {n : ℕ} (pre : List Gate) (N : Gate) (post : List Gate)
    (x : Fin n → Bool) :
    ∀ i, val (pre ++ N :: post) x i =
      val (pre.map (shGate n) ++ liftPost n pre.length post)
        (ext x (val (pre ++ [N]) x (n + pre.length))) (liftWire n pre.length i) := by
  induction post using List.reverseRecOn with
  | nil =>
    intro i
    simp only [liftPost, List.mapIdx_nil, List.append_nil]
    by_cases hi : i = n + pre.length
    · subst hi
      rw [liftWire, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, val_ext_y]
    · rw [val_snoc, ite_eq_right hi]
      rcases Nat.lt_or_gt_of_ne hi with h | h
      · rw [liftWire_lt_sh n pre.length i h, val_shift]
      · rw [val_ge pre x i (by omega), liftWire, ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), val_ge _ _ _ (by simp; omega)]
  | append_singleton post g ih =>
    intro i
    have e1 : pre ++ N :: (post ++ [g]) = (pre ++ N :: post) ++ [g] := by simp
    have e2 : pre.map (shGate n) ++ liftPost n pre.length (post ++ [g]) =
        (pre.map (shGate n) ++ liftPost n pre.length post) ++
          [⟨g.op, g.inputs.map (rd n pre.length (pre.length + 1 + post.length))⟩] := by
      simp [liftPost, List.mapIdx_append, List.append_assoc]
    rw [e1, e2, val_snoc, val_snoc]
    simp only [List.length_append, List.length_cons, List.length_map, length_liftPost]
    have hiff : liftWire n pre.length i = n + 1 + (pre.length + post.length) ↔
        i = n + (pre.length + (post.length + 1)) := by
      unfold liftWire; split_ifs <;> omega
    by_cases hi : i = n + (pre.length + (post.length + 1))
    · rw [ite_eq_left (hiff.mpr hi), ite_eq_left hi]
      simp only [List.map_map]
      congr 2
      funext j
      simp only [Function.comp]
      by_cases hj : j < n + (pre.length + 1 + post.length)
      · rw [rd_eq _ _ _ _ hj]
        exact ih j
      · have hrd : rd n pre.length (pre.length + 1 + post.length) j = j + 1 := by
          unfold rd; split_ifs <;> omega
        rw [hrd, val_ge _ _ _ (by simp; omega), val_ge _ _ _ (by simp [length_liftPost]; omega)]
    · rw [ite_eq_right (fun h => hi (hiff.mp h)), ite_eq_right hi]
      exact ih i

theorem split_at {gates : List Gate} {p : ℕ} (hp : p < gates.length) :
    gates.take p ++ gates[p] :: gates.drop (p + 1) = gates := by
  rw [List.getElem_cons_drop, List.take_append_drop]

theorem length_take_of_lt {gates : List Gate} {p : ℕ} (hp : p < gates.length) :
    (gates.take p).length = p := by
  simp; omega

/-- **The lift theorem**: the original value of every wire is the lifted value at `(x, ν x)`,
`ν x` = the value of the NOT gate. -/
theorem val_lift {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (x : Fin n → Bool) (i : ℕ) :
    val gates x i = val (lift n p gates) (ext x (val gates x (n + p))) (liftWire n p i) := by
  have hs := split_at hp
  have hl := length_take_of_lt hp
  have key := val_lift_split (gates.take p) gates[p] (gates.drop (p + 1)) x i
  rw [hs, hl] at key
  have hb : val (gates.take p ++ [gates[p]]) x (n + p) = val gates x (n + p) := by
    conv_rhs => rw [← hs]
    rw [show gates.take p ++ gates[p] :: gates.drop (p + 1) =
      (gates.take p ++ [gates[p]]) ++ gates.drop (p + 1) by simp]
    rw [val_append (gates.take p ++ [gates[p]]) (gates.drop (p + 1)) x (n + p) (by simp; omega)]
  rw [hb] at key
  exact key

theorem length_lift (n p : ℕ) (gates : List Gate) (hp : p < gates.length) :
    (lift n p gates).length = gates.length - 1 := by
  simp [lift, length_liftPost]
  omega

/-- The gates before the NOT do not read `y`. -/
theorem lift_pre_noY (n : ℕ) (pre : List Gate) : ∀ g ∈ pre.map (shGate n), n ∉ g.inputs := by
  intro g hg hn
  obtain ⟨g0, -, rfl⟩ := List.mem_map.mp hg
  obtain ⟨j, -, hj⟩ := List.mem_map.mp hn
  exact sh_ne n j hj

/-! ## The NOT gate and the wire `h` it reads -/

/-- The wire read by the gate at position `p` (`n + p`, which reads `false`, if it reads nothing). -/
def notIn (n p : ℕ) (gates : List Gate) : ℕ :=
  (gates.getD p ⟨GateOp.not, []⟩).inputs.headD (n + p)

/-- The NOT gate computes `! h x`, `h x` = the value of the wire it reads, before it. -/
theorem val_not {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hN : (gates[p]'hp).op = GateOp.not) (x : Fin n → Bool) :
    val gates x (n + p) = !(val (gates.take p) x (notIn n p gates)) := by
  rw [val_gate gates x p hp, hN]
  have hd : gates.getD p ⟨GateOp.not, []⟩ = gates[p] := by
    simp [List.getD_eq_getElem?_getD, hp]
  unfold notIn
  rw [hd]
  cases hin : (gates[p]'hp).inputs with
  | nil =>
    simp only [GateOp.eval, List.map_nil, List.headD_nil, List.headD_nil]
    rw [val_ge _ _ _ (by simp)]
  | cons j r => simp [GateOp.eval]

/-- `h` is a `y`-free wire of the lifted circuit (when the NOT reads an existing wire). -/
theorem val_lift_h {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (x : Fin n → Bool) (y : Bool) (j : ℕ) (hj : j < n + p) :
    val (lift n p gates) (ext x y) (sh n j) = val (gates.take p) x j := by
  unfold lift
  rw [val_append _ _ _ _ (by simp; unfold sh; split_ifs <;> omega), val_shift]

/-! ## The lift has no NOT and is monotone -/

theorem lift_ops {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) :
    ∀ g ∈ lift n p gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  have key : ∀ k (hk : k < gates.length), k ≠ p →
      ((gates[k]'hk).op = GateOp.and ∨ (gates[k]'hk).op = GateOp.or) ∧
        (gates[k]'hk).inputs.length ≤ 2 := by
    intro k hk hkp
    obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hk)
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (hU k p hk hp h hN) hkp
  intro g hgm
  rcases List.mem_append.mp hgm with h | h
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg0
    rw [List.getElem_take]
    have := key k (by simp at hk; omega) (by simp at hk; omega)
    simpa [shGate] using this
  · obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp h
    rw [List.getElem_drop]
    have := key (p + 1 + k) (by simp at hk; omega) (by omega)
    simpa using this

/-- The lifted circuit is monotone in its whole input `(x, y)`. -/
theorem lift_mono {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
    (z z' : Fin (n + 1) → Bool) (hz : ∀ c, z c = true → z' c = true) :
    ∀ i, val (lift n p gates) z i = true → val (lift n p gates) z' i = true :=
  mono_val _ (fun g hm => (lift_ops (n := n) gates p hp hg hU hN g hm).1) z z' hz

/-! ## The exactness lemma -/

/-- **Exactness lemma.** For every wire `i`, with `F y` its lifted value at `(x, y)`, `r` its
original value at `x` and `h` the wire read by the NOT:
`F 0 ≤ r`, `r ≤ F 1`, `F 0 = r` when `h x = 1`, `F 1 = r` when `h x = 0`. -/
theorem lift_exact {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (x : Fin n → Bool) (i : ℕ) :
    (val (lift n p gates) (ext x false) (liftWire n p i) = true → val gates x i = true) ∧
    (val gates x i = true → val (lift n p gates) (ext x true) (liftWire n p i) = true) ∧
    (val (gates.take p) x (notIn n p gates) = true →
      val (lift n p gates) (ext x false) (liftWire n p i) = val gates x i) ∧
    (val (gates.take p) x (notIn n p gates) = false →
      val (lift n p gates) (ext x true) (liftWire n p i) = val gates x i) := by
  have hl := val_lift (n := n) gates p hp x i
  have hν := val_not (n := n) gates p hp hN x
  have hm := lift_mono (n := n) gates p hp hg hU hN (ext x false) (ext x true) (ext_le x)
    (liftWire n p i)
  cases hh : val (gates.take p) x (notIn n p gates) with
  | true =>
    rw [hh] at hν
    rw [hν] at hl
    simp only [Bool.not_true] at hl
    refine ⟨fun h => hl ▸ h, fun h => hm (hl ▸ h), fun _ => hl.symm, fun h => absurd h (by simp)⟩
  | false =>
    rw [hh] at hν
    rw [hν] at hl
    simp only [Bool.not_false] at hl
    refine ⟨fun h => hl ▸ hm h, fun h => hl ▸ h, fun h => absurd h (by simp), fun _ => hl.symm⟩

/-- The interval `[o ∧ (y ∨ h), o ∨ (y ∧ h)]` (as two implications). -/
def InInterval (o y h F : Bool) : Prop :=
  ((o && (y || h)) = true → F = true) ∧ (F = true → (o || (y && h)) = true)

/-- At `y = ! h` the interval is the single value `o`. -/
theorem inInterval_not (o h F : Bool) (H : InInterval o (!h) h F) : F = o := by
  obtain ⟨h1, h2⟩ := H
  cases o <;> cases h <;> cases F <;> simp_all

/-- **Interval form of the exactness lemma**: every lifted wire lies in the interval of its
original value, for every `x` and `y` (`h` = the wire read by the NOT). -/
theorem lift_interval_wire {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (x : Fin n → Bool)
    (y : Bool) (i : ℕ) :
    InInterval (val gates x i) y (val (gates.take p) x (notIn n p gates))
      (val (lift n p gates) (ext x y) (liftWire n p i)) := by
  obtain ⟨e1, e2, e3, e4⟩ := lift_exact (n := n) gates p hp hg hU hN x i
  have hm := lift_mono (n := n) gates p hp hg hU hN (ext x false) (ext x true) (ext_le x)
    (liftWire n p i)
  constructor
  · intro ho
    cases y with
    | true => exact e2 (by simpa using ho)
    | false =>
      simp only [Bool.false_or, Bool.and_eq_true] at ho
      rw [e3 ho.2]; exact ho.1
  · intro hF
    cases y with
    | false => simp [e1 hF]
    | true =>
      cases hh : val (gates.take p) x (notIn n p gates) with
      | true => simp
      | false => rw [e4 hh] at hF; simp [hF]

/-- **Interval form for the outputs**: if output `w` computes `OR(S w)` then its lifted function
`F_w(x, y)` lies in `[o_w ∧ (y ∨ h), o_w ∨ (y ∧ h)]` for all `x, y`. -/
theorem lift_interval {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (w : Fin m) (x : Fin n → Bool) (y : Bool) :
    InInterval (decide (∃ v ∈ S w, x v = true)) y (val (gates.take p) x (notIn n p gates))
      (val (lift n p gates) (ext x y) (liftWire n p (out w))) := by
  rw [← hev w x]
  exact lift_interval_wire gates p hp hg hU hN x y (out w)

/-! ## Replacing one gate by a gate with the same value -/

/-- Two circuits that differ in one gate only, the two versions computing the same value on `x`,
agree on every wire at `x` (they have the same lift). -/
theorem val_gate_congr {n : ℕ} (pre : List Gate) (N N' : Gate) (post : List Gate)
    (x : Fin n → Bool)
    (hN : val (pre ++ [N]) x (n + pre.length) = val (pre ++ [N']) x (n + pre.length)) (i : ℕ) :
    val (pre ++ N :: post) x i = val (pre ++ N' :: post) x i := by
  rw [val_lift_split pre N post x i, val_lift_split pre N' post x i, hN]

end PEqualNP.Outside.L_meta_951_aux
