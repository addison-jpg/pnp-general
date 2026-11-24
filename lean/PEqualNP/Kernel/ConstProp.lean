import PEqualNP.Kernel.Circuit

/-!
# Kernel.ConstProp: constant propagation on `Dag`

One pass over the gates of a `Dag n s`. Every old wire gets a status: a constant, or a wire of
the new circuit. A gate whose value is a constant or a copy of an earlier wire is not emitted,
and the gates that read it are rewired. Statuses are well scoped by type (`Stat M` names a wire
below `M`), so there is no validity predicate to carry.

* `Dag.cpRun D j h` is the state after the first `j` gates: the gates emitted so far and the
  status of each of the first `n + j` old wires. `Dag.cpRun_sound` relates wire values.
* `Dag.constProp D` is the new circuit. If the output wire is a constant, it is the circuit
  with one constant gate. `Dag.eval_constProp` is soundness, `Dag.size_constProp_le` is the cost.
* `Dag.size_constProp_restrict_le`: after `Dag.restrict`, if some gate of `D` reads the fixed
  input, the result has at most `max 1 (D.size - 1)` gates.

The pass does not remove gates that the output does not depend on.
-/

namespace PEqualNP.Kernel

variable {n s : ℕ}

/-! ### Values of a gate family

`Dag.val` needs a `Dag`, and a `Dag` needs an output wire, which a circuit under construction
with no wire yet cannot have. `gval` is the same recursion on the gates alone. -/

/-- `m` gates on `n` inputs, without an output wire. -/
abbrev Gates (n m : ℕ) := (i : Fin m) → DGate (n + i)

/-- The value of wire `k`; the recursion of `Dag.val`. -/
def gval {m : ℕ} (G : Gates n m) (x : Fin n → Bool) (k : ℕ) : Bool :=
  if h : k < n then x ⟨k, h⟩ else
  if h2 : k - n < m then
    (G ⟨k - n, h2⟩).eval fun a => gval G x a.val
  else false
termination_by k
decreasing_by
  have h3 : (⟨k - n, h2⟩ : Fin m).val = k - n := rfl
  have := a.isLt
  omega

theorem Dag.val_eq_gval (D : Dag n s) (x : Fin n → Bool) (k : ℕ) :
    D.val x k = gval D.gate x k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [Dag.val.eq_1, gval.eq_1]
    split_ifs with h h2
    · rfl
    · congr 1
      funext a
      have h3 : (⟨k - n, h2⟩ : Fin s).val = k - n := rfl
      have := a.isLt
      exact ih a.val (by omega)
    · rfl

theorem gval_lt {m : ℕ} (G : Gates n m) (x : Fin n → Bool) (k : ℕ) (h : k < n) :
    gval G x k = x ⟨k, h⟩ := by
  rw [gval.eq_1, dite_eq_left_of_eq_true (eq_true h)]

/-- Wire `k` is gate `j` when `k = n + j`. -/
theorem gval_gate {m : ℕ} (G : Gates n m) (x : Fin n → Bool) (k j : ℕ) (hj : j < m)
    (hk : k = n + j) :
    gval G x k = (G ⟨j, hj⟩).eval fun a => gval G x a.val := by
  subst hk
  have hk : ¬ (n + j < n) := by omega
  have hs : n + j - n < m := by omega
  have cong : ∀ i i' : Fin m, i.val = i'.val →
      (G i).eval (fun a => gval G x a.val) = (G i').eval (fun a => gval G x a.val) := by
    intro i i' h
    have := Fin.ext h
    subst this
    rfl
  rw [gval.eq_1, dite_eq_right_of_eq_false (eq_false hk), dite_eq_left_of_eq_true (eq_true hs)]
  exact cong _ _ (by simp)

/-- Add a gate at the end. -/
def Gates.snoc {m : ℕ} (G : Gates n m) (g : DGate (n + m)) : Gates n (m + 1) :=
  Fin.lastCases (motive := fun i : Fin (m + 1) => DGate (n + i)) g G

/-- A new last gate does not change the earlier wires. -/
theorem gval_snoc_lt {m : ℕ} (G : Gates n m) (g : DGate (n + m)) (x : Fin n → Bool) :
    ∀ k, k < n + m → gval (G.snoc g) x k = gval G x k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkm
    by_cases hk : k < n
    · rw [gval_lt _ _ _ hk, gval_lt _ _ _ hk]
    · have hj : k - n < m := by omega
      rw [gval_gate (G.snoc g) x k (k - n) (by omega) (by omega),
        gval_gate G x k (k - n) hj (by omega)]
      have hg : G.snoc g ⟨k - n, by omega⟩ = G ⟨k - n, hj⟩ :=
        Fin.lastCases_castSucc (motive := fun i : Fin (m + 1) => DGate (n + i)) ⟨k - n, hj⟩
      rw [hg]
      congr 1
      funext a
      have h3 : (⟨k - n, hj⟩ : Fin m).val = k - n := rfl
      have := a.isLt
      exact ih a.val (by omega) (by omega)

/-- The new last wire is the new gate, read off the old wires. -/
theorem gval_snoc_last {m : ℕ} (G : Gates n m) (g : DGate (n + m)) (x : Fin n → Bool) :
    gval (G.snoc g) x (n + m) = g.eval fun a => gval G x a.val := by
  rw [gval_gate (G.snoc g) x (n + m) m (by omega) rfl]
  have hg : G.snoc g ⟨m, by omega⟩ = g :=
    Fin.lastCases_last (motive := fun i : Fin (m + 1) => DGate (n + i))
  rw [hg]
  congr 1
  funext a
  exact gval_snoc_lt G g x a.val a.isLt

/-! ### Statuses and the simplification of one gate -/

/-- The status of an old wire: a constant, or a wire of the new circuit, numbered below `M`. -/
inductive Stat (M : ℕ) where
  | const (c : Bool)
  | wire (i : Fin M)

/-- The value of a status, given the values `v` of the new wires. -/
def Stat.val {M : ℕ} (v : ℕ → Bool) : Stat M → Bool
  | .const c => c
  | .wire i => v i.val

/-- The same status after one more new wire. -/
def Stat.lift {M : ℕ} : Stat M → Stat (M + 1)
  | .const c => .const c
  | .wire i => .wire i.castSucc

/-- What a gate becomes: a gate to emit, or a status with nothing emitted. -/
inductive Res (M : ℕ) where
  | emit (g : DGate M)
  | stat (r : Stat M)

def Res.eval {M : ℕ} (v : ℕ → Bool) : Res M → Bool
  | .emit g => g.eval fun a => v a.val
  | .stat r => r.val v

/-- Simplify a gate given the statuses of the wires it may read. A gate is emitted only when
every wire it reads has a `wire` status. -/
def simpGate {N M : ℕ} (st : Fin N → Stat M) : DGate N → Res M
  | .and a b =>
    match st a, st b with
    | .const c, .const d => .stat (.const (c && d))
    | .const c, .wire j => .stat (if c then .wire j else .const false)
    | .wire i, .const d => .stat (if d then .wire i else .const false)
    | .wire i, .wire j => .emit (.and i j)
  | .or a b =>
    match st a, st b with
    | .const c, .const d => .stat (.const (c || d))
    | .const c, .wire j => .stat (if c then .const true else .wire j)
    | .wire i, .const d => .stat (if d then .const true else .wire i)
    | .wire i, .wire j => .emit (.or i j)
  | .not a =>
    match st a with
    | .const c => .stat (.const (!c))
    | .wire i => .emit (.not i)
  | .const c => .stat (.const c)

/-- Simplification keeps the value of the gate. -/
theorem simpGate_eval {N M : ℕ} (st : Fin N → Stat M) (g : DGate N) (v : ℕ → Bool) :
    (simpGate st g).eval v = g.eval fun a => (st a).val v := by
  cases g with
  | and a b =>
    simp only [simpGate, DGate.eval]
    cases st a <;> cases st b <;> simp [Res.eval, Stat.val, DGate.eval] <;>
      split_ifs <;> simp_all
  | or a b =>
    simp only [simpGate, DGate.eval]
    cases st a <;> cases st b <;> simp [Res.eval, Stat.val, DGate.eval] <;>
      split_ifs <;> simp_all
  | not a =>
    simp only [simpGate, DGate.eval]
    cases st a <;> simp [Res.eval, Stat.val, DGate.eval]
  | const c => rfl

/-- The gate reads wire `k` directly. -/
def DGate.Reads {m : ℕ} : DGate m → ℕ → Prop
  | .and a b, k => a.val = k ∨ b.val = k
  | .or a b, k => a.val = k ∨ b.val = k
  | .not a, k => a.val = k
  | .const _, _ => False

theorem DGate.reads_cast {m m' : ℕ} (h : m = m') (g : DGate m) (k : ℕ) :
    (g.cast h).Reads k ↔ g.Reads k := by
  cases g <;> simp [DGate.cast, DGate.Reads]

/-- A gate that reads a wire with a constant status is not emitted. -/
theorem simpGate_of_reads_const {N M : ℕ} (st : Fin N → Stat M) (g : DGate N) (k : ℕ)
    (hr : g.Reads k) (hc : ∀ a : Fin N, a.val = k → ∃ c, st a = .const c) :
    ∃ r, simpGate st g = .stat r := by
  cases g with
  | and a b =>
    rcases hr with h | h
    · obtain ⟨c, hc⟩ := hc a h
      simp only [simpGate, hc]
      cases st b <;> exact ⟨_, rfl⟩
    · obtain ⟨c, hc⟩ := hc b h
      simp only [simpGate, hc]
      cases st a <;> exact ⟨_, rfl⟩
  | or a b =>
    rcases hr with h | h
    · obtain ⟨c, hc⟩ := hc a h
      simp only [simpGate, hc]
      cases st b <;> exact ⟨_, rfl⟩
    · obtain ⟨c, hc⟩ := hc b h
      simp only [simpGate, hc]
      cases st a <;> exact ⟨_, rfl⟩
  | not a =>
    obtain ⟨c, hc⟩ := hc a hr
    simp only [simpGate, hc]
    exact ⟨_, rfl⟩
  | const c => exact hr.elim

/-! ### The pass -/

/-- The state after `j` old gates: `m` new gates, and a status for each of the `n + j` old
wires seen so far. -/
structure CPState (n j : ℕ) where
  m : ℕ
  gate : Gates n m
  stat : Fin (n + j) → Stat (n + m)

/-- Record the result for the next old gate. -/
def CPState.push {j : ℕ} (S : CPState n j) : Res (n + S.m) → CPState n (j + 1)
  | .emit g =>
    { m := S.m + 1
      gate := S.gate.snoc g
      stat := Fin.lastCases (motive := fun _ : Fin (n + j + 1) => Stat (n + S.m + 1))
        (.wire (Fin.last (n + S.m))) fun k => (S.stat k).lift }
  | .stat r =>
    { m := S.m
      gate := S.gate
      stat := Fin.lastCases (motive := fun _ : Fin (n + j + 1) => Stat (n + S.m)) r S.stat }

/-- The state after the first `j` gates of `D`. -/
def Dag.cpRun (D : Dag n s) : (j : ℕ) → j ≤ s → CPState n j
  | 0, _ => { m := 0, gate := fun i => i.elim0, stat := fun k => .wire k }
  | j + 1, h =>
    (D.cpRun j (by omega)).push (simpGate (D.cpRun j (by omega)).stat (D.gate ⟨j, h⟩))

theorem Dag.cpRun_succ (D : Dag n s) (j : ℕ) (h : j + 1 ≤ s) :
    D.cpRun (j + 1) h
      = (D.cpRun j (by omega)).push (simpGate (D.cpRun j (by omega)).stat (D.gate ⟨j, h⟩)) :=
  rfl

/-- One step: old statuses keep their values, and the new status has the value of the result. -/
theorem CPState.push_sound {j : ℕ} (S : CPState n j) (r : Res (n + S.m)) (x : Fin n → Bool) :
    (∀ k : Fin (n + j), ((S.push r).stat k.castSucc).val (gval (S.push r).gate x)
        = (S.stat k).val (gval S.gate x)) ∧
    ((S.push r).stat (Fin.last (n + j))).val (gval (S.push r).gate x)
        = r.eval (gval S.gate x) := by
  cases r with
  | emit g =>
    constructor
    · intro k
      have e : (S.push (.emit g)).stat k.castSucc = (S.stat k).lift :=
        Fin.lastCases_castSucc (motive := fun _ : Fin (n + j + 1) => Stat (n + S.m + 1)) k
      rw [e]
      cases S.stat k with
      | const c => rfl
      | wire i => exact gval_snoc_lt S.gate g x i.val i.isLt
    · have e : (S.push (.emit g)).stat (Fin.last (n + j)) = .wire (Fin.last (n + S.m)) :=
        Fin.lastCases_last (motive := fun _ : Fin (n + j + 1) => Stat (n + S.m + 1))
      rw [e]
      exact gval_snoc_last S.gate g x
  | stat r =>
    constructor
    · intro k
      have e : (S.push (.stat r)).stat k.castSucc = S.stat k :=
        Fin.lastCases_castSucc (motive := fun _ : Fin (n + j + 1) => Stat (n + S.m)) k
      rw [e]
      rfl
    · have e : (S.push (.stat r)).stat (Fin.last (n + j)) = r :=
        Fin.lastCases_last (motive := fun _ : Fin (n + j + 1) => Stat (n + S.m))
      rw [e]
      rfl

/-- **Wire relation.** After `j` gates, the status of every old wire `k < n + j`, read in the
new gates, has the value of wire `k` of `D`. -/
theorem Dag.cpRun_sound (D : Dag n s) (x : Fin n → Bool) :
    ∀ (j : ℕ) (h : j ≤ s) (k : Fin (n + j)),
      ((D.cpRun j h).stat k).val (gval (D.cpRun j h).gate x) = D.val x k.val := by
  intro j
  induction j with
  | zero =>
    intro h k
    have hk : k.val < n := k.isLt
    rw [Dag.val_eq_gval, gval_lt _ _ _ hk]
    exact gval_lt _ _ _ hk
  | succ j ih =>
    intro h k
    have hs := (D.cpRun j (by omega)).push_sound
      (simpGate (D.cpRun j (by omega)).stat (D.gate ⟨j, h⟩)) x
    induction k using Fin.lastCases with
    | cast k => exact (hs.1 k).trans (ih (by omega) k)
    | last =>
      refine hs.2.trans ?_
      rw [simpGate_eval]
      have e : D.val x (Fin.last (n + j)).val
          = (D.gate ⟨j, h⟩).eval fun a => gval D.gate x a.val := by
        rw [Dag.val_eq_gval]
        exact gval_gate D.gate x _ j h rfl
      refine Eq.trans ?_ e.symm
      congr 1
      funext a
      rw [ih (by omega) a, Dag.val_eq_gval]

/-! ### Counting -/

theorem CPState.push_m_le {j : ℕ} (S : CPState n j) (r : Res (n + S.m)) :
    (S.push r).m ≤ S.m + 1 := by
  cases r
  · exact le_rfl
  · exact Nat.le_succ _

theorem CPState.push_m_stat {j : ℕ} (S : CPState n j) (r : Stat (n + S.m)) :
    (S.push (.stat r)).m = S.m := rfl

/-- A constant status stays. -/
theorem CPState.push_const {j : ℕ} (S : CPState n j) (r : Res (n + S.m)) (k : Fin (n + j))
    (c : Bool) (hc : S.stat k = .const c) : (S.push r).stat k.castSucc = .const c := by
  cases r with
  | emit g =>
    have e : (S.push (.emit g)).stat k.castSucc = (S.stat k).lift :=
      Fin.lastCases_castSucc (motive := fun _ : Fin (n + j + 1) => Stat (n + S.m + 1)) k
    rw [e, hc]
    rfl
  | stat r =>
    have e : (S.push (.stat r)).stat k.castSucc = S.stat k :=
      Fin.lastCases_castSucc (motive := fun _ : Fin (n + j + 1) => Stat (n + S.m)) k
    exact e.trans hc

/-- At most one new gate per old gate, and strictly fewer once some status is a constant. -/
theorem CPState.push_count {j : ℕ} (S : CPState n j) (r : Res (n + S.m))
    (h1 : S.m ≤ j) (h2 : ∀ k c, S.stat k = .const c → S.m < j) :
    (S.push r).m ≤ j + 1 ∧ ∀ k c, (S.push r).stat k = .const c → (S.push r).m < j + 1 := by
  cases r with
  | emit g =>
    refine ⟨Nat.succ_le_succ h1, fun k c => ?_⟩
    induction k using Fin.lastCases with
    | cast k =>
      have e : (S.push (.emit g)).stat k.castSucc = (S.stat k).lift :=
        Fin.lastCases_castSucc (motive := fun _ : Fin (n + j + 1) => Stat (n + S.m + 1)) k
      rw [e]
      intro hc
      cases hk : S.stat k with
      | const d => exact Nat.succ_lt_succ (h2 k d hk)
      | wire i => rw [hk] at hc; cases hc
    | last =>
      have e : (S.push (.emit g)).stat (Fin.last (n + j)) = .wire (Fin.last (n + S.m)) :=
        Fin.lastCases_last (motive := fun _ : Fin (n + j + 1) => Stat (n + S.m + 1))
      intro hc
      cases e.symm.trans hc
  | stat r =>
    exact ⟨Nat.le_succ_of_le h1, fun _ _ _ => Nat.lt_succ_of_le h1⟩

theorem Dag.cpRun_count (D : Dag n s) :
    ∀ (j : ℕ) (h : j ≤ s), (D.cpRun j h).m ≤ j ∧
      ∀ k c, (D.cpRun j h).stat k = .const c → (D.cpRun j h).m < j := by
  intro j
  induction j with
  | zero =>
    intro h
    refine ⟨le_rfl, fun k c hc => ?_⟩
    cases hc
  | succ j ih =>
    intro h
    obtain ⟨h1, h2⟩ := ih (by omega)
    exact CPState.push_count _ _ h1 h2

/-- The number of new gates grows by at most one per old gate. -/
theorem Dag.cpRun_m_mono (D : Dag n s) :
    ∀ (j' : ℕ) (h' : j' ≤ s) (j : ℕ) (h : j ≤ j'),
      (D.cpRun j' h').m ≤ (D.cpRun j (h.trans h')).m + (j' - j) := by
  intro j'
  induction j' with
  | zero =>
    intro h' j h
    obtain rfl : j = 0 := by omega
    exact le_rfl
  | succ j' ih =>
    intro h' j h
    obtain rfl | hlt := Nat.eq_or_lt_of_le h
    · omega
    · have h3 := ih (by omega) j (by omega)
      have h4 := CPState.push_m_le (D.cpRun j' (by omega))
        (simpGate (D.cpRun j' (by omega)).stat (D.gate ⟨j', h'⟩))
      rw [D.cpRun_succ j' h']
      omega

/-- A constant status stays for the rest of the pass. -/
theorem Dag.cpRun_const (D : Dag n s) :
    ∀ (j' : ℕ) (h' : j' ≤ s) (j : ℕ) (h : j ≤ j') (k : ℕ) (hk : k < n + j) (c : Bool),
      (D.cpRun j (h.trans h')).stat ⟨k, hk⟩ = .const c →
      (D.cpRun j' h').stat ⟨k, by omega⟩ = .const c := by
  intro j'
  induction j' with
  | zero =>
    intro h' j h k hk c hc
    obtain rfl : j = 0 := by omega
    exact hc
  | succ j' ih =>
    intro h' j h k hk c hc
    obtain rfl | hlt := Nat.eq_or_lt_of_le h
    · exact hc
    · have h3 := ih (by omega) j (by omega) k hk c hc
      exact CPState.push_const (D.cpRun j' (by omega)) _ ⟨k, by omega⟩ c h3

/-- A gate that reads a wire with a constant status adds no new gate. -/
theorem Dag.cpRun_m_of_reads_const (D : Dag n s) (j : ℕ) (h : j + 1 ≤ s) (k : ℕ)
    (hk : k < n + j) (c : Bool) (hr : (D.gate ⟨j, h⟩).Reads k)
    (hc : (D.cpRun j (by omega)).stat ⟨k, hk⟩ = .const c) :
    (D.cpRun (j + 1) h).m = (D.cpRun j (by omega)).m := by
  obtain ⟨r, hr⟩ := simpGate_of_reads_const (D.cpRun j (by omega)).stat (D.gate ⟨j, h⟩) k hr
    (fun a ha => ⟨c, by rw [← hc]; congr 1; exact Fin.ext ha⟩)
  rw [D.cpRun_succ j h, hr]
  rfl

/-! ### The new circuit -/

/-- Close a state with the status of the output wire. A constant output gives the circuit
with one constant gate; the gates emitted so far are dropped. -/
def CPState.finish {j : ℕ} (S : CPState n j) : Stat (n + S.m) → Σ s', Dag n s'
  | .const c => ⟨1, { gate := fun _ => .const c, out := ⟨n, by omega⟩ }⟩
  | .wire i => ⟨S.m, { gate := S.gate, out := i }⟩

/-- Constant propagation. -/
def Dag.constProp (D : Dag n s) : Σ s', Dag n s' :=
  (D.cpRun s le_rfl).finish ((D.cpRun s le_rfl).stat D.out)

/-- **Soundness.** The new circuit computes the same function. -/
theorem Dag.eval_constProp (D : Dag n s) (x : Fin n → Bool) :
    D.constProp.2.eval x = D.eval x := by
  have hs := D.cpRun_sound x s le_rfl D.out
  unfold Dag.constProp
  unfold Dag.eval
  rw [← hs]
  cases (D.cpRun s le_rfl).stat D.out with
  | const c =>
    simp only [CPState.finish, Stat.val]
    rw [Dag.val_eq_gval, gval_gate _ x n 0 (by omega) rfl]
    rfl
  | wire i =>
    simp only [CPState.finish, Stat.val]
    rw [Dag.val_eq_gval]

/-- The new circuit is one constant gate, or the gates the pass emitted. -/
theorem Dag.size_constProp_cases (D : Dag n s) :
    D.constProp.2.size = 1 ∨ D.constProp.2.size = (D.cpRun s le_rfl).m := by
  unfold Dag.constProp
  cases (D.cpRun s le_rfl).stat D.out with
  | const c => exact Or.inl rfl
  | wire i => exact Or.inr rfl

/-- **Cost.** Constant propagation never adds a gate. -/
theorem Dag.size_constProp_le (D : Dag n s) : D.constProp.2.size ≤ D.size := by
  obtain ⟨h1, h2⟩ := D.cpRun_count s le_rfl
  unfold Dag.constProp
  cases hc : (D.cpRun s le_rfl).stat D.out with
  | const c =>
    have := h2 _ _ hc
    change 1 ≤ s
    omega
  | wire i => exact h1

/-! ### After `restrict` -/

/-- In `D.restrict b` the fixed input keeps status `const b` from the first step on. -/
private theorem restrict_const (D : Dag (n + 1) s) (b : Bool) (j : ℕ) (h1 : 1 ≤ j)
    (h : j ≤ s + 1) : ((D.restrict b).cpRun j h).stat ⟨n, by omega⟩ = .const b := by
  refine (D.restrict b).cpRun_const j h 1 h1 n (by omega) b ?_
  exact Fin.lastCases_last (motive := fun _ : Fin (n + 0 + 1) => Stat (n + 0))

/-- The pass emits at most `D.size` gates on `D.restrict b`: the constant gate is not emitted. -/
theorem Dag.cpRun_restrict_m_le (D : Dag (n + 1) s) (b : Bool) :
    ((D.restrict b).cpRun (s + 1) le_rfl).m ≤ s := by
  have h := (D.restrict b).cpRun_m_mono (s + 1) le_rfl 1 (by omega)
  have h0 : ((D.restrict b).cpRun 1 (by omega)).m = 0 := rfl
  omega

/-- If gate `i` of `D` reads the fixed input, the pass emits at most `D.size - 1` gates. -/
theorem Dag.cpRun_restrict_m_le_of_reads (D : Dag (n + 1) s) (b : Bool) (i : Fin s)
    (hr : (D.gate i).Reads n) :
    ((D.restrict b).cpRun (s + 1) le_rfl).m ≤ s - 1 := by
  have hi := i.isLt
  have hg : ((D.restrict b).gate ⟨i.val + 1, by omega⟩).Reads n :=
    (DGate.reads_cast _ (D.gate i) n).2 hr
  have e := (D.restrict b).cpRun_m_of_reads_const (i.val + 1) (by omega) n (by omega) b hg
    (restrict_const D b (i.val + 1) (by omega) (by omega))
  have h1 := (D.restrict b).cpRun_m_mono (i.val + 1) (by omega) 1 (by omega)
  have h0 : ((D.restrict b).cpRun 1 (by omega)).m = 0 := rfl
  have h2 := (D.restrict b).cpRun_m_mono (s + 1) le_rfl (i.val + 1 + 1) (by omega)
  omega

/-- Fixing an input and propagating never costs a gate, except that the empty circuit
(output an input, no gates) may become one constant gate. -/
theorem Dag.size_constProp_restrict_le_max (D : Dag (n + 1) s) (b : Bool) :
    (D.restrict b).constProp.2.size ≤ max 1 D.size := by
  have h := D.cpRun_restrict_m_le b
  rcases (D.restrict b).size_constProp_cases with h1 | h1 <;> rw [h1] <;>
    simp only [Dag.size] <;> omega

/-- **Gate elimination.** If some gate of `D` reads the last input directly, then fixing that
input and propagating leaves at most `D.size - 1` gates, or exactly one gate (when the output
became a constant). -/
theorem Dag.size_constProp_restrict_le (D : Dag (n + 1) s) (b : Bool)
    (hr : ∃ i : Fin s, (D.gate i).Reads n) :
    (D.restrict b).constProp.2.size ≤ max 1 (D.size - 1) := by
  obtain ⟨i, hr⟩ := hr
  have h := D.cpRun_restrict_m_le_of_reads b i hr
  rcases (D.restrict b).size_constProp_cases with h1 | h1 <;> rw [h1] <;>
    simp only [Dag.size] <;> omega

/-- The same, in the form a size induction uses: no more gates than `D`. -/
theorem Dag.size_constProp_restrict_le_size (D : Dag (n + 1) s) (b : Bool)
    (hr : ∃ i : Fin s, (D.gate i).Reads n) :
    (D.restrict b).constProp.2.size ≤ D.size := by
  have h := D.size_constProp_restrict_le b hr
  have hs : 1 ≤ s := by obtain ⟨i, _⟩ := hr; have := i.isLt; omega
  simp only [Dag.size] at h ⊢
  omega

/-- Soundness after `restrict`: the function of `D` with the last input fixed to `b`. -/
theorem Dag.eval_constProp_restrict (D : Dag (n + 1) s) (b : Bool) (x : Fin n → Bool) :
    (D.restrict b).constProp.2.eval x = D.eval (snocIn x b) := by
  rw [Dag.eval_constProp, Dag.eval_restrict]

end PEqualNP.Kernel
