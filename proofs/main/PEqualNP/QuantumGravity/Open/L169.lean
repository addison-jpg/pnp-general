import PEqualNP.QuantumGravity.Helpers.CtcClass
import PEqualNP.Library.Universal.BruteForce
import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.Library.L055

/-!
# L-qg-169: P_CTC is inside EXP

The decision rule of row L-qg-168 (apply the register map `2 ^ m` times from any register) is made
into a machine, as in `Library/Universal/BruteForce.lean`.

* The padded query for `x` is `expPad F` with `F = pairB x (un m)`, `m = p (length of x)`, so the
  padded string carries `2 ^ |F|` ones with `|F| ≥ m`.
* The state of the iteration is `pairB x r` on plain bit strings. One step, `gStep`, splits the
  state, runs the polynomial-time circuit, pads the answer with `blank r` and cuts it to `|r|`
  bits by `unpairB (un |r| ++ false :: _)`, then packs the pair again.
* `cpt_iterGrow` iterates `gStep` as many times as the padded string has leading ones.
* Iterating `N ≥ 2 ^ m` times lands on a cycle, and the uniform distribution on that cycle is
  Deutsch-consistent, so the read-out there decides `x`.
* `expPad` and `comp_time` give the time bound `2 ^ (n ^ k) + k`.
-/

namespace PEqualNP.QuantumGravity.Open.L169

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
  PEqualNP.Library.Machines.ExpPad PEqualNP.QuantumGravity

local notation "CPTb" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-! ### Small pieces -/

/-- One `true` for each symbol. -/
def unL (l : List Bool) : List Bool := l.map fun _ => true

theorem unL_eq (l : List Bool) : unL l = un l.length := by
  simp [unL, un, List.map_const']

theorem unL_run (l : List Bool) :
    fstRun (fun (_ : Unit) (_ : Bool) => ((), some true)) (fun _ => none) () l = unL l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, unL] at ih ⊢; exact ih

theorem cpt_unL : CPTb unL :=
  fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some true)) (fun _ => none) ()
    (fun s => (unL_run s).symm)

theorem blank_eq (l : List Bool) : blank l = List.replicate l.length false := by
  simp [blank, List.map_const']

theorem unpairB_un (n : ℕ) (t : List Bool) :
    unpairB (un n ++ false :: t) = (t.take n, t.drop n) := by
  have h1 : (un n ++ false :: t).takeWhile id = un n := by simp [un]
  have h2 : (un n ++ false :: t).dropWhile id = false :: t := by simp [un]
  simp [unpairB, h1, h2, un]

/-! ### The step on packed states -/

/-- One step of the register map on the packed state `pairB x r`. -/
def gStep (next : List Bool × List Bool → List Bool) (y : List Bool) : List Bool :=
  pairB (unpairB y).1
    (unpairB (unL (unpairB y).2 ++ false :: (next (unpairB y) ++ blank (unpairB y).2))).1

theorem cpt_gStep {next : List Bool × List Bool → List Bool}
    (hn : ComputableInPolyTime encodePair (fun y : List Bool => y) next) : CPTb (gStep next) := by
  have hS : CPTb (fun y => next (unpairB y)) := cpt_comp cpt_unpairB hn
  have hB : CPTb (fun y => blank (unpairB y).2) := cpt_comp cpt_unpairB2 cpt_blank
  have hU : CPTb (fun y => unL (unpairB y).2) := cpt_comp cpt_unpairB2 cpt_unL
  have hZ : CPTb (fun y => unL (unpairB y).2 ++ false :: (next (unpairB y) ++ blank (unpairB y).2)) :=
    cpt_app2 hU (cpt_cons1 false (cpt_app2 hS hB))
  exact cpt_pairB2 cpt_unpairB1 (cpt_unpairB1_1 hZ)

theorem gStep_length (next : List Bool × List Bool → List Bool) (y : List Bool) :
    (gStep next y).length ≤ y.length + 1 := by
  have h1 := unpairB_length y
  have h2 : (unpairB (unL (unpairB y).2 ++ false :: (next (unpairB y) ++ blank (unpairB y).2))).1.length
      ≤ (unpairB y).2.length := by
    rw [unL_eq, unpairB_un, List.length_take]
    simp
  unfold gStep
  rw [pairB_length]
  omega

theorem gStep_pack (next : List Bool × List Bool → List Bool) (x : List Bool) (m : ℕ)
    (r : List.Vector Bool m) :
    gStep next (pairB x r.toList) = pairB x (ctcRegisterMap next x m r).toList := by
  unfold gStep
  rw [unpairB_pairB, unL_eq, blank_eq, unpairB_un]
  simp only [ctcRegisterMap, List.Vector.toList_length, List.Vector.toList_mk]

theorem gStep_iter (next : List Bool × List Bool → List Bool) (x : List Bool) (m : ℕ)
    (r : List.Vector Bool m) (j : ℕ) :
    (gStep next)^[j] (pairB x r.toList) = pairB x ((ctcRegisterMap next x m)^[j] r).toList := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, gStep_pack]

/-! ### The decider on the padded string -/

/-- The initial packed state `pairB x (false^m)`, read off the padded string. -/
def initSt (s : List Bool) : List Bool :=
  pairB (unpairB (dropN s)).1 (blank (unpairB (dropN s)).2)

/-- The packed state after iterating as often as the padded string has leading ones. -/
def finalSt (next : List Bool × List Bool → List Bool) (s : List Bool) : List Bool :=
  (gStep next)^[(hd s).length] (initSt s)

/-- The decider: read the answer off the register reached. -/
def decG (ans : List Bool × List Bool → Bool) (next : List Bool × List Bool → List Bool)
    (s : List Bool) : Bool :=
  ans (unpairB (finalSt next s))

theorem cpt_decG {ans : List Bool × List Bool → Bool}
    {next : List Bool × List Bool → List Bool}
    (ha : ComputableInPolyTime encodePair Computability.encodeBool ans)
    (hn : ComputableInPolyTime encodePair (fun y : List Bool => y) next) :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool (decG ans next) := by
  have h1 : CPTb (fun s => (unpairB (dropN s)).1) :=
    cpt_comp (f := dropN) (g := fun s => (unpairB s).1) cpt_dropN cpt_unpairB1
  have h2 : CPTb (fun s => (unpairB (dropN s)).2) :=
    cpt_comp (f := dropN) (g := fun s => (unpairB s).2) cpt_dropN cpt_unpairB2
  have hI : CPTb initSt := cpt_pairB2 h1 (cpt_comp h2 cpt_blank)
  have hF : CPTb (finalSt next) :=
    cpt_iterGrow (cnt := hd) (arg := initSt) (cpt_gStep hn) 1 (gStep_length next) cpt_hd hI
  have h3 : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s => ans (unpairB s)) := cpt_comp (f := unpairB) (g := ans) cpt_unpairB ha
  exact cpt_comp (f := finalSt next) (g := fun s => ans (unpairB s)) hF h3

/-- On the padded query for `x` the decider answers by `N ≥ 2 ^ m` steps of the register map. -/
theorem decG_expPad (ans : List Bool × List Bool → Bool)
    (next : List Bool × List Bool → List Bool) (x : List Bool) (m : ℕ) :
    decG ans next (expPad (pairB x (un m))) =
      ans (x, ((ctcRegisterMap next x m)^[2 ^ (pairB x (un m)).length]
        (List.Vector.replicate m false)).toList) := by
  have e1 : initSt (expPad (pairB x (un m))) =
      pairB x (List.Vector.replicate m false).toList := by
    simp [initSt, dropN_expPad, unpairB_pairB, blank_eq, un, List.Vector.replicate,
      List.Vector.toList]
  unfold decG finalSt
  rw [hd_expPad, un_length, e1, gStep_iter, unpairB_pairB]

/-! ### Landing on a cycle -/

theorem exists_consistent_of_ge {S : Type} [Fintype S] (f : S → S) (x : S) (N : ℕ)
    (hN : Fintype.card S ≤ N) :
    ∃ μ : PMF S, DeutschConsistent f μ ∧ f^[N] x ∈ μ.support := by
  obtain ⟨q, hq⟩ := PEqualNP.QuantumGravity.Helpers.periodic_iterate_card f x
  refine PEqualNP.QuantumGravity.Helpers.consistent_of_periodic_mem f _ q ?_
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  have comm : ∀ a b y, f^[a] (f^[b] y) = f^[b] (f^[a] y) := fun a b y => by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]
  have e1 : f^[Fintype.card S + d] x = f^[d] (f^[Fintype.card S] x) := by
    rw [Nat.add_comm, Function.iterate_add_apply]
  rw [e1, comm (q + 1) d, hq]

/-! ### From a padded decider to EXP -/

theorem exp_of_padded (L : Language Bool) (F : List Bool → List Bool) (hF : CPTb F)
    (G : List Bool → Bool)
    (hG : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool G)
    (hcorr : ∀ x, x ∈ L ↔ G (expPad (F x)) = true) : L ∈ EXP := by
  obtain ⟨p₁, hp₁⟩ := time_of_polyTime hF
  obtain ⟨r, hr⟩ := output_length_poly F hF
  obtain ⟨p₂, hp₂⟩ := time_of_polyTime hG
  have hmono : Monotone (fun n : ℕ => 8 * 2 ^ n + 8 * n + 8) := by
    intro a b hab
    have : (2 : ℕ) ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
    show 8 * 2 ^ a + 8 * a + 8 ≤ 8 * 2 ^ b + 8 * b + 8
    omega
  have h1 := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => x) F expPad (fun n => p₁.eval n)
    (fun n : ℕ => 8 * 2 ^ n + 8 * n + 8) (fun n => r.eval n) hp₁ expPad_time hmono hr
  have h2 := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
    Computability.encodeBool (fun x => expPad (F x)) G _ (fun n => p₂.eval n)
    (fun n => 2 ^ r.eval n + r.eval n + 1) h1 hp₂ (fun _ _ hxy => eval_mono p₂ hxy)
    (fun x => by
      have e := expPad_length (F x)
      have h3 := hr x
      have : (2 : ℕ) ^ (F x).length ≤ 2 ^ r.eval x.length :=
        Nat.pow_le_pow_right (by norm_num) h3
      show (expPad (F x)).length ≤ 2 ^ r.eval x.length + r.eval x.length + 1
      omega)
  obtain ⟨k, hk⟩ := bf_time_bound p₁ r p₂
  exact ⟨k, fun x => G (expPad (F x)), hcorr, time_mono h2 hk⟩

/-- L-qg-169: P_CTC is inside EXP. -/
theorem PCTC_subset_EXP : PCTC ⊆ EXP := by
  intro L hL
  obtain ⟨p, ans, next, ha, hn, h⟩ := hL
  let F : List Bool → List Bool := fun x => pairB x (un (p.eval x.length))
  have hF : CPTb F := cpt_pairB2 cpt_id (L055 p)
  refine exp_of_padded L F hF (decG ans next) (cpt_decG ha hn) (fun x => ?_)
  rw [show F x = pairB x (un (p.eval x.length)) from rfl, decG_expPad]
  set f := ctcRegisterMap next x (p.eval x.length) with hf
  have hN : Fintype.card (List.Vector Bool (p.eval x.length)) ≤
      2 ^ (pairB x (un (p.eval x.length))).length := by
    rw [card_vector, Fintype.card_bool]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    rw [pairB_length]
    simp
    omega
  obtain ⟨μ, hμ, hmem⟩ := exists_consistent_of_ge f (List.Vector.replicate _ false) _ hN
  exact (h x μ hμ _ hmem).symm

end PEqualNP.QuantumGravity.Open.L169
